//===--- Verifier.cpp - CppVerify driver ----------------------------------===//
#include "Verifier.h"
#include "../Backend/Obligation.h"
#include "../Backend/Z3Encode.h"
#include "../Frontend/ASTConverter.h"
#include "../IR/VStmt.h"
#include "../Transform/LoopUnroll.h"
#include "../Transform/Ownership.h"
#include "../Transform/Passivize.h"
#include "../Transform/SpecInline.h"
#include "../Transform/UBChecks.h"
#include "DumpIR.h"
#include "clang/AST/ASTContext.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <optional>

using namespace clang;
using namespace verify;

namespace {

struct VerifyDiagnostic {
  enum Kind { Verified, Lowered, Exported, Error, Warning, Unknown };
  Kind K;
  std::string Message;
};

class Verifier {
  ASTContext &Ctx;
  VerifyOptions Opts;
  llvm::raw_ostream *DumpOS = nullptr;
  std::vector<VerifyDiagnostic> Diags;

  void checkCalleeRecommendsOnFailure(const VFunction &Caller,
                                      const FunctionMap &FnMap,
                                      VerifyBackend &Backend) {
    std::vector<const VSpecCallExpr *> Calls;
    collectSpecCallsInFunction(Caller, Calls);
    for (const VSpecCallExpr *C : Calls) {
      auto It = FnMap.find(C->CalleeIdentity);
      if (It == FnMap.end() || It->second->Recommends.empty())
        continue;
      std::map<std::string, std::unique_ptr<VExpr>> ArgMap;
      for (unsigned I = 0; I < It->second->Params.size() && I < C->Args.size();
           ++I)
        ArgMap[It->second->Params[I].first] = cloneVExpr(C->Args[I].get());
      PassiveProgram PP;
      PP.FunctionName = Caller.Name + ".recommends";
      PP.FunctionIdentity =
          Caller.Identity + "::recommends::" + C->CalleeIdentity;
      for (const auto &Pre : Caller.Preconditions)
        PP.EntryAssumes.push_back(cloneVExpr(Pre.get()));
      for (const auto &Rec : It->second->Recommends) {
        auto Inst = substParamsInExpr(Rec.get(), ArgMap);
        if (!Inst)
          continue;
        Inst = SpecInliner(FnMap, Caller.SpecFuel).inlineExpr(std::move(Inst));
        PP.ExitAsserts.push_back(std::move(Inst));
      }
      if (PP.ExitAsserts.empty())
        continue;
      PP.CallerIntMode = Caller.IntMode;
      auto Module = buildObligationModule(PP);
      if (!Module) {
        Diags.push_back({VerifyDiagnostic::Unknown,
                         "recommends lowering failed for " + Caller.Name +
                             " (" + llvm::toString(Module.takeError()) + ")"});
        continue;
      }
      VerifyResult R = Backend.verify(*Module);
      if (R.Status == VerifyStatus::Failed)
        Diags.push_back({VerifyDiagnostic::Warning,
                         "recommends of spec " + C->Callee +
                             " may be violated at call in " + Caller.Name});
    }
  }

public:
  Verifier(ASTContext &Ctx, const VerifyOptions &Opts,
           llvm::raw_ostream &DumpOS)
      : Ctx(Ctx), Opts(Opts), DumpOS(&DumpOS) {}

  bool run() {
    if (Opts.LowerOnly && Opts.Backend == BackendKind::Lean) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--lower-only supports the Z3 and BMC lowering pipelines; use "
           "--backend=lean to validate Lean export"});
      return false;
    }

    ASTConverter DiscoveryConverter(Ctx);
    auto DiscoveryFunctions = DiscoveryConverter.convertTranslationUnit();
    inferFreshOwnedReturns(DiscoveryFunctions);
    std::set<std::string> FreshOwnedCalleeIdentities;
    for (const auto &Fn : DiscoveryFunctions)
      if (Fn->FreshOwnedReturn)
        FreshOwnedCalleeIdentities.insert(Fn->Identity);

    ASTConverter Converter(Ctx, FreshOwnedCalleeIdentities);
    auto Functions = Converter.convertTranslationUnit();
    for (const std::string &Err : Converter.getErrors())
      Diags.push_back({VerifyDiagnostic::Error, Err});
    if (!Converter.getErrors().empty())
      return false;
    if (Functions.empty()) {
      Diags.push_back(
          {VerifyDiagnostic::Warning, "no verifiable functions found"});
      return true;
    }
    inferFreshOwnedReturns(Functions);

    FunctionMap FnMap;
    for (const auto &Fn : Functions)
      FnMap[Fn->Identity] = Fn.get();

    std::vector<std::unique_ptr<VFunction>> InterfaceFunctions;
    FunctionMap InterfaceMap;
    InterfaceFunctions.reserve(Functions.size());
    for (const auto &Fn : Functions) {
      auto Interface = std::make_unique<VFunction>(cloneVFunction(*Fn));
      if (!Interface->IsSpec && Opts.CheckUB &&
          (Opts.Backend == BackendKind::Z3 || Opts.Backend == BackendKind::BMC))
        (void)instrumentUBChecks(*Interface);
      InterfaceMap[Interface->Identity] = Interface.get();
      InterfaceFunctions.push_back(std::move(Interface));
    }

    std::unique_ptr<llvm::raw_fd_ostream> LeanFile;
    llvm::raw_ostream *LeanOut = DumpOS;
    if (Opts.Backend == BackendKind::Lean && !Opts.LeanOutPath.empty()) {
      std::error_code EC;
      LeanFile = std::make_unique<llvm::raw_fd_ostream>(Opts.LeanOutPath, EC,
                                                        llvm::sys::fs::OF_Text);
      if (EC) {
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot open lean output: " + Opts.LeanOutPath});
        return false;
      }
      LeanOut = LeanFile.get();
    }

    auto Backend = createVerifyBackend(Opts.Backend, LeanOut, Opts.BMCUnroll,
                                       Opts.SolverTimeoutMs);
    Passivizer P;
    P.setFunctionMap(InterfaceMap);
    Z3Encoder Z3Lowering;

    const unsigned DumpLayers = Opts.DumpIRLayers;
    const bool MultiLayerDump = llvm::popcount(DumpLayers) > 1;
    bool AllOk = true;
    bool AnyFailed = false;
    std::set<std::string> FailedCallers;

    for (const auto &Fn : Functions) {
      if (Fn->IsExternalContract) {
        Diags.push_back({VerifyDiagnostic::Warning,
                         "assuming external contract: " + Fn->Name});
        continue;
      }
      bool DumpedAny = false;
      auto dumpSep = [&]() {
        if (DumpedAny && MultiLayerDump)
          *DumpOS << "======\n";
        DumpedAny = true;
      };

      std::optional<VFunction> PreparedFn;
      std::optional<VFunction> UnrolledFn;
      std::optional<std::string> UBError;
      const VFunction &WorkFn = [&]() -> const VFunction & {
        if (Fn->IsSpec) {
          if (Fn->NeedsDecreasesCheck)
            return *Fn;
          return *Fn;
        }
        PreparedFn = cloneVFunction(*Fn);
        // `valid(p, n)` is a recognized UB marker. Discover it before spec
        // preparation folds its deliberately trivial body to `true`.
        if (Opts.CheckUB && (Opts.Backend == BackendKind::Z3 ||
                             Opts.Backend == BackendKind::BMC))
          UBError = instrumentUBChecks(*PreparedFn);
        if (UBError)
          return *PreparedFn;
        SpecInliner Inliner(FnMap, PreparedFn->SpecFuel);
        if (Opts.Backend == BackendKind::Z3)
          Inliner.prepareFunctionAxiomatic(*PreparedFn);
        else
          Inliner.prepareFunction(*PreparedFn);
        if (Opts.Backend == BackendKind::BMC) {
          UnrolledFn = LoopUnroller::unroll(*PreparedFn, Opts.BMCUnroll);
          return *UnrolledFn;
        }
        return *PreparedFn;
      }();

      if (UBError) {
        AllOk = false;
        AnyFailed = true;
        if (!Fn->IsProof)
          FailedCallers.insert(Fn->Identity);
        Diags.push_back({VerifyDiagnostic::Error, Fn->Name + ": " + *UBError});
        continue;
      }

      if (Fn->IsSpec && !Fn->NeedsDecreasesCheck) {
        const VerifyDiagnostic::Kind Kind =
            Opts.LowerOnly ? VerifyDiagnostic::Lowered
                           : (Opts.Backend == BackendKind::Lean
                                  ? VerifyDiagnostic::Exported
                                  : VerifyDiagnostic::Verified);
        if (Fn->IsConstexprSpec)
          Diags.push_back({Kind, "constexpr spec axiom: " + Fn->Name});
        else
          Diags.push_back({Kind, "spec axiom: " + Fn->Name});
        continue;
      }

      if (Fn->NeedsDecreasesCheck) {
        PassiveProgram DecPP = buildDecreasesChecks(*Fn, FnMap);
        auto DecModuleOrErr = buildObligationModule(DecPP);
        if (!DecModuleOrErr) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back(
              {VerifyDiagnostic::Unknown,
               "obligation lowering failed for decreases: " + Fn->Name + " (" +
                   llvm::toString(DecModuleOrErr.takeError()) + ")"});
          continue;
        }
        ObligationModule DecModule = std::move(*DecModuleOrErr);
        if (Opts.LowerOnly) {
          VerifyResult DR = Z3Lowering.lowerModule(DecModule);
          if (DR.Status != VerifyStatus::Verified) {
            AllOk = false;
            AnyFailed = true;
            std::string Message =
                "Z3 lowering failed for decreases: " + Fn->Name;
            if (!DR.Message.empty())
              Message += " (" + DR.Message + ")";
            Diags.push_back({VerifyDiagnostic::Error, std::move(Message)});
            continue;
          }
          if (Fn->IsSpec) {
            Diags.push_back(
                {VerifyDiagnostic::Lowered, "spec decreases: " + Fn->Name});
            continue;
          }
        } else {
          VerifyResult R = Backend->verify(DecModule);
          if (R.Status == VerifyStatus::Exported) {
            Diags.push_back(
                {VerifyDiagnostic::Exported, "decreases: " + Fn->Name});
            if (Fn->IsSpec)
              continue;
          } else if (R.Status == VerifyStatus::Verified) {
            if (Fn->IsSpec) {
              Diags.push_back(
                  {VerifyDiagnostic::Verified, "spec decreases: " + Fn->Name});
              continue;
            }
          } else {
            AllOk = false;
            AnyFailed = true;
            if (!Fn->IsProof)
              FailedCallers.insert(Fn->Identity);
            const bool IsUnknown = R.Status == VerifyStatus::Unknown;
            std::string Message =
                std::string(Fn->IsSpec ? "spec decreases " : "decreases ") +
                (IsUnknown ? "unknown: " : "failed: ") + Fn->Name;
            if (!R.Message.empty())
              Message += " (" + R.Message + ")";
            Diags.push_back({IsUnknown ? VerifyDiagnostic::Unknown
                                       : VerifyDiagnostic::Error,
                             std::move(Message)});
            continue;
          }
        }
      }

      if (DumpLayers & LayerVCR) {
        dumpSep();
        dumpVFunction(WorkFn, *DumpOS);
      }

      PassiveProgram PP = P.run(WorkFn);
      if (DumpLayers & LayerPassive) {
        dumpSep();
        dumpPassiveProgram(Fn->Name, PP, *DumpOS);
      }

      auto ModuleOrErr = buildObligationModule(PP);
      if (!ModuleOrErr) {
        AllOk = false;
        AnyFailed = true;
        Diags.push_back({VerifyDiagnostic::Unknown,
                         "obligation lowering failed: " + Fn->Name + " (" +
                             llvm::toString(ModuleOrErr.takeError()) + ")"});
        continue;
      }
      ObligationModule Module = std::move(*ModuleOrErr);

      if (DumpLayers & LayerVC) {
        dumpSep();
        dumpVC(Module, *DumpOS);
      }

      if (DumpLayers & LayerZ3 || Opts.LowerOnly) {
        if (DumpLayers & LayerZ3)
          dumpSep();
        llvm::raw_ostream *Z3Out = DumpLayers & LayerZ3 ? DumpOS : nullptr;
        VerifyResult Lowered = Z3Lowering.lowerModule(Module, Z3Out);
        if (Lowered.Status != VerifyStatus::Verified) {
          AllOk = false;
          AnyFailed = true;
          std::string Message = "Z3 lowering failed: " + Fn->Name;
          if (!Lowered.Message.empty())
            Message += " (" + Lowered.Message + ")";
          Diags.push_back({VerifyDiagnostic::Error, std::move(Message)});
          continue;
        }
      }
      if (DumpLayers)
        DumpOS->flush();

      if (Opts.LowerOnly) {
        Diags.push_back({VerifyDiagnostic::Lowered, Fn->Name});
        continue;
      }

      VerifyResult R = Backend->verify(Module);
      if (R.Status == VerifyStatus::Verified) {
        Diags.push_back({VerifyDiagnostic::Verified, Fn->Name});
      } else if (R.Status == VerifyStatus::Exported) {
        Diags.push_back(
            {VerifyDiagnostic::Exported, "lean obligation: " + Fn->Name});
      } else if (R.Status == VerifyStatus::Failed) {
        AllOk = false;
        AnyFailed = true;
        if (!Fn->IsProof)
          FailedCallers.insert(Fn->Identity);
        std::string Msg = "verification failed: " + Fn->Name;
        if (!R.ObligationId.empty())
          Msg += " [" + R.ObligationId + "]";
        if (!R.Message.empty())
          Msg += " (counterexample: " + R.Message + ")";
        Diags.push_back({VerifyDiagnostic::Error, Msg});
      } else {
        AllOk = false;
        AnyFailed = true;
        if (!Fn->IsProof)
          FailedCallers.insert(Fn->Identity);
        std::string Message = Fn->Name;
        if (!R.Message.empty())
          Message += " (" + R.Message + ")";
        Diags.push_back({VerifyDiagnostic::Unknown, std::move(Message)});
      }
    }

    if (AnyFailed && !Opts.LowerOnly && Opts.Backend == BackendKind::Z3) {
      auto Z3 = createVerifyBackend(BackendKind::Z3, nullptr, 0,
                                    Opts.SolverTimeoutMs);
      for (const auto &Fn : Functions) {
        if (!FailedCallers.count(Fn->Identity) || Fn->IsSpec || Fn->IsProof ||
            Fn->IsExternalContract)
          continue;
        checkCalleeRecommendsOnFailure(*Fn, FnMap, *Z3);
      }
    }

    return AllOk;
  }

  void printDiagnostics(llvm::raw_ostream &OS) const {
    for (const auto &D : Diags) {
      switch (D.K) {
      case VerifyDiagnostic::Verified:
        OS << "Verified: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Lowered:
        OS << "Lowered: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Exported:
        OS << "Exported: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Error:
        OS << "error: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Warning:
        OS << "warning: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Unknown:
        OS << "unknown: " << D.Message << "\n";
        break;
      }
    }
  }
};

} // namespace

bool verify::verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                                   const VerifyOptions &Opts) {
  Verifier V(Ctx, Opts, OS);
  bool Ok = V.run();
  V.printDiagnostics(OS);
  return Ok;
}