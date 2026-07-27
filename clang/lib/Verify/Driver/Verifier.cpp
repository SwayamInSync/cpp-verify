//===--- Verifier.cpp - CppVerify driver ----------------------------------===//
#include "Verifier.h"
#include "../Backend/LeanBackend.h"
#include "../Backend/VCMachine.h"
#include "../Backend/WPCalc.h"
#include "../Backend/Z3Encode.h"
#include "../Frontend/ASTConverter.h"
#include "../IR/VStmt.h"
#include "../Transform/LoopUnroll.h"
#include "../Transform/Passivize.h"
#include "../Transform/SpecInline.h"
#include "../Transform/UBChecks.h"
#include "DumpIR.h"
#include "clang/AST/ASTContext.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <optional>

using namespace clang;
using namespace verify;

namespace {

struct VerifyDiagnostic {
  enum Kind { Verified, Lowered, Error, Warning, Unknown };
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
      VerifyResult R = Backend.verifyPassive(PP);
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

    ASTConverter Converter(Ctx);
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

    FunctionMap FnMap;
    for (const auto &Fn : Functions)
      FnMap[Fn->Identity] = Fn.get();

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
    P.setFunctionMap(FnMap);
    WPCalculator WP;
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
        if (Opts.CheckUB && Opts.Backend == BackendKind::Z3)
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
        const VerifyDiagnostic::Kind Kind = Opts.LowerOnly
                                                ? VerifyDiagnostic::Lowered
                                                : VerifyDiagnostic::Verified;
        if (Fn->IsConstexprSpec)
          Diags.push_back({Kind, "constexpr spec axiom: " + Fn->Name});
        else
          Diags.push_back({Kind, "spec axiom: " + Fn->Name});
        continue;
      }

      if (Fn->NeedsDecreasesCheck) {
        PassiveProgram DecPP = buildDecreasesChecks(*Fn, FnMap);
        if (Opts.LowerOnly) {
          VCMachine DecMachine = VCMachine::fromPassive(DecPP);
          VerifyResult DR = Z3Lowering.lowerMachine(DecMachine);
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
        } else if (!Fn->IsSpec) {
          VerifyResult DR = Backend->verifyPassive(DecPP);
          if (DR.Status != VerifyStatus::Verified) {
            AllOk = false;
            AnyFailed = true;
            if (!Fn->IsProof)
              FailedCallers.insert(Fn->Identity);
            Diags.push_back({DR.Status == VerifyStatus::Unknown
                                 ? VerifyDiagnostic::Unknown
                                 : VerifyDiagnostic::Error,
                             "decreases " +
                                 std::string(DR.Status == VerifyStatus::Unknown
                                                 ? "unknown: "
                                                 : "failed: ") +
                                 Fn->Name});
            continue;
          }
        } else {
          VerifyResult R = Backend->verifyPassive(DecPP);
          if (R.Status == VerifyStatus::Verified)
            Diags.push_back(
                {VerifyDiagnostic::Verified, "spec decreases: " + Fn->Name});
          else if (R.Status == VerifyStatus::Failed) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Error,
                             "spec decreases failed: " + Fn->Name});
          } else {
            AllOk = false;
            AnyFailed = true;
            std::string Message = "spec decreases unknown: " + Fn->Name;
            if (!R.Message.empty())
              Message += " (" + R.Message + ")";
            Diags.push_back({VerifyDiagnostic::Error, std::move(Message)});
          }
          continue;
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

      auto VC = WP.computeVC(PP);
      if (DumpLayers & LayerVC && VC) {
        dumpSep();
        dumpVC(Fn->Name, VC.get(), *DumpOS);
      }

      if (DumpLayers & LayerZ3 || Opts.LowerOnly) {
        if (DumpLayers & LayerZ3)
          dumpSep();
        VCMachine M = VCMachine::fromPassive(PP);
        llvm::raw_ostream *Z3Out = DumpLayers & LayerZ3 ? DumpOS : nullptr;
        VerifyResult Lowered = Z3Lowering.lowerMachine(M, Z3Out);
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

      if (Opts.Backend == BackendKind::Lean) {
        VerifyResult R;
        if (LeanOut != DumpOS) {
          *LeanOut << "\n/- function: " << Fn->Name << " -/\n";
          R = exportLeanScratchPad(PP, *LeanOut, Opts.SolverTimeoutMs);
        } else {
          R = exportLeanScratchPad(PP, *DumpOS, Opts.SolverTimeoutMs);
        }
        if (R.Status == VerifyStatus::Verified) {
          Diags.push_back(
              {VerifyDiagnostic::Verified, "lean export: " + Fn->Name});
        } else if (R.Status == VerifyStatus::Failed) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back(
              {VerifyDiagnostic::Error,
               "verification failed: " + Fn->Name + " (lean export written)"});
        } else {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back(
              {VerifyDiagnostic::Unknown, "lean export check: " + Fn->Name});
        }
        continue;
      }

      VerifyResult R = Backend->verifyPassive(PP);
      if (R.Status == VerifyStatus::Verified) {
        Diags.push_back({VerifyDiagnostic::Verified, Fn->Name});
      } else if (R.Status == VerifyStatus::Failed) {
        AllOk = false;
        AnyFailed = true;
        if (!Fn->IsProof)
          FailedCallers.insert(Fn->Identity);
        std::string Msg = "verification failed: " + Fn->Name;
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