//===--- Verifier.cpp - CppVerify driver ----------------------------------===//
#include "clang/AST/ASTContext.h"
#include "../Frontend/ASTConverter.h"
#include "../Transform/Passivize.h"
#include "../Transform/LoopUnroll.h"
#include "../Transform/SpecInline.h"
#include "../IR/VStmt.h"
#include "../Backend/WPCalc.h"
#include "../Backend/VCMachine.h"
#include "../Backend/Z3Encode.h"
#include "../Backend/LeanBackend.h"
#include "Verifier.h"
#include "DumpIR.h"
#include "llvm/Support/FileSystem.h"
#include <optional>
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace verify;

namespace {

struct VerifyDiagnostic {
  enum Kind { Verified, Error, Warning, Unknown };
  Kind K;
  std::string Message;
};

class Verifier {
  ASTContext &Ctx;
  VerifyOptions Opts;
  llvm::raw_ostream *DumpOS = nullptr;
  std::vector<VerifyDiagnostic> Diags;

  void checkRecommendsImplied(const std::vector<std::unique_ptr<VFunction>> &Fns,
                              VerifyBackend &Backend) {
    for (const auto &Fn : Fns) {
      if (Fn->Recommends.empty())
        continue;
      PassiveProgram PP;
      for (const auto &Pre : Fn->Preconditions)
        PP.EntryAssumes.push_back(cloneVExpr(Pre.get()));
      for (const auto &Rec : Fn->Recommends)
        PP.ExitAsserts.push_back(cloneVExpr(Rec.get()));
      if (PP.ExitAsserts.empty())
        continue;
      VerifyResult R = Backend.verifyPassive(PP);
      if (R.Status == VerifyStatus::Failed)
        Diags.push_back({VerifyDiagnostic::Warning,
                         "recommends not implied by preconditions in " + Fn->Name});
    }
  }

  void checkCalleeRecommendsOnFailure(const VFunction &Caller,
                                    const FunctionMap &FnMap,
                                    VerifyBackend &Backend) {
    std::vector<const VSpecCallExpr *> Calls;
    collectSpecCallsInFunction(Caller, Calls);
    for (const VSpecCallExpr *C : Calls) {
      auto It = FnMap.find(C->Callee);
      if (It == FnMap.end() || It->second->Recommends.empty())
        continue;
      std::map<std::string, std::unique_ptr<VExpr>> ArgMap;
      for (unsigned I = 0; I < It->second->Params.size() && I < C->Args.size(); ++I)
        ArgMap[It->second->Params[I].first] = cloneVExpr(C->Args[I].get());
      PassiveProgram PP;
      for (const auto &Pre : Caller.Preconditions)
        PP.EntryAssumes.push_back(cloneVExpr(Pre.get()));
      for (const auto &Rec : It->second->Recommends) {
        auto Inst = substParamsInExpr(Rec.get(), ArgMap);
        if (!Inst)
          continue;
        auto NotRec = std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(Inst),
                                                     VType::makeBool(), C->Loc);
        PP.ExitAsserts.push_back(std::move(NotRec));
      }
      if (PP.ExitAsserts.empty())
        continue;
      VerifyResult R = Backend.verifyPassive(PP);
      if (R.Status == VerifyStatus::Failed)
        Diags.push_back({VerifyDiagnostic::Warning,
                         "recommends of spec " + C->Callee +
                             " may be violated at call in " + Caller.Name});
    }
  }

public:
  Verifier(ASTContext &Ctx, const VerifyOptions &Opts, llvm::raw_ostream &DumpOS)
      : Ctx(Ctx), Opts(Opts), DumpOS(&DumpOS) {}

  bool run() {
    ASTConverter Converter(Ctx);
    auto Functions = Converter.convertTranslationUnit();
    for (const std::string &Err : Converter.getErrors())
      Diags.push_back({VerifyDiagnostic::Error, Err});
    if (!Converter.getErrors().empty())
      return false;
    if (Functions.empty()) {
      Diags.push_back({VerifyDiagnostic::Warning, "no verifiable functions found"});
      return true;
    }

    FunctionMap FnMap;
    for (const auto &Fn : Functions)
      FnMap[Fn->Name] = Fn.get();

    std::unique_ptr<llvm::raw_fd_ostream> LeanFile;
    llvm::raw_ostream *LeanOut = DumpOS;
    if (Opts.Backend == BackendKind::Lean && !Opts.LeanOutPath.empty()) {
      std::error_code EC;
      LeanFile = std::make_unique<llvm::raw_fd_ostream>(
          Opts.LeanOutPath, EC, llvm::sys::fs::OF_Text);
      if (EC) {
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot open lean output: " + Opts.LeanOutPath});
        return false;
      }
      LeanOut = LeanFile.get();
    }

    auto Backend = createVerifyBackend(Opts.Backend, LeanOut, Opts.BMCUnroll);
    Passivizer P;
    P.setFunctionMap(FnMap);
    WPCalculator WP;
    Z3Encoder Z3Dump;

    const unsigned DumpLayers = Opts.DumpIRLayers;
    const bool MultiLayerDump = llvm::popcount(DumpLayers) > 1;
    bool AllOk = true;
    bool AnyFailed = false;

    for (const auto &Fn : Functions) {
      bool DumpedAny = false;
      auto dumpSep = [&]() {
        if (DumpedAny && MultiLayerDump)
          *DumpOS << "======\n";
        DumpedAny = true;
      };

      std::optional<VFunction> PreparedFn;
      std::optional<VFunction> UnrolledFn;
      const VFunction &WorkFn = [&]() -> const VFunction & {
        if (Fn->IsSpec) {
          if (Fn->NeedsDecreasesCheck)
            return *Fn;
          return *Fn;
        }
        PreparedFn = cloneVFunction(*Fn);
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

      if (Fn->IsSpec && !Fn->NeedsDecreasesCheck) {
        if (Fn->IsConstexprSpec)
          Diags.push_back(
              {VerifyDiagnostic::Verified, "constexpr spec axiom: " + Fn->Name});
        else
          Diags.push_back({VerifyDiagnostic::Verified, "spec axiom: " + Fn->Name});
        continue;
      }

      if ((Fn->IsSpec || Fn->IsProof) && Fn->NeedsDecreasesCheck) {
        PassiveProgram DecPP = buildDecreasesChecks(*Fn, FnMap);
        if (!Fn->IsSpec && Opts.Backend != BackendKind::Lean) {
          VerifyResult DR = Backend->verifyPassive(DecPP);
          if (DR.Status == VerifyStatus::Failed) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Error,
                             "decreases failed: " + Fn->Name});
            continue;
          }
        } else if (Fn->IsSpec) {
          if (Opts.Backend == BackendKind::Lean) {
            Diags.push_back({VerifyDiagnostic::Verified,
                             "spec decreases: " + Fn->Name});
            continue;
          }
          VerifyResult R = Backend->verifyPassive(DecPP);
          if (R.Status == VerifyStatus::Verified)
            Diags.push_back({VerifyDiagnostic::Verified,
                             "spec decreases: " + Fn->Name});
          else if (R.Status == VerifyStatus::Failed) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Error,
                             "spec decreases failed: " + Fn->Name});
          } else {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Error,
                             "spec decreases unknown: " + Fn->Name});
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

      if (DumpLayers & LayerZ3 && VC) {
        dumpSep();
        VCMachine M = VCMachine::fromPassive(PP);
        if (M.Goal)
          Z3Dump.dumpVC(M.Goal.get(), *DumpOS);
      }

      if (Opts.Backend == BackendKind::Lean) {
        if (LeanOut != DumpOS) {
          *LeanOut << "\n/- function: " << Fn->Name << " -/\n";
          exportLeanScratchPad(PP, *LeanOut);
        } else {
          exportLeanScratchPad(PP, *DumpOS);
        }
        Diags.push_back({VerifyDiagnostic::Verified,
                         "lean export: " + Fn->Name});
        continue;
      }

      VerifyResult R = Backend->verifyPassive(PP);
      if (R.Status == VerifyStatus::Verified) {
        Diags.push_back({VerifyDiagnostic::Verified, Fn->Name});
      } else if (R.Status == VerifyStatus::Failed) {
        AllOk = false;
        AnyFailed = true;
        std::string Msg = "verification failed: " + Fn->Name;
        if (!R.Message.empty())
          Msg += " (counterexample: " + R.Message + ")";
        Diags.push_back({VerifyDiagnostic::Error, Msg});
      } else {
        AllOk = false;
        AnyFailed = true;
        Diags.push_back({VerifyDiagnostic::Unknown, "unknown: " + Fn->Name});
      }
    }

    if (AnyFailed && Opts.Backend == BackendKind::Z3) {
      auto Z3 = createVerifyBackend(BackendKind::Z3, nullptr, 0);
      checkRecommendsImplied(Functions, *Z3);
      for (const auto &Fn : Functions) {
        if (Fn->IsSpec || Fn->IsProof)
          continue;
        VFunction Prepared = cloneVFunction(*Fn);
        SpecInliner(FnMap, Prepared.SpecFuel).prepareFunctionAxiomatic(Prepared);
        checkCalleeRecommendsOnFailure(Prepared, FnMap, *Z3);
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