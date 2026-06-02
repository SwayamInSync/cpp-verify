//===--- Verifier.cpp - CppVerify driver ----------------------------------===//
#include "clang/AST/ASTContext.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceManager.h"
#include "../Frontend/ASTConverter.h"
#include "../Transform/Passivize.h"
#include "../Backend/WPCalc.h"
#include "../Backend/Z3Encode.h"
#include "Verifier.h"
#include "DumpIR.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"

namespace clang {
namespace verify {

struct VerifyDiagnostic {
  enum Kind { Verified, Error, Warning, Unknown };
  Kind K;
  std::string Message;
  SourceLocation Loc;
};

class Verifier {
  ASTContext &Ctx;
  VerifyOptions Opts;
  llvm::raw_ostream *DumpOS = nullptr;
  std::vector<VerifyDiagnostic> Diags;

public:
  Verifier(ASTContext &Ctx, const VerifyOptions &Opts, llvm::raw_ostream &DumpOS)
      : Ctx(Ctx), Opts(Opts), DumpOS(&DumpOS) {}

  bool run() {
    ASTConverter Converter(Ctx);
    auto Functions = Converter.convertTranslationUnit();
    if (Functions.empty()) {
      Diags.push_back({VerifyDiagnostic::Warning, "no verifiable functions found",
                       SourceLocation()});
      return true;
    }

    Passivizer P;
    WPCalculator WP;
    Z3Encoder Z3;

    const unsigned DumpLayers = Opts.DumpIRLayers;
    const bool MultiLayerDump = llvm::popcount(DumpLayers) > 1;
    bool AllOk = true;
    for (const auto &Fn : Functions) {
      bool DumpedAny = false;
      auto dumpSep = [&]() {
        if (DumpedAny && MultiLayerDump)
          *DumpOS << "======\n";
        DumpedAny = true;
      };

      if (DumpLayers & LayerVCR) {
        dumpSep();
        dumpVFunction(*Fn, *DumpOS);
      }

      PassiveProgram PP = P.run(*Fn);
      if (DumpLayers & LayerPassive) {
        dumpSep();
        dumpPassiveProgram(Fn->Name, PP, *DumpOS);
      }

      auto VC = WP.computeVC(PP);
      if (DumpLayers & LayerVC && VC) {
        dumpSep();
        dumpVC(Fn->Name, VC.get(), *DumpOS);
      }

      if (!VC) {
        AllOk = false;
        Diags.push_back(
            {VerifyDiagnostic::Error, "failed to build VC for " + Fn->Name,
             SourceLocation()});
        continue;
      }
      if (DumpLayers & LayerZ3) {
        dumpSep();
        dumpZ3(VC.get(), *DumpOS);
      }
      Z3CheckResult R = Z3.checkVC(VC.get());
      if (R.S == Z3CheckResult::Verified) {
        Diags.push_back({VerifyDiagnostic::Verified,
                         "verified: " + Fn->Name, SourceLocation()});
      } else if (R.S == Z3CheckResult::Failed) {
        AllOk = false;
        std::string Msg = "verification failed: " + Fn->Name;
        if (!R.Counterexample.empty())
          Msg += " (counterexample: " + R.Counterexample + ")";
        Diags.push_back({VerifyDiagnostic::Error, Msg, SourceLocation()});
      } else {
        AllOk = false;
        Diags.push_back({VerifyDiagnostic::Unknown,
                         "unknown: " + Fn->Name, SourceLocation()});
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

bool verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                           const VerifyOptions &Opts) {
  Verifier V(Ctx, Opts, OS);
  bool Ok = V.run();
  V.printDiagnostics(OS);
  return Ok;
}

} // namespace verify
} // namespace clang