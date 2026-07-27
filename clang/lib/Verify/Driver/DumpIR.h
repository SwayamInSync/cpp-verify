//===--- DumpIR.h - Textual dumps of verification IR --------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_DUMPIR_H
#define LLVM_CLANG_VERIFY_DRIVER_DUMPIR_H

#include "../Backend/Obligation.h"
#include "../IR/VExpr.h"
#include "../IR/VStmt.h"
#include "../Transform/Passivize.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm {
class StringRef;
}

namespace clang {
namespace verify {

enum IRLayer : unsigned {
  LayerVCR = 1 << 0,
  LayerPassive = 1 << 1,
  LayerVC = 1 << 2,
  LayerZ3 = 1 << 3,
  LayerAll = LayerVCR | LayerPassive | LayerVC | LayerZ3,
};

/// Parse `--dump-ir` value: empty / "all" → all layers; "1,2,3,4" or
/// "layer-1,...".
unsigned parseDumpIRLayers(llvm::StringRef Spec);

void dumpVExpr(const VExpr *E, llvm::raw_ostream &OS, unsigned Indent = 0);
void dumpVFunction(const VFunction &Fn, llvm::raw_ostream &OS);
void dumpPassiveProgram(llvm::StringRef FnName, const PassiveProgram &P,
                        llvm::raw_ostream &OS);
void dumpVC(const ObligationModule &Module, llvm::raw_ostream &OS);

} // namespace verify
} // namespace clang

#endif