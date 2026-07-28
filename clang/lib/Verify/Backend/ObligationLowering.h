//===--- ObligationLowering.h - VCR to canonical obligations -----*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONLOWERING_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONLOWERING_H

#include "../IR/VExpr.h"
#include "../Transform/Passivize.h"
#include "Obligation.h"

namespace clang {
namespace verify {

llvm::Expected<ObligationModule>
buildObligationModule(const PassiveProgram &Program);

llvm::Expected<std::unique_ptr<LogicExpr>>
lowerLogicExpr(const VExpr *Expr, const std::string &ResultVar,
               const std::string &CurrentHeap,
               VIntMode CallerMode = VIntMode::Math);

} // namespace verify
} // namespace clang

#endif
