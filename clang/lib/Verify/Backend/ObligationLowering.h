//===--- ObligationLowering.h - VCR to canonical obligations -----*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONLOWERING_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONLOWERING_H

#include "../IR/VExpr.h"
#include "../Transform/Passivize.h"
#include "Obligation.h"

namespace clang {
namespace verify {

/// Something a function's verification builds would have more expression
/// nodes than the limit allows (--max-query-nodes), found before or as it
/// was built: the obligations, each repeating every assumption before it
/// (their size is known before any is built), or a spec's definition
/// unfolded as deep as its fuel.
class ObligationSizeError : public llvm::ErrorInfo<ObligationSizeError> {
public:
  static char ID;
  ObligationSizeError(std::string What, uint64_t Nodes, uint64_t Limit,
                      std::string Advice)
      : What(std::move(What)), Nodes(Nodes), Limit(Limit),
        Advice(std::move(Advice)) {}
  /// The obligations of a module of \p Nodes nodes.
  static llvm::Error obligations(uint64_t Nodes, uint64_t Limit);
  void log(llvm::raw_ostream &OS) const override;
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }
  std::string What;
  /// At least this many: a construction stops once it passes the limit.
  uint64_t Nodes;
  uint64_t Limit;
  std::string Advice;
};

/// With \p MaxNodes, a module that would have more nodes than that (as
/// obligationModuleNodeCount counts them) is an ObligationSizeError, before
/// its goals are built. So is a program one of whose constructions passed
/// its limit (PassiveProgram::TooLarge).
llvm::Expected<ObligationModule>
buildObligationModule(const PassiveProgram &Program, uint64_t MaxNodes = 0);

ObligationKind obligationKind(ProofObligationKind Kind);

llvm::Expected<std::unique_ptr<LogicExpr>>
lowerLogicExpr(const VExpr *Expr, const std::string &ResultVar,
               const std::string &CurrentHeap,
               VIntMode CallerMode = VIntMode::Math,
               const FunctionMap *Functions = nullptr);

} // namespace verify
} // namespace clang

#endif
