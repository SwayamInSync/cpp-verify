//===--- NodeBudget.h - Bounds on the expression trees built ----*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_NODEBUDGET_H
#define LLVM_CLANG_VERIFY_IR_NODEBUDGET_H

#include <cstdint>

namespace clang {
namespace verify {

/// Counts the expression nodes (VExpr and LogicExpr) built on this thread
/// while it lives, against the limit the driver sets for the function being
/// verified (--max-query-nodes). A construction whose size can outgrow the
/// program, such as a spec unfolded as deep as its fuel, runs in a budget
/// and stops where it can once the limit is passed; its owner then reports
/// the function as too large and never uses the partial result.
class NodeBudget {
public:
  /// The limit for the budgets of this thread while it lives; 0: none.
  class Limit {
  public:
    explicit Limit(uint64_t Nodes);
    ~Limit();
    Limit(const Limit &) = delete;
    Limit &operator=(const Limit &) = delete;

  private:
    uint64_t Saved;
  };

  /// A budget inside another counts toward it too.
  NodeBudget();
  ~NodeBudget();
  NodeBudget(const NodeBudget &) = delete;
  NodeBudget &operator=(const NodeBudget &) = delete;

  /// The nodes built in this budget and those enclosing it.
  uint64_t built() const { return Built + (Outer ? Outer->built() : 0); }
  /// The thread's limit when the budget began, 0 when there is none.
  uint64_t limit() const { return Max; }
  bool exceeded() const { return Max != 0 && built() > Max; }

  /// Whether the innermost budget of this thread is exceeded: where a
  /// construction can stop, it checks this.
  static bool exhausted() { return Active && Active->exceeded(); }
  /// Counts one node; the constructors of expression nodes call it.
  static void count() {
    if (Active)
      ++Active->Built;
  }

private:
  static thread_local NodeBudget *Active;
  NodeBudget *Outer;
  uint64_t Built = 0;
  uint64_t Max;
};

} // namespace verify
} // namespace clang

#endif
