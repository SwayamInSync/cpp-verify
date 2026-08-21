// RUN: rm -rf %t.project
// RUN: not %cpp-verify --solver-rlimit=1 --lean-fallback=%t.project %s 2>&1 \
// RUN:   | FileCheck %s
// RUN: test -f %t.project/CppVerify/Check.lean
// RUN: grep -c '^import CppVerify.Proofs.Goal_' \
// RUN:   %t.project/CppVerify/Check.lean | FileCheck %s --check-prefix=GOALS

spec int double_value(int value) {
  return value + value;
}

proof void lemma_double_value(int value)
  pre(value >= 0 && value <= 1000)
  post(double_value(value) == 2 * value)
{
}

// CHECK-DAG: Verified: spec axiom: double_value
// CHECK-DAG: Exported: lean fallback: lemma_double_value
// CHECK-DAG: Unresolved: lemma_double_value [backend=z3] [reason=solver.resource-limit] (proof obligation
// GOALS: 3
