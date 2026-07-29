// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=IR
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int unused_when_folded(int value) {
  return value + 1;
}

int canonical_bool_simplification(int value)
  pre(true)
  post(result == value)
{
  contract_assert(true && !!(value == value));
  contract_assert((value == value) || unused_when_folded(value) > 0);
  return value;
}

// IR-LABEL: vc canonical_bool_simplification
// IR: simplification nodes {{[1-9][0-9]*}} -> {{[1-9][0-9]*}}, rewrites {{[1-9][0-9]*}}, functions-removed 0
// IR: features mathematical-integers, bit-vectors, pointers, heap-arrays
// IR-NOT: spec-functions
// IR: logic-functions 0
// IR-NOT: function {{.*}} unused_when_folded
// VERIFY: Verified: canonical_bool_simplification
