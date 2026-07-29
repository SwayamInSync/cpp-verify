// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only --dump-ir=3 %s > %t.first 2>&1
// RUN: %cpp-verify --lower-only --dump-ir=3 %s > %t.second 2>&1
// RUN: diff %t.first %t.second
// RUN: FileCheck %s --input-file=%t.first --check-prefix=LOGIC
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s
// RUN: FileCheck %s --input-file=%t.lean --check-prefix=LEAN

spec int hidden(int x) { return x + 1; }

spec int countdown(int n)
  decreases(n)
{
  if (n <= 0)
    return 0;
  return 1 + countdown(n - 1);
}

proof void recursive_logic()
  post(countdown(2) == 2)
{
  reveal_with_fuel(countdown, 3);
}

proof void opaque_logic()
  pre(hidden(1) == 2)
  post(hidden(1) == 2)
{
  hide(hidden);
}

// LOGIC-LABEL: vc recursive_logic
// LOGIC: logic-functions 1
// LOGIC-NEXT: function [[COUNTDOWN:fn_[0-9a-f]+]] countdown math
// LOGIC-NEXT: parameter n int signed
// LOGIC-NEXT: result int signed
// LOGIC-NEXT: fuel 3
// LOGIC-NEXT: step
// LOGIC: spec_call [[COUNTDOWN]] : int
// LOGIC: definition 1
// LOGIC: spec_call [[COUNTDOWN]] : int
// LOGIC: definition 2
// LOGIC: spec_call [[COUNTDOWN]] : int
// LOGIC: definition 3
// LOGIC: spec_call [[COUNTDOWN]] : int
// LOGIC-LABEL: vc opaque_logic
// LOGIC: logic-functions 1
// LOGIC-NEXT: function [[HIDDEN:fn_[0-9a-f]+]] hidden math
// LOGIC-NEXT: parameter x int signed
// LOGIC-NEXT: result int signed
// LOGIC-NEXT: fuel 0
// LOGIC-NOT: step
// LOGIC-NOT: definition
// LOGIC: Lowered: spec axiom: hidden

// Z3-DAG: Verified: recursive_logic
// Z3-DAG: Verified: opaque_logic

// LEAN: opaque cppSpec_[[LEAN_COUNTDOWN:fn_[0-9a-f]+]] : Int -> Int
// LEAN: def cppSpecBody_m{{[0-9]+}}_[[LEAN_COUNTDOWN]]_1
// LEAN: def cppSpecBody_m{{[0-9]+}}_[[LEAN_COUNTDOWN]]_2
// LEAN: def cppSpecBody_m{{[0-9]+}}_[[LEAN_COUNTDOWN]]_3
// LEAN: opaque cppSpec_[[LEAN_HIDDEN:fn_[0-9a-f]+]] : Int -> Int
// LEAN-NOT: cppSpecBody_m{{[0-9]+}}_[[LEAN_HIDDEN]]
