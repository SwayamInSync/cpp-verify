// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: grep -Eq 'theorem cppverify_abs_fn_[0-9a-f]+_correct' %t.lean
// RUN: grep -q 'unchecked Lean scratch-pad' %t.lean
// RUN: grep -q 'sorry' %t.lean

int abs(int x)
  pre(x != (-2147483647 - 1))
  post(result >= 0)
{
  return x < 0 ? -x : x;
}

// VERIFY: Exported: lean obligation: abs