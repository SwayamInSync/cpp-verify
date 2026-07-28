// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: grep -Eq 'theorem cppverify_inc_fn_[0-9a-f]+_correct' %t.lean
// RUN: grep -Eq 'theorem cppverify_inc_fn_[0-9a-f]+_obligation_[0-9]+' %t.lean
// RUN: grep -Fq 'kind: postcondition' %t.lean
// RUN: grep -q 'sorry' %t.lean

int inc(int x)
  pre(x >= 0 && x < 100)
  post(result == x + 1)
{
  return x + 1;
}

// VERIFY: Exported: lean obligation: inc