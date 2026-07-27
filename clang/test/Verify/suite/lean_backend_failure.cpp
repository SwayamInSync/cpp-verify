// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=lean --timeout=1 --lean-out=%t.lean %s 2>&1 | FileCheck %s
// RUN: grep -q 'unchecked Lean scratch-pad' %t.lean
// RUN: grep -Eq 'theorem cppverify_invalid_lean_export_fn_[0-9a-f]+_correct' %t.lean
// RUN: grep -Fq ': ¬ (' %t.lean
// RUN: not grep -q 'Z3 check:' %t.lean

int invalid_lean_export(int x)
  post(result == x + 1)
{
  return x;
}

// CHECK: Exported: lean obligation: invalid_lean_export
