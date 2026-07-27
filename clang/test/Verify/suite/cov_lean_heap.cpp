// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: grep -Eq 'theorem cppverify_swap_val_fn_[0-9a-f]+_correct' %t.lean

int swap_val(int *a, int *b)
  pre(a != 0 && b != 0 && a != b)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
  int t = *a;
  *a = *b;
  *b = t;
  return 0;
}

// VERIFY: Exported: lean obligation: swap_val