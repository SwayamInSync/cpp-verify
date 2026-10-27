// RUN: %python %S/Inputs/interrupt_after.py 1 4 %cpp-verify --jobs=1 --timeout=600000 %s -- | FileCheck %s

// Ctrl-C also stops the evaluation of a definition. Before it solves, the
// verifier computes span_sum(0, 100000000) from the definition, which takes
// tens of millions of applications.

cppverify::spec int span_sum(int lo, int hi)
  cppverify::decreases(hi - lo)
{
  return hi - lo <= 0 ? 0
       : hi - lo == 1 ? lo
       : span_sum(lo, lo + (hi - lo) / 2) + span_sum(lo + (hi - lo) / 2, hi);
}

cppverify::proof void large_sum()
  cppverify::post(span_sum(0, 100000000) == 4999999950000000)
{
}

// CHECK:      Interrupted: large_sum
// CHECK-NEXT: Summary: {{.*}}
// CHECK-NEXT: exit: 130
