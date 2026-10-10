// RUN: not %python %S/Inputs/within_seconds.py 20 %cpp-verify --jobs=1 --timeout=60000 %s -- 2>&1 | FileCheck %s
// RUN: not %python %S/Inputs/within_seconds.py 20 %cpp-verify --jobs=3 --timeout=60000 %s -- 2>&1 | FileCheck %s

// The complete query refutes the postcondition at once, but the solver's
// search for a counterexample to the postcondition's own query does not end
// within the timeout. The complete query's certified counterexample is
// reported without waiting for that search.

cppverify::spec bool valid(int *p, int n) { return true; }

void break_heap_wrong(int *p)
  cppverify::pre(valid(p, 3))
  cppverify::modifies(*p)
  cppverify::post(p[2] == 1)
{
  int i = 0;
  while (i < 3)
    cppverify::invariant(0 <= i && i <= 1)
    cppverify::invariant(cppverify::forall(k, 0, i, p[k] == 1))
    cppverify::decreases(3 - i)
  {
    p[i] = 1;
    if (i == 1)
      break;
    i = i + 1;
  }
}
// CHECK: error: verification failed: break_heap_wrong [{{.*}}::postcondition@14:24] {{.*}}[reason=counterexample]
// CHECK-NOT: within_seconds
