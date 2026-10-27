// RUN: not %python %S/Inputs/within_seconds.py 40 %cpp-verify --jobs=1 --timeout=60000 %s -- 2>&1 | FileCheck %s
// RUN: not %python %S/Inputs/within_seconds.py 40 %cpp-verify --jobs=3 --timeout=60000 %s -- 2>&1 | FileCheck %s
//
// How long the complete query's search takes depends on Z3's search order,
// which differs between machines (Z3 hashes some objects by address): on the
// three-core macOS runners the run took more than 40 s, which only the 60 s
// path explains, while it takes 1.7 s on Linux. The time is measured there.
// UNSUPPORTED: system-darwin

// The complete query refutes the postcondition at once, but the solver's
// search for a counterexample to the postcondition's own query does not end
// within the timeout. The complete query's certified counterexample is
// reported without waiting for that search: well within 40 s, where waiting
// takes the 60 s timeout. The body reads p first, so p is an input whose
// storage is initialized, and the postcondition is the first check that
// fails.

cppverify::spec bool valid(int *p, int n) { return true; }

void break_heap_wrong(int *p)
  cppverify::pre(valid(p, 3))
  cppverify::modifies(*p)
  cppverify::post(p[2] == 1)
{
  int last = p[2];
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
// CHECK: error: verification failed: break_heap_wrong [{{.*}}::postcondition@23:24] {{.*}}[reason=counterexample]
// CHECK-NOT: within_seconds
