// REQUIRES: cvc5, system-linux
// RUN: not %cpp-verify --backend=cvc5 --jobs=1 --memory-limit=5 %s -- 2>&1 \
// RUN:   | FileCheck %s
//
// Each cvc5 process may allocate --memory-limit megabytes; on Linux that is
// its data (RLIMIT_DATA). cvc5 needs more than 5 to start solving, so every
// query runs out, which cvc5 reports as std::bad_alloc or as its SAT solver's
// OutOfMemoryException.

int small(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}
// CHECK: Unresolved: small [backend=cvc5] [reason=solver.memory-limit] ({{.*}}: cvc5 ran out of memory: each cvc5 process may use 5 MB (--memory-limit))
