// REQUIRES: cvc5, system-linux
// RUN: not %cpp-verify --backend=cvc5 --jobs=1 --memory-limit=16 %s -- 2>&1 \
// RUN:   | FileCheck %s
//
// Each cvc5 process may allocate --memory-limit megabytes; on Linux that is
// its data (RLIMIT_DATA). Bit-blasting these 64-bit products needs far more
// than 16, so every query runs out once it is solving, which cvc5 reports as
// std::bad_alloc or as its SAT solver's OutOfMemoryException. At a few
// megabytes cvc5 may instead crash where an allocation fails, at limits that
// differ between versions and builds (1.1.2 at 1 and 6, 1.4.2 at 2 and 3),
// and 1.4.2 solves a small query within 4.

unsigned long long mix(unsigned long long a, unsigned long long b,
                       unsigned long long c)
  cppverify::post(cppverify::result == (a ^ b) * (b ^ c) * (c ^ a))
{
  return (a ^ b) * (b ^ c) * (c ^ a);
}
// CHECK: Unresolved: mix [backend=cvc5] [reason=solver.memory-limit] ({{.*}}: cvc5 ran out of memory: each cvc5 process may use 16 MB (--memory-limit))
