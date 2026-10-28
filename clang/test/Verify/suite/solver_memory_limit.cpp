// RUN: not %cpp-verify --jobs=1 --timeout=60000 --memory-limit=100 %s -- 2>&1 \
// RUN:   | FileCheck %s
// RUN: not %cpp-verify --jobs=1 --timeout=60000 --memory-limit=100 \
// RUN:   --diagnostics-format=json %s -- 2>&1 | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --backend=lean --memory-limit=100 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=LEAN

// A matching loop: each instance of the quantifier makes a term that matches
// it again, so Z3's memory grows until something stops the query. Without a
// memory limit that is the timeout, at 2 GB after 20 s.
cppverify::spec int g(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : g(n - 1);
}

void matching_loop(int a)
  cppverify::pre(cppverify::forall(k, cppverify::trigger(g(k)) == g(k + 1) + 1))
{
  cppverify::ghost { cppverify::hide(g); }
  cppverify::check(g(a) > 100);
}
// CHECK: solver_memory_limit.cpp:[[@LINE-2]]:3: Unresolved: matching_loop [backend=z3] [reason=solver.memory-limit] ({{.*}}: Z3 reached the memory limit: its queries share 100 MB (--memory-limit))
// JSON: "function":"matching_loop"{{.*}}"reason":"solver.memory-limit"

// The memory of a stopped query is freed, and the next one runs within the
// limit.
int small(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}
// CHECK: Verified: small [backend=z3]

// LEAN: error: --memory-limit requires a backend that runs an SMT solver
