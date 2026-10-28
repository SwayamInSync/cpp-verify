// RUN: rm -rf %t && mkdir -p %t
// RUN: %cpp-verify --lean-project=%t/project %s -- 2>&1 | FileCheck %s --check-prefix=PROJECT
// RUN: test -f %t/project/CppVerify/Generated.lean
// RUN: %cpp-verify --lean-out=%t/goal.lean %s -- 2>&1 | FileCheck %s --check-prefix=EXPORT
// RUN: test -f %t/goal.lean
// RUN: %cpp-verify --unroll=3 %s -- 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --backend=z3 --unroll=3 %s -- 2>&1 | FileCheck %s --check-prefix=UNROLL
// RUN: not %cpp-verify --lean-out=%t/both.lean --unroll=3 %s -- 2>&1 | FileCheck %s --check-prefix=UNROLL
// RUN: not %cpp-verify --lean-fallback-scope=all %s -- 2>&1 | FileCheck %s --check-prefix=SCOPE
// RUN: not %cpp-verify --proof-cache-max-entries=2 %s -- 2>&1 | FileCheck %s --check-prefix=CACHE
// RUN: not %cpp-verify --backend=cvc5 --profile-quantifiers %s -- 2>&1 | FileCheck %s --check-prefix=PROFILE
// RUN: not %cpp-verify --lean-out=%t/other.lean --int-encoding=integer %s -- 2>&1 | FileCheck %s --check-prefix=ENCODING
// RUN: %cpp-verify --lower-only --obligation-out=%t/goals.cpv %s --
// RUN: %cpp-verify --obligation-in=%t/goals.cpv --lean-out=%t/replay.lean 2>&1 | FileCheck %s --check-prefix=REPLAY-LEAN
// RUN: not %cpp-verify --obligation-in=%t/goals.cpv --check-ub 2>&1 | FileCheck %s --check-prefix=REPLAY-UB
// RUN: not %cpp-verify --obligation-in=%t/goals.cpv --profile-quantifiers 2>&1 | FileCheck %s --check-prefix=REPLAY-PROFILE
// RUN: not %cpp-verify --obligation-in=%t/goals.cpv --unroll=1 2>&1 | FileCheck %s --check-prefix=REPLAY-UNROLL
// RUN: not %cpp-verify --lean-out=%t/budget.lean --timeout=1000 %s -- 2>&1 | FileCheck %s --check-prefix=TIMEOUT
// RUN: not %cpp-verify --lean-project=%t/budget --function-timeout=1000 %s -- 2>&1 | FileCheck %s --check-prefix=FUNCTION
// RUN: not test -e %t/budget
// RUN: not %cpp-verify --backend=lean --collection-timeout=1000 %s -- 2>&1 | FileCheck %s --check-prefix=COLLECTION
// RUN: not %cpp-verify --lean-out=%t/budget.lean --certify-timeout=1000 %s -- 2>&1 | FileCheck %s --check-prefix=CERTIFY
// RUN: not %cpp-verify --lean-out=%t/budget.lean --solver-rlimit=100000 %s -- 2>&1 | FileCheck %s --check-prefix=RLIMIT
// RUN: not %cpp-verify --lean-out=%t/budget.lean --memory-limit=4096 %s -- 2>&1 | FileCheck %s --check-prefix=MEMORY
// RUN: not test -e %t/budget.lean
// RUN: %cpp-verify --lean-out=%t/nodes.lean --max-query-nodes=100000 %s -- 2>&1 | FileCheck %s --check-prefix=NODES
// RUN: not %cpp-verify --obligation-in=%t/goals.cpv --lean-out=%t/budget.lean --timeout=1000 2>&1 | FileCheck %s --check-prefix=TIMEOUT
// RUN: %cpp-verify --timeout=20000 --function-timeout=200000 --solver-rlimit=50000000 --max-query-nodes=1000000 %s -- 2>&1 | FileCheck %s --check-prefix=SOLVER
// RUN: %cpp-verify --lean-fallback=%t/fallback --timeout=20000 %s -- 2>&1 | FileCheck %s --check-prefix=SOLVER
//
// An option one backend alone uses selects it when no backend is named, and
// an option the run would ignore is an error: Lean export runs no solver, so
// no solver option applies to it.

int count(int n)
  cppverify::pre(0 <= n && n <= 2)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}

// PROJECT: Exported: lean obligation: count
// EXPORT: Exported: lean obligation: count
// BMC: Verified: count [backend=bmc
// UNROLL: error: --unroll requires --backend=bmc
// SCOPE: error: --lean-fallback-scope requires --lean-fallback
// CACHE: error: --proof-cache-max-mb and --proof-cache-max-entries require --proof-cache
// PROFILE: error: --profile-quantifiers requires a backend that runs Z3
// ENCODING: error: --int-encoding requires a backend that runs an SMT solver
// REPLAY-LEAN: Exported: lean obligation: count [backend=lean]
// REPLAY-UB: error: --check-ub and --no-check-ub apply to source verification
// REPLAY-PROFILE: error: --profile-quantifiers applies to source verification
// REPLAY-UNROLL: error: --unroll requires a BMC-transformed archive
// TIMEOUT: error: --timeout requires a backend that runs an SMT solver
// FUNCTION: error: --function-timeout requires a backend that runs an SMT solver
// COLLECTION: error: --collection-timeout requires a backend that runs an SMT solver
// CERTIFY: error: --certify-timeout requires a backend that runs an SMT solver
// RLIMIT: error: --solver-rlimit requires a backend that runs an SMT solver
// MEMORY: error: --memory-limit requires a backend that runs an SMT solver
// NODES: Exported: lean obligation: count
// SOLVER: Verified: count [backend=z3]
