// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// A spec's post holds for every argument. It is proved together with the
// spec's termination by well-founded induction on the measure: a recursive
// call may assume the post only where its measure is lower. Callers then
// assume it at each application, without unfolding the definition.

// Nested recursion terminates only because of what g returns.
spec int g(int n)
  decreases(n)
  post(result >= 0 && result <= (n < 0 ? 0 : n))
{
  return n <= 0 ? 0 : g(g(n - 1));
}
// CHECK-DAG: Verified: spec decreases and post: g

spec int m91(int n)
  decreases(n > 100 ? 0 : 101 - n)
  post(n > 100 ? result == n - 10 : result == 91)
{
  return n > 100 ? n - 10 : m91(m91(n + 11));
}
// CHECK-DAG: Verified: spec decreases and post: m91

void uses_m91(int n)
  pre(n <= 100)
{
  ghost { contract_assert(m91(n) == 91); }
}
// CHECK-DAG: Verified: uses_m91

// The post never assumes itself at the same argument.
spec int loops(int n)
  decreases(n)
  post(result == 0)
{
  return n <= 0 ? 0 : loops(loops(n));
}
// CHECK-DAG: Unresolved: spec decreases and post unresolved: loops

spec int half(int n)
  decreases(n)
  post(result * 2 == n)
{
  return n <= 1 ? 0 : 1 + half(n - 2);
}
// CHECK-DAG: error: spec decreases and post failed: half {{.*}}[reason=counterexample]

void uses_half()
{
  ghost { contract_assert(half(4) == 2); }
}
// CHECK-DAG: Unresolved: uses_half {{.*}}[reason=spec.termination]

spec int clamp(int x)
  post(result >= 0 && result <= 100)
{
  return x < 0 ? 0 : (x > 100 ? 100 : x);
}
// CHECK-DAG: Verified: spec post: clamp

// A call keeps the post where the definition is hidden.
void clamped(int x)
{
  ghost {
    hide(clamp);
    contract_assert(clamp(x) <= 100);
  }
}
// CHECK-DAG: Verified: clamped

spec int bad_clamp(int x)
  post(result >= 0)
{
  return x > 100 ? 100 : x;
}
// CHECK-DAG: error: spec post failed: bad_clamp [backend={{.*}}] [reason=counterexample] (x [type=math-i32] = {{-[0-9]+}})

void uses_bad_clamp(int x)
{
  ghost {
    hide(bad_clamp);
    contract_assert(bad_clamp(x) >= 0);
  }
}

// Unfolded, the definition decides.
void unfolds_bad_clamp(int x)
{
  ghost { contract_assert(bad_clamp(x) >= 0); }
}
// CHECK-DAG: error: verification failed: unfolds_bad_clamp {{.*}}(counterexample: x [ssa=x_0] [type=i32] = {{-[0-9]+}})
// CHECK-DAG: Unresolved: uses_bad_clamp {{.*}}[reason=spec.post] (relies on the postcondition of bad_clamp, which is not established)
// JSON-DAG: "function":"uses_bad_clamp"{{.*}}"reason":"spec.post"{{.*}}"status":"unresolved"
