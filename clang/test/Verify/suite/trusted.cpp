// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s -- 2>/dev/null \
// RUN:   | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify %s -- -std=c++17 -DTRUSTED_SPEC 2>&1 \
// RUN:   | FileCheck %s --check-prefix=SPEC
// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only -Werror %s
//
// [[cppverify::trusted]] marks the boundary of what is verified, like
// Verus's #[verifier::external_body]: the contract is assumed, any body is
// compiled but not verified, and every proof that relies on it says so with
// [trusts=...], transitively. A contract without a definition and without
// the mark verifies nothing that calls it.

// A library function: no definition here.
[[cppverify::trusted]] int clamp_byte(int v)
  cppverify::post(0 <= cppverify::result && cppverify::result <= 255);
// CHECK-DAG: trusted.cpp:[[@LINE-2]]:28: Trusted: clamp_byte (contract assumed, not verified)

// A definition whose body is not verified.
[[cppverify::trusted]] int read_sensor(int channel)
  cppverify::pre(channel >= 0 && channel < 4)
  cppverify::post(cppverify::result >= 0 && cppverify::result <= 1023)
{
  return channel * 300;
}
// CHECK-DAG: Trusted: read_sensor (contract assumed, not verified)

// An axiom: a proof function without a proof.
cppverify::spec int sq(int x) { return x * x; }

[[cppverify::trusted]] cppverify::proof void sq_nonnegative(int x)
  cppverify::post(sq(x) >= 0);
// CHECK-DAG: Trusted: sq_nonnegative (contract assumed, not verified)

int sample(int c)
  cppverify::pre(c >= 0 && c < 4)
  cppverify::post(0 <= cppverify::result && cppverify::result <= 255)
{
  int r = read_sensor(c);
  cppverify::ghost { sq_nonnegative(r); }
  return clamp_byte(r);
}
// CHECK-DAG: Verified: sample [backend=z3] [trusts=clamp_byte,read_sensor,sq_nonnegative]
// JSON-DAG: "function":"sample"{{.*}}"status":"verified","trusts":["clamp_byte","read_sensor","sq_nonnegative"]

// Trust is transitive: sample's proof rests on the trusted contracts.
int twice(int c)
  cppverify::pre(c >= 0 && c < 4)
  cppverify::post(0 <= cppverify::result && cppverify::result <= 510)
{
  int a = sample(c);
  int b = sample(c);
  return a + b;
}
// CHECK-DAG: Verified: twice [backend=z3] [trusts=clamp_byte,read_sensor,sq_nonnegative]

// The trusted contract is used as written.
int too_much(int c)
  cppverify::pre(c >= 0 && c < 4)
  cppverify::post(cppverify::result <= 100)
{
  return clamp_byte(read_sensor(c));
}
// CHECK-DAG: error: verification failed: too_much

// Unmarked, a contract without a definition proves nothing.
int helper(int v)
  cppverify::post(cppverify::result == v);

int uses_helper(int v)
  cppverify::post(cppverify::result == v)
{
  return helper(v);
}
// CHECK-DAG: warning: helper has a contract but no definition, so its callers are not verified; mark the declaration {{\[\[}}cppverify::trusted]] to assume the contract
// CHECK-DAG: Unresolved: uses_helper [backend=z3] [reason=callee.contract] (relies on the contract of helper (no definition; mark it {{\[\[}}cppverify::trusted]] to assume it), which is not established)

// A trusted contract writes nothing through a pointer to const, so a call
// keeps every cell and a valid extent crosses it.
#include <cppverify.h>

[[cppverify::trusted]] int index_of_max(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 1)
  cppverify::post(0 <= cppverify::result && cppverify::result < n)
  cppverify::post(cppverify::forall(k, 0, n, a[k] <= a[cppverify::result]));

int largest(const int *a, int n, int *seen)
  cppverify::pre(cppverify::valid(a, n) && n >= 1 && n <= 1000)
  cppverify::pre(cppverify::valid(seen, 1))
  cppverify::post(cppverify::forall(k, 0, n, a[k] <= cppverify::result) && *seen == cppverify::old(*seen))
{
  int i = index_of_max(a, n);
  return a[i];
}
// CHECK-DAG: Verified: largest [backend=z3] [trusts=index_of_max]

#ifdef TRUSTED_SPEC
[[cppverify::trusted]] cppverify::spec int arbitrary(int x) { return x; }
#endif
// SPEC: error: arbitrary: {{\[\[}}cppverify::trusted]] does not apply to a spec function, whose definition is its meaning
