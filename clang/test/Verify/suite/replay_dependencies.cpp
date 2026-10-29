// RUN: rm -f %t.cpv
// RUN: not %cpp-verify --obligation-out=%t.cpv %s -- 2>&1 | FileCheck %s --check-prefix=SOURCE
// RUN: not %cpp-verify --obligation-in=%t.cpv 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REPLAY --implicit-check-not=Verified
// RUN: not %cpp-verify --obligation-in=%t.cpv --diagnostics-format=json 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON --implicit-check-not='"status":"verified"'
//
// Replay proves each archived module alone. A source verdict also rests on
// callee contracts, trust, termination, and vacuity, which replay does not
// check, so a replayed proof is never reported as verified.

// caller's proof rests on the contract of bad_callee, which is false.
int bad_callee(int x)
  cppverify::post(cppverify::result > 0)
{
  return x;
}

int caller(int x)
  cppverify::post(cppverify::result > 0)
{
  return bad_callee(x);
}

int vac(int x)
  cppverify::pre(x > 0 && x < 0)
  cppverify::post(cppverify::result == 42)
{
  return 0;
}

[[cppverify::trusted]] int tr(int x)
  cppverify::post(cppverify::result > 100);

int uses_tr(int x)
  cppverify::post(cppverify::result > 100)
{
  return tr(x);
}

int loop_star(int n)
  cppverify::post(cppverify::result == 7)
{
  while (true)
    cppverify::invariant(true)
    cppverify::decreases(*)
  {
    if (n == 3)
      return 7;
  }
}

// SOURCE-DAG: error: verification failed: bad_callee
// SOURCE-DAG: Unresolved: caller [backend=z3] [reason=callee.contract]
// SOURCE-DAG: Verified: vac [backend=z3] [vacuous]
// SOURCE-DAG: Verified: uses_tr [backend=z3] [trusts=tr]
// SOURCE-DAG: Verified: loop_star [backend=z3] [partial]

// REPLAY-DAG: error: verification failed: bad_callee
// REPLAY-DAG: Proved obligations: caller (dependencies not checked in replay) [backend=z3]
// REPLAY-DAG: Proved obligations: vac (dependencies not checked in replay) [backend=z3]
// REPLAY-DAG: Proved obligations: uses_tr (dependencies not checked in replay) [backend=z3]
// REPLAY-DAG: Proved obligations: loop_star (dependencies not checked in replay) [backend=z3]

// JSON-DAG: "function":"bad_callee"{{.*}}"status":"failed"
// JSON-DAG: "function":"caller",{{.*}}"message":"dependencies not checked in replay"{{.*}}"status":"proved-obligations"
