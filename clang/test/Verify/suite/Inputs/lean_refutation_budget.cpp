// Refutations that are bounded, and refutations that are not reported, for
// lean_refutation.test.

// Lean decides a quantifier over a thousand integers by trying each one.
cppverify::proof void below_a_thousand()
  cppverify::post(cppverify::forall(i, 0, 1000, i < 999))
{
}

// It would decide this one by trying each of a billion integers, which the
// prelude does only for ranges of at most 4096: each integer is a level of
// recursion, whose memory heartbeats do not bound. The counterexample is not
// decided.
cppverify::proof void below_a_billion()
  cppverify::post(cppverify::forall(i, 0, 1000000000, i < 999999999))
{
}

// A counterexample checked with a postcondition that is not established is
// not a failure (spec.post), so nothing is reported of its refutation.
cppverify::spec bool ge(int n)
  cppverify::inductive
  cppverify::post(!cppverify::result || n > -1000)
{
  return n == 20 || ge(n + 1);
}

cppverify::proof void far()
  cppverify::post(ge(-5000))
{
}
