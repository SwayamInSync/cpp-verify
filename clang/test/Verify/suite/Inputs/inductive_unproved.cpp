// Run with a solver budget too small for the rule proofs.
cppverify::spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

cppverify::spec bool reach(int a, int b) cppverify::inductive {
  return a == b || cppverify::exists(c, edge(a, c) && reach(c, b));
}
