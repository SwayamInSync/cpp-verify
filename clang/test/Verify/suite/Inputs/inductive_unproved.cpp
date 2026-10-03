// Run with a solver budget too small for the rule proofs.
spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

spec bool reach(int a, int b) inductive {
  return a == b || exists(c, edge(a, c) && reach(c, b));
}
