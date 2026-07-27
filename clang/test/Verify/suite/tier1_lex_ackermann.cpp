// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-1: function-level lexicographic decreases on the textbook example. Each
// recursive call decreases (m, n) lexicographically: ack(m-1, _) drops the
// first component; ack(m, n-1) keeps m and drops n.
spec int ack(int m, int n)
  decreases(m, n)
{
  if (m <= 0) return n + 1;
  if (n < 0) return 0;
  if (n == 0) return ack(m - 1, 1);
  int inner = ack(m, n - 1);
  return ack(m - 1, inner < 0 ? 0 : inner);
}
// VERIFY: Verified: spec decreases: ack
