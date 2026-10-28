// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 --no-check-ub %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=NOUB
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=2 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
//
// A contract is C++ evaluated where the function is called and where it
// returns, so it must be defined there, as Dafny checks a method's
// well-formedness. Each precondition is checked where the ones before it
// hold; each postcondition in the state the function returns in, which for a
// function whose body is not verified is any state its frame allows. A
// clause that may be undefined fails as `contract of f` at its operation, and
// a caller that relies on that contract is not verified.

using cppverify::valid;

struct Ring {
  int buf[8];
  int head;
};

// Each kind of definedness, in a precondition.
int ratio(int a, int b)
  cppverify::pre(a / b == 0)
{
  return 0;
}
// CHECK: [[@LINE-4]]:20: error: verification failed: contract of ratio [division-by-zero]
// CHECK: note: counterexample: b = 0
// CHECK: Verified: ratio [backend=z3]
// BMC: error: verification failed: contract of ratio [division-by-zero]
// NOUB: error: verification failed: contract of ratio [division-by-zero]

int ratio_ok(int a, int b)
  cppverify::pre(b != 0 && a / b == 0)
{
  return 0;
}
// CHECK-NOT: contract of ratio_ok
// CHECK: Verified: ratio_ok [backend=z3]

int deref(const int *p)
  cppverify::pre(*p > 0)
{
  return 0;
}
// CHECK: [[@LINE-4]]:18: error: verification failed: contract of deref [dereference]
// CHECK: note: counterexample: p = 0
// NOUB: error: verification failed: contract of deref [dereference]

int deref_ok(const int *p)
  cppverify::pre(p != nullptr && *p > 0)
{
  return 0;
}
// CHECK-NOT: contract of deref_ok
// CHECK: Verified: deref_ok [backend=z3]

int at(const int *p, int i)
  cppverify::pre(valid(p, 8) && p[i] == 3)
{
  return 0;
}
// CHECK: [[@LINE-4]]:33: error: verification failed: contract of at [bounds]
// NOUB: error: verification failed: contract of at [dereference]

int at_ok(const int *p, int i)
  cppverify::pre(valid(p, 8) && 0 <= i && i < 8 && p[i] == 3)
{
  return 0;
}
// CHECK-NOT: contract of at_ok
// CHECK: Verified: at_ok [backend=z3]

// A pointer without an extent addresses one object. Without memory checking
// (--no-check-ub) accesses are not checked against objects, in a contract as
// in a body, and an extent is not assumed: above, p may be null.
int second(const int *p)
  cppverify::pre(p != nullptr && p[1] == 0)
{
  return 0;
}
// CHECK: [[@LINE-4]]:34: error: verification failed: contract of second [bounds]
// NOUB-NOT: contract of second

int slot(const Ring *r, int i)
  cppverify::pre(r != nullptr && r->buf[i] == 0)
{
  return 0;
}
// CHECK: [[@LINE-4]]:31: error: verification failed: contract of slot [bounds]
// NOUB: error: verification failed: contract of slot [bounds]

constexpr bool positive(int v) { return v > 0; }

int next_positive(int x)
  cppverify::pre(positive(x + 1))
{
  return 0;
}
// CHECK: [[@LINE-4]]:29: error: verification failed: contract of next_positive [overflow]
// CHECK: note: counterexample: x = 2147483647

constexpr int share(int v) { return 100 / v; }

// An operation inside a lifted helper is reported at the helper's call.
int shared(int x)
  cppverify::pre(share(x) > 0)
{
  return 0;
}
// CHECK: [[@LINE-4]]:18: error: verification failed: contract of shared [division-by-zero]
// CHECK: note: counterexample: x = 0

// Order: a clause, an operand of && or ||, a branch of ?:, and a quantifier's
// body are evaluated where what comes before them holds.
int ordered(int a, int b)
  cppverify::pre(b != 0)
  cppverify::pre(a / b == 0)
{
  return 0;
}
// CHECK-NOT: contract of ordered
// CHECK: Verified: ordered [backend=z3]

int reversed(int a, int b)
  cppverify::pre(a / b == 0)
  cppverify::pre(b != 0)
{
  return 0;
}
// CHECK: [[@LINE-5]]:20: error: verification failed: contract of reversed [division-by-zero]
// CHECK: note: counterexample: b = 0

int either(int a, int b)
  cppverify::pre(b == 0 || a / b > 0)
{
  return 0;
}
// CHECK-NOT: contract of either

int choice(const int *p, int i)
  cppverify::pre(valid(p, 4) && (0 <= i && i < 4 ? p[i] > 0 : i == 9))
{
  return 0;
}
// CHECK-NOT: contract of choice

int all_positive(const int *a, int n)
  cppverify::pre(valid(a, n) && cppverify::forall(k, 0, n, a[k] > 0))
{
  return 0;
}
// CHECK-NOT: contract of all_positive

int one_more(const int *a, int n)
  cppverify::pre(valid(a, n) && n >= 1 &&
                 cppverify::forall(k, 0, n + 1, a[k] > 0))
{
  return 0;
}
// CHECK: [[@LINE-4]]:18: error: verification failed: contract of one_more [bounds]

int sign(int x)
  cppverify::behavior(positive, x > 0)
    cppverify::pre(100 / x > 0)
  cppverify::behavior(other, x <= 0)
    cppverify::pre(x > -10)
{
  return 0;
}
// CHECK-NOT: contract of sign
// CHECK: Verified: sign [backend=z3]

// A postcondition is checked in the state the body returns in, where the
// postconditions before it hold.
int read_ahead(const int *p, int i)
  cppverify::pre(valid(p, 8) && 0 <= i && i < 8)
  cppverify::post(cppverify::result == p[i + 1])
{
  return p[i];
}
// CHECK: [[@LINE-4]]:37: error: verification failed: read_ahead [bounds]
// BMC: error: verification failed: read_ahead [bounds]

int one(int x)
  cppverify::post(cppverify::result != 0)
  cppverify::post(10 / cppverify::result == 10)
{
  return 1;
}
// CHECK: Verified: one [backend=z3]

int zero(int x)
  cppverify::post(cppverify::result != 0)
  cppverify::post(10 / cppverify::result == 10)
{
  return 0;
}
// CHECK: [[@LINE-5]]:37: error: verification failed: zero [postcondition]
// CHECK-NOT: division-by-zero

// A loop invariant and an assertion read memory as the body does.
int walk(const int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n <= 100)
  cppverify::pre(cppverify::forall(k, 0, n, p[k] >= 0))
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n && p[i] >= 0)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return 0;
}
// CHECK: [[@LINE-7]]:46: error: verification failed: walk [bounds]

int last(const int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n <= 100)
  cppverify::pre(cppverify::forall(k, 0, n, p[k] >= 0))
{
  cppverify::check(p[n] >= 0);
  return 0;
}
// CHECK: [[@LINE-3]]:20: error: verification failed: last [bounds]
// BMC: error: verification failed: last [bounds]

int ghost_last(const int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n <= 100)
{
  cppverify::ghost { cppverify::check(p[n] >= 0 || p[n] < 0); }
  return 0;
}
// CHECK: [[@LINE-3]]:39: error: verification failed: ghost_last [bounds]

// The postcondition before it holds, and the body's own state places the
// result: *result lies in p.
int *second_of(int *p)
  cppverify::pre(valid(p, 4))
  cppverify::post(cppverify::result == p + 1)
  cppverify::post(*cppverify::result == p[1])
{
  return p + 1;
}
// CHECK: Verified: second_of [backend=z3]

// A read under old is checked in the entry state, where p[0] is the index the
// precondition bounds, not the 100 the body stores.
int take(int *p)
  cppverify::pre(valid(p, 4) && 1 <= p[0] && p[0] < 4)
  cppverify::modifies(p[0])
  cppverify::post(cppverify::result == cppverify::old(p[p[0]]))
{
  int v = p[p[0]];
  p[0] = 100;
  return v;
}
// CHECK: Verified: take [backend=z3]
// BMC: Verified: take [backend=bmc

// A parameter in a postcondition is its entry value, whatever the body
// assigns to its copy.
int advance(const int *p)
  cppverify::pre(valid(p, 2))
  cppverify::post(cppverify::result == p[1])
{
  p = p + 1;
  return *p;
}
// CHECK: Verified: advance [backend=z3]

// p[2] is q[0], but read through p it lies outside p's object, which is what
// the clause is checked against, whatever the body assigns to p.
int next_object(const int *p, const int *q)
  cppverify::pre(valid(p, 2) && valid(q, 2) && q == p + 2)
  cppverify::post(cppverify::result == p[2])
{
  p = p + 1;
  return q[0];
}
// CHECK: [[@LINE-5]]:37: error: verification failed: next_object [bounds]

int prev_object(const int *p, const int *q)
  cppverify::pre(valid(p, 2) && valid(q, 2) && q == p + 2 && p[2] == 0)
{
  p = p + 1;
  return 0;
}
// CHECK: [[@LINE-5]]:55: error: verification failed: contract of prev_object [bounds]

// A trusted contract holds in every state its frame allows, with any result.
[[cppverify::trusted]] int inverse(int x)
  cppverify::post(10 / cppverify::result > 0);
// CHECK: Trusted: inverse (contract assumed, not verified)
// CHECK-NEXT: [[@LINE-2]]:22: error: verification failed: contract of inverse [division-by-zero]
// CHECK: note: counterexample: result = 0

[[cppverify::trusted]] int nonzero(int x)
  cppverify::post(cppverify::result != 0)
  cppverify::post(10 / cppverify::result >= -10);
// CHECK: Trusted: nonzero (contract assumed, not verified)
// CHECK-NOT: contract of nonzero

[[cppverify::trusted]] int *find(int *p, int x)
  cppverify::pre(valid(p, 4))
  cppverify::post(cppverify::result == nullptr || *cppverify::result == x);
// CHECK: Trusted: find (contract assumed, not verified)
// CHECK-NOT: contract of find

[[cppverify::trusted]] int *find_any(int *p, int x)
  cppverify::pre(valid(p, 4))
  cppverify::post(*cppverify::result == x);
// CHECK: [[@LINE-1]]:19: error: verification failed: contract of find_any [dereference]

// What the frame does not name keeps its value: *q stays nonzero.
[[cppverify::trusted]] void scale(int *p, const int *q)
  cppverify::pre(p != nullptr && q != nullptr && *q != 0)
  cppverify::modifies(*p)
  cppverify::post(*p == cppverify::old(*p) + 10 / *q);
// CHECK: Trusted: scale (contract assumed, not verified)
// CHECK-NOT: contract of scale

[[cppverify::trusted]] void scale_both(int *p, int *q)
  cppverify::pre(p != nullptr && q != nullptr && *q != 0)
  cppverify::modifies(*p, *q)
  cppverify::post(*p == cppverify::old(*p) + 10 / *q);
// CHECK: [[@LINE-1]]:49: error: verification failed: contract of scale_both [division-by-zero]

// A contract without a definition is checked too.
int past(const int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1)
  cppverify::post(cppverify::result == p[n]);
// CHECK: warning: past has a contract but no definition
// CHECK: [[@LINE-2]]:40: error: verification failed: contract of past [bounds]

// A trusted contract whose extent marker cannot be read establishes nothing.
[[cppverify::trusted]] int either_end(const int *p, int n)
  cppverify::pre(n == 0 || valid(p, n));
// CHECK: Trusted: either_end (contract assumed, not verified)
// CHECK-NEXT: error: either_end: valid marker must be a positive top-level conjunction clause

int use_end(const int *p)
  cppverify::pre(valid(p, 2))
{
  int r = either_end(p, 2);
  return r;
}
// CHECK: Unresolved: use_end [backend=z3] [reason=callee.contract] (relies on the contract of either_end (its clauses are not shown to be defined), which is not established)

// A caller relies on the contract it calls, which a contract that may be
// undefined does not establish.
int use_inverse(int x)
  cppverify::post(cppverify::result > 0)
{
  int r = inverse(x);
  return 10 / r;
}
// CHECK: Unresolved: use_inverse [backend=z3] [reason=callee.contract] (relies on the contract of inverse (its clauses are not shown to be defined), which is not established)

int use_nonzero(int x)
  cppverify::post(cppverify::result != 0)
{
  int r = nonzero(x);
  return r;
}
// CHECK: Verified: use_nonzero [backend=z3] [trusts=nonzero]

int use_ratio(int b)
  cppverify::pre(b != 0)
{
  int r = ratio(0, b);
  return r;
}
// CHECK: Unresolved: use_ratio [backend=z3] [reason=callee.contract] (relies on the contract of ratio (its clauses are not shown to be defined), which is not established)

// A proof function's contract is checked against its extents.
cppverify::proof void lemma(const int *a, int n)
  cppverify::pre(valid(a, n) && n >= 1 && a[n] == 0)
{
}
// CHECK: [[@LINE-3]]:43: error: verification failed: contract of lemma [bounds]
// CHECK: Verified: lemma [backend=z3]

// A spec is total: division by zero is zero there, and it has no
// precondition to check.
cppverify::spec int quotient(int a, int b) { return a / b; }

int halves(int a)
  cppverify::pre(quotient(a, 0) == 0)
{
  return 0;
}
// CHECK-NOT: contract of halves
// CHECK: Verified: halves [backend=z3]

// A spec is total, as in Verus: applied in a postcondition it reads memory
// without a check, even a cell outside p.
cppverify::spec int cell(const int *p, int i) { return p[i]; }

[[cppverify::trusted]] int far(const int *p)
  cppverify::pre(valid(p, 4))
  cppverify::post(cppverify::result == cell(p, 7));
// CHECK: Trusted: far (contract assumed, not verified)
// CHECK-NOT: contract of far

int far_copy(const int *p)
  cppverify::pre(valid(p, 4))
  cppverify::post(cppverify::result == cell(p, 7))
{
  int r = far(p);
  return r;
}
// CHECK: Verified: far_copy [backend=z3] [trusts=far]

// A contract is established by its function's proof and by the check that it
// is defined, so that check takes part in the cycle rule. The check of
// cycled's contract needs sum_up's postcondition, whose proof calls cycled.
cppverify::spec int sum_up(int n);

[[cppverify::trusted]] cppverify::proof void cycled(int n)
  cppverify::pre(n >= 0 && 10 / (sum_up(n) + 1) >= 0);
// CHECK: Trusted: cycled (contract assumed, not verified)
// CHECK-NEXT: Unresolved: contract of cycled [backend=z3] [reason=proof.cycle]

cppverify::spec int sum_up(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0) by { if (n > 0) cycled(n - 1); }
{
  return n <= 0 ? 0 : sum_up(n - 1) + n;
}
// CHECK: Unresolved: spec decreases and post: sum_up [reason=proof.cycle]

// With measures every use between them lowers, they form a cluster: the
// check uses sum_down(n) at (n, 1), below (n, 2), and the proof block calls
// measured at (n - 1, 2), below (n, 1).
cppverify::spec int sum_down(int n);

[[cppverify::trusted]] cppverify::proof void measured(int n)
  cppverify::pre(n >= 0 && 10 / (sum_down(n) + 1) >= 0)
  cppverify::decreases(n, 2);
// CHECK: Trusted: measured (contract assumed, not verified)
// CHECK-NOT: contract of measured

cppverify::spec int sum_down(int n)
  cppverify::decreases(n, 1)
  cppverify::post(cppverify::result >= 0) by { if (n > 0) measured(n - 1); }
{
  return n <= 0 ? 0 : sum_down(n - 1) + n;
}
// CHECK: Verified: spec decreases and post: sum_down
