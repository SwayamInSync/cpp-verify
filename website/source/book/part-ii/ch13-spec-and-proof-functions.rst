Chapter 13 — Spec and proof functions
=====================================

**Spec** functions (mathematical)
---------------------------------

.. code-block:: cpp

   spec int fibo(int n)
     decreases(n)
   {
     if (n <= 1) return n;
     return fibo(n - 1) + fibo(n - 2);
   }

Use in contracts:

.. code-block:: cpp

   int client(int n)
     pre(n >= 0 && n <= 40)
     post(result == fibo(n));

``fibo`` is not compiled. Integers are **mathematical** (unbounded) inside ``spec``.
Because it has no compiled form, a spec can be called only from contracts, ghost
code, and other spec or proof functions; ``return fibo(n);`` in an executable
body is a compile error. In ghost or proof code, ``int f = fibo(n);`` converts
the unbounded value to ``int``, and the verifier checks that it fits.

**Proof** functions (lemmas)
----------------------------

.. code-block:: cpp

   proof void lemma(int i, int j)
     pre(i <= j)
     post(fibo(i) <= fibo(j))
     decreases(j - i)
   { /* ghost proof */ }

Call from ``ghost { ... }`` blocks in executable functions.

Proof functions are isolated from runtime state: they may update local proof
variables, but cannot write pointees/globals or call executable functions.
Every proof-only loop needs ``decreases``. The same erased-state rules apply to
inline ``ghost`` blocks, which also cannot return from their executable
enclosing function.

Soft preconditions (``recommends``)
-----------------------------------

A ``spec`` function stays **total**, but ``recommends`` flags likely misuse. It generates no
call-site obligation; the verifier only **warns** when a call may violate it:

.. code-block:: cpp

   spec int safe_div(int a, int b)
     recommends(b != 0)
   { return a / b; }

Opacity: fuel, ``reveal``, ``hide``
-----------------------------------

A recursive ``spec`` is finitely transparent by default (fuel 1), so its
defining equation cannot send Z3 into a matching loop.
``reveal_with_fuel(f, n)`` raises the depth when a proof needs more (the
``safe_fib`` walkthrough uses it). ``reveal`` / ``hide`` toggle a spec's
transparency for the rest of a function:

.. code-block:: cpp

   spec int triple(int x) { return 3 * x; }

   int f(int x)
     pre(x >= 0 && x <= 10)
     post(result == triple(x))
   {
     ghost { reveal(triple); }            // reveal_with_fuel(f, n) for recursive specs
     return x + x + x;
   }

   int g(int x)
     pre(x >= 0 && x <= 10)
     post(result == x + x + x)
   {
     ghost { hide(triple); }              // keep triple opaque; prove without unfolding it
     return x + x + x;
   }

Use the smallest fuel that exposes the recurrence needed at the current proof
site. If a proof function has already supplied a finite table or step lemma,
``hide(f)`` can suppress irrelevant recursive equations while the imported
postconditions remain available. Hiding a spec keeps its definition out of
proofs, never out of the program's meaning: a counterexample must still fail
under the real definition, and an obligation that only the hidden definition
would settle is reported as ``spec.hidden``. The full-range factorial and Fibonacci
acceptance tests use this pattern to retain exact mathematical specifications
without making solver time depend on unnecessary unfolding.

See also :doc:`ch17-backends-modular-calls`.

Termination of recursive specs
------------------------------

A recursive ``spec`` needs ``decreases``, and every recursive call must lower
the measure: a single measure must stay nonnegative and strictly decrease; for
a tuple, the first component that changes must stay nonnegative and decrease.
A spec's definition becomes a fact only once the spec is known to terminate,
so the termination proof cannot use it. Each recursive call must decrease the
measure whatever the spec's other calls return:

.. code-block:: cpp

   spec int ack(int m, int n)
     decreases(m, n)                     // verified: m decides the outer call
   {
     return m <= 0 ? n + 1
          : n <= 0 ? ack(m - 1, 1)
          : ack(m - 1, ack(m, n - 1));
   }

   spec int nested(int n)
     decreases(n)                        // unresolved: needs nested(n - 1) < n,
   {                                     // a fact about nested itself
     return n <= 0 ? 0 : 1 + nested(nested(n - 1));
   }

A recursive call inside ``forall`` or ``exists`` must decrease the measure
for every value of the bound variable. Spec functions may call each other in a
cycle when they share a measure of the same length and every call within the
cycle lowers it; the termination proof treats all of them as opaque:

.. code-block:: cpp

   spec bool is_odd(int n);
   spec bool is_even(int n) decreases(n) { return n <= 0 ? n == 0 : is_odd(n - 1); }
   spec bool is_odd(int n)  decreases(n) { return n <= 0 ? false : is_even(n - 1); }

A spec whose termination is not established has no definition, so a proof
that relies on it is reported as not verified with reason
``spec.termination`` rather than as verified.

Proof and executable functions may also call each other in a cycle under the
same rule, with calls inside the cycle reasoned about through the callees'
contracts.

A spec takes no ``pre``, ``modifies``, or ``aliases``: it is defined for every
argument, and ``recommends`` states its intended domain.

A spec's ``post`` is a property of its value at every argument, proved
together with its termination by well-founded induction on the measure: a
recursive call may assume the post only where its measure is lower than the
caller's. That is what lets a nested call terminate:

.. code-block:: cpp

   spec int g(int n)
     decreases(n)
     post(result >= 0 && result <= (n < 0 ? 0 : n))
   {
     return n <= 0 ? 0 : g(g(n - 1));   // g(n - 1) < n by the post
   }

   spec int m91(int n)                  // McCarthy's 91 function
     decreases(n > 100 ? 0 : 101 - n)
     post(n > 100 ? result == n - 10 : result == 91)
   {
     return n > 100 ? n - 10 : m91(m91(n + 11));
   }

Every application of the spec then carries its post, so ``m91(n) == 91``
for ``n <= 100`` needs no unfolding. A post that fails is reported; a proof
that relied on it is reported with reason ``spec.post``, or
``spec.termination`` for a recursive spec, whose termination may have used
it. A non-recursive spec is unfolded at its calls, so its post matters where
it is hidden.

``when(c)`` restricts a spec's definition to the domain ``c``. Termination is
checked under ``c`` only, and outside it the spec's value is unspecified:
nothing about it can be proved, and a counterexample that depends on it is
reported as ``counterexample.unchecked``. A post is required, and assumed,
only within the domain:

.. code-block:: cpp

   spec int log2(int n)
     when(n >= 1)
     decreases(n)
     post(result >= 0 && result < n)
   {
     return n == 1 ? 0 : 1 + log2(n / 2);   // no base case needed for n <= 0
   }

Proving properties of recursive specs
-------------------------------------

The verifier gives the solver each spec's defining equation at the call sites
in a function, unfolded as deep as the fuel allows. Beyond that, it settles
four kinds of goal without help:

- **Closed applications** such as ``sum(15000) == 112507500`` or
  ``fib(90) == ...`` are computed: the solver receives the defining equation
  at every argument the evaluation reaches, up to 20000 of them.
- **Bounded domains.** For ``pre(n >= 0 && n <= 200)``, the solver first proves
  the domain bounded, then receives the definitions across it and checks every
  value. Domains of up to about a thousand values are settled this way.
- **Counterexamples.** A failure is reported only after the counterexample is
  checked against the true definitions, so it never relies on a value the
  solver invented for an unfolded call.
- **Inductions.** When no finite unfolding settles a goal, the verifier tries
  strong induction on an integer variable that the recursive calls depend on:
  it proves the goal assuming it holds at every smaller nonnegative value of
  that variable, with everything else fixed. A least counterexample would
  satisfy that assumption, so this never proves a false goal; below zero the
  assumption is empty, and those values are proved directly. Assignments are
  substituted first, so ``return n * (n + 1);`` with
  ``post(result == 2 * sum(n))`` is proved this way, and a lemma such as
  ``2 * sum(n) == n * (n + 1)`` needs no body.

The automatic induction keeps every other variable fixed and assumes nothing
but the goal itself. When the recursion changes another argument, or the step
needs a stronger statement than the goal, the verifier reports ``spec.fuel``
and says so. State the induction as a ``proof`` function whose ``decreases``
clause shrinks on each recursive call, and call the lemma where the fact is
needed:

.. code-block:: cpp

   spec int sum(int n) decreases(n) { return n <= 0 ? 0 : n + sum(n - 1); }

   spec int accumulate(int n, int acc) decreases(n) {
     return n <= 0 ? acc : accumulate(n - 1, acc + n);
   }

   proof void accumulate_sum(int n, int acc)
     pre(n >= 0 && n <= 25000 && acc >= 0 && acc <= 1000000000 - 40000 * n)
     post(accumulate(n, acc) == acc + sum(n))
     decreases(n)
   {
     if (n > 0)
       accumulate_sum(n - 1, acc + n);   // the hypothesis at another acc
   }

   void check(int n)
     pre(n >= 0 && n <= 25000)
   {
     ghost {
       accumulate_sum(n, 0);
       contract_assert(accumulate(n, 0) == sum(n));
     }
   }

The recursive call is legal only at a smaller measure, and its postcondition
is the induction hypothesis. Machine arithmetic in the lemma is checked for
overflow and reasoned about exactly. A ``contract_assert`` is proved where it
stands and assumed afterwards, so a chain of assertions in a ghost block
works as a step-by-step proof.

A spec's own ``post``, ``decreases``, and ``reads`` clauses are checked
without a function body to put a lemma call in. A proof block after the
clause gives them one. ``mul`` below is multiplication by repeated
addition; its commutativity needs ``mul(a, b) == a * b`` at both orders,
an induction the verifier does not find by itself:

.. code-block:: cpp

   spec int mul(int a, int b) decreases(b) { return b <= 0 ? 0 : mul(a, b - 1) + a; }

   proof void mul_is(int a, int b)
     post(b < 0 || mul(a, b) == a * b)
     decreases(b)
   {
     if (b > 0)
       mul_is(a, b - 1);
   }

   spec int area(int a, int b)
     post(a < 0 || b < 0 || result == mul(b, a)) by { mul_is(a, b); mul_is(b, a); }
   {
     return mul(a, b);
   }

Without the block, ``spec post: area`` is unresolved (``spec.fuel``); with
it, it is verified. In the block, ``result`` is the value the body returns,
and naming the spec at a smaller measure uses the induction hypothesis
there. ``decreases(...) by { ... }`` helps a termination proof the same
way, and ``reads(p, n) by { ... }`` a frame. The block of an inductive
predicate's postcondition is its induction step. A lemma the block calls
must not itself be proved from the spec's postcondition: the two proofs
would only support each other, and both are reported with reason
``proof.cycle``.

Use Z3, the default backend, for recursive specs. cvc5 checks its
counterexamples against the same definitions but has no recursive definitions,
does not cover bounded domains, computes deep closed applications much more
slowly, and settles fewer lemmas and inductions with nonlinear machine
arithmetic, so more such goals stay unresolved there.
The strict portfolio is unresolved whenever cvc5 is.

Frames of heap-reading specs
----------------------------

A spec that reads through a pointer is evaluated in the heap state of each
call. After a write, the solver knows the value of the written cell but not
that a recursive spec over other cells is unchanged: that is an induction over
the spec. ``reads(p, n)`` declares the cells ``p[0..n)`` the spec depends on,
and every write outside them then leaves the spec unchanged:

.. code-block:: cpp

   spec int sum(const int *p, int n)
     reads(p, n)
     decreases(n)
   {
     return n <= 0 ? 0 : sum(p, n - 1) + p[n - 1];
   }

   void append(int *p, int n)
     pre(n >= 0 && n <= 100 && valid(p, n + 1))
     modifies(p[n])
     post(sum(p, n) == old(sum(p, n)))   // verified: p[n] is outside p[0..n)
   {
     p[n] = 7;
   }

The clause is checked against the body: every load, under the conditions
that reach it, and every range that a heap-reading callee reads must lie in
the declared cells, so a spec may call another heap-reading spec only if that
spec has a ``reads`` clause too. A wrong clause fails with a counterexample,
and a proof that used its frames is reported with reason ``spec.reads``. The
range is a pointer and an element count fixed by the arguments; it cannot
depend on the heap. Several ``reads`` clauses declare the union of their
ranges.

Structured proofs: ``by`` and ``calc``
--------------------------------------

A lemma call in a ghost block adds its postcondition to everything after it.
``contract_assert(c) by { ... }`` keeps a proof local instead: the block may
call lemmas, assert intermediate facts, and declare locals, and only ``c``
holds afterwards, as with Verus's and Dafny's ``assert ... by``:

.. code-block:: cpp

   spec int sq(int x) { return x * x; }

   proof void sq_monotone(int a, int b)
     pre(0 <= a && a <= b)
     post(sq(a) <= sq(b))
   {
   }

   int bigger(int a, int b)
     pre(0 <= a && a <= b && b <= 1000)
     post(result == 1)
   {
     contract_assert(sq(a) <= sq(b)) by {
       sq_monotone(a, b);
     }
     return 1;
   }

A lemma's precondition is checked where the proof calls it. When the claim
is a ``forall``, the block proves it for one arbitrary value of the bound
variable, which it can name (Verus's ``assert forall ... by``):

.. code-block:: cpp

   proof void pair_ordered(const int *a, int n, int i, int j)
     pre(valid(a, n) && n <= 1000 && 0 <= i && i <= j && j < n)
     pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
     post(a[i] <= a[j])
     decreases(j - i)
   {
     if (i < j)
       pair_ordered(a, n, i, j - 1);
   }

   proof void below_last(const int *a, int n)
     pre(valid(a, n) && n >= 1 && n <= 1000)
     pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
     post(forall(k, 0, n, a[k] <= a[n - 1]))
   {
     contract_assert(forall(k, 0, n, a[k] <= a[n - 1])) by {
       pair_ordered(a, n, k, n - 1);
     }
   }

Inside the block ``k`` lies in ``[0, n)`` and cannot be assigned; a lemma
call there is an instance for that ``k``, and since ``k`` is arbitrary the
whole ``forall`` follows. ``calc`` chains
such steps, each with an optional proof block, and concludes the relation
between its first and last terms: ``==`` when every step is ``==``, ``<`` (or
``>``) when some step is strict, otherwise ``<=`` (or ``>=``):

.. code-block:: cpp

   void chain(int a, int b, int c)
     pre(0 <= a && a <= b && b <= c && c <= 1000)
   {
     calc {
       sq(a);
       <= { sq_monotone(a, b); }
       sq(b);
       <= { sq_monotone(b, c); }
       sq(c);
       == c * c;
     }
     contract_assert(sq(a) <= c * c);
   }

Quantifiers over all integers
-----------------------------

``forall(k, body)`` and ``exists(k, body)`` range over all mathematical
integers. They state lemmas without an artificial range and let a caller
instantiate them anywhere:

.. code-block:: cpp

   proof void sq_nonnegative_all()
     post(forall(k, sq(k) >= 0))
   {
   }

   void uses_lemma(int a)
   {
     ghost { sq_nonnegative_all(); }
     contract_assert(sq(a + 7) >= 0);
   }

A counterexample to an unbounded quantifier is certified exactly when its
body depends on the bound variable through memory reads, collection reads,
and comparisons: the body is then constant beyond finitely many values, which
the checker evaluates. Otherwise the result is ``counterexample.unchecked``.

Triggers
--------

The solver uses a quantified fact by instantiating it at terms that match a
*pattern*. Usually it picks the patterns itself; ``trigger(term)`` inside the
body chooses one, as Verus's ``#[trigger]`` does:

.. code-block:: cpp

   void positive(const int *a, int n)
     pre(valid(a, n) && n >= 1 && n <= 1000)
     pre(forall(k, 0, n, trigger(a[k]) > 0))
   {
     contract_assert(a[n - 1] > 0);
   }

A trigger must be a memory read, a collection read, or a call of a recursive
spec, and must mention a quantified variable; any other mark draws a warning
and is ignored. A trigger whose instances create new matching terms (for
example ``trigger(g(k))`` with a fact about ``g(k + 1)``) makes a *matching
loop*, and the query times out. ``--profile-quantifiers`` reports how often
each quantifier of an unresolved query was instantiated, which points at the
culprit (see :doc:`ch16-when-verification-fails`).

``choose``
----------

``choose(k, body)`` is an integer for which ``body`` holds, when there is one,
and otherwise some unspecified integer (Hilbert's ε). ``choose(k, lo, hi,
body)`` chooses in ``[lo, hi)``:

.. code-block:: cpp

   spec int index_of(const int *a, int n, int x)
   {
     return choose(k, 0, n, a[k] == x);
   }

   void found(const int *a, int n, int x)
     pre(valid(a, n) && n >= 1 && n <= 1000)
     pre(exists(k, 0, n, a[k] == x))
   {
     contract_assert(0 <= index_of(a, n, x) && index_of(a, n, x) < n);
     contract_assert(a[index_of(a, n, x)] == x);
   }

A choice is a function of the values its body mentions, so it is the same
for the same values, and that is all the verifier knows about it: a claim
that holds for some choices but not others fails with a checked
counterexample.

Spec collections
----------------

``<cppverify.h>`` provides ``cppverify::seq``, ``set``, ``multiset``, and
``map`` of mathematical integers, the counterparts of Verus's ``Seq``,
``Set``, ``Multiset``, and ``Map``. They exist only for verification: use
them in contracts, ghost code, and spec and proof functions. A ghost
sequence can record what a loop has seen:

.. code-block:: cpp

   #include <cppverify.h>
   using cppverify::seq;

   int count_positive(const int *a, int n)
     pre(valid(a, n) && n >= 0 && n <= 1000)
     post(0 <= result && result <= n)
   {
     ghost seq seen = cppverify::seq_empty();
     int c = 0;
     for (int i = 0; i < n; i = i + 1)
       invariant(0 <= i && i <= n && 0 <= c && c <= i)
       invariant(seen.len() == i)
       invariant(forall(k, 0, i, seen[k] == a[k]))
       decreases(n - i)
     {
       if (a[i] > 0)
         c = c + 1;
       ghost { seen = seen.push(a[i]); }
     }
     return c;
   }

Spec functions over collections recurse on their size:

.. code-block:: cpp

   spec int sum(seq s)
     decreases(s.len())
   {
     return s.len() <= 0 ? 0 : sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
   }

   proof void sum_push(seq s, int x)
     post(sum(s.push(x)) == sum(s) + x)
   {
   }

A sequence has ``len()``, ``s[i]``, ``push(x)``, ``update(i, x)``,
``reverse()``, ``subrange(lo, hi)``, ``s + t``, and ``contains(x)``.
``update`` and ``reverse`` are themselves spec functions of
``<cppverify.h>``, defined by the other operations; ``reverse`` comes with
its length, ``s.reverse().len() == s.len()``, and other facts about it are
proved by induction (see :doc:`ch20-mathematics-to-code`).

Every operation is total: an index outside ``[0, len())`` reads 0, an update
there changes nothing, ``subrange`` clamps its bounds, and a key outside a
map's domain maps to 0. Sequences are finite; sets, multisets, and maps range
over all integers and may be infinite. Counterexamples show their values, such
as ``s = [4, 3]`` or ``m = {1 -> 7, 4.. -> 2}``. Z3 and cvc5 decide all
four, and Lean none.

Inductive predicates
--------------------

Some predicates have no measure: whether ``b`` can be reached from ``a`` by
steps ``x -> x + 1`` and ``x -> 2 * x`` is a question about paths, not about a
smaller argument. ``inductive`` makes a ``spec`` returning ``bool`` the
*least* predicate its body defines (Dafny's ``least predicate``): true exactly
where a finite derivation shows it.

.. code-block:: cpp

   spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

   spec bool reach(int a, int b)
     inductive
     post(!result || a < 0 || a <= b)
   {
     return a == b || exists(c, edge(a, c) && reach(c, b));
   }

   proof void three_reaches_twelve()
     post(reach(3, 12))
   {
     contract_assert(reach(12, 12));
     contract_assert(reach(6, 12));
   }

   proof void no_way_back(int a, int b)
     pre(a >= 0 && b < a)
     post(!reach(a, b))
   {
   }

   proof void wrong_way(int a, int b)
     pre(a >= 0 && reach(a, b))
     post(a < b)
   {
   }

.. code-block:: text

   Verified: spec axiom: edge
   Verified: inductive predicate: reach
   Verified: spec post: reach
   Verified: three_reaches_twelve [backend=z3]
   Verified: no_way_back [backend=z3]
   book.cpp:27:10: error: verification failed: wrong_way [...::postcondition@27:10]
     (counterexample: a [ssa=a_0] [type=i32] = 38, b [ssa=b_0] [type=i32] = 38)
     [backend=z3] [reason=counterexample]

A proof sees ``reach`` through its body, unfolded once at each application it
names: ``reach(6, 12)`` holds by the edge ``6 -> 12`` and ``reach(12, 12)``,
and ``reach(3, 12)`` by the edge ``3 -> 6``. The postcondition says what every
derivation satisfies; the verifier proves it by induction on derivations,
and ``no_way_back`` follows from it. ``wrong_way`` fails: ``reach(38, 38)``
holds with no step at all.

A counterexample is checked against what the predicate really means, true
or false. Where its derivations from an argument reach finitely many
arguments, the checker computes it over all of them: every value starts
false and becomes true once the body holds, until nothing changes. Where
they reach infinitely many, ``reach(a, b)`` true is shown by a derivation,
and false by the postcondition: ``reach(5, 3)`` cannot hold because
``5 <= 3`` does not.

The predicate may occur in its body only positively (as a conjunct, a
disjunct, a branch, or under ``exists`` or a bounded ``forall``), which makes
the least predicate exist and equal its body. That equality is what the
proofs above use, and it is proved, not assumed: for each predicate the
verifier generates proofs of three rules, by induction on the height of
derivations where needed, and ``Verified: inductive predicate: reach`` says
they hold. Monotonicity says that a derivation of some height is one of
every greater height; case analysis, that ``reach(a, b)`` implies its body;
introduction, that the body implies ``reach(a, b)``. If one fails, the
predicate and every proof that uses it are ``Unresolved`` with reason
``spec.inductive``. A postcondition that does not hold of every derivation
fails with ``spec post by induction failed`` and a counterexample giving the
height of a derivation.

Predicates that apply each other are defined together, and a predicate may
read memory:

.. code-block:: cpp

   spec bool ev(int n);
   spec bool od(int n) inductive { return n == 1 || ev(n - 1); }
   spec bool ev(int n) inductive { return n == 0 || od(n - 1); }

   struct node { int value; node *next; };

   // q is reached from p by following next.
   spec bool segment(const node *p, const node *q) inductive {
     return p == q || (p != nullptr && segment(p->next, q));
   }

A postcondition may mention the predicate itself. Transitivity is one: a
derivation of ``reach(a, b)`` extends every path from ``b``:

.. code-block:: cpp

   spec bool reach(int a, int b);
   spec bool reach(int a, int b)
     inductive
     post(!result || forall(c, !reach(b, c) || reach(a, c)))
   {
     return a == b || exists(c, edge(a, c) && reach(c, b));
   }

   proof void chain(int a, int b, int c)
     pre(reach(a, b) && reach(b, c))
     post(reach(a, c))
   {
   }

In the induction, the premise ``reach(c, b)`` already extends every path
from ``b`` (the induction hypothesis), and ``reach(a, c2)`` follows from
``edge(a, c)`` and ``reach(c, c2)`` by the predicate's proved unfolding. The
postcondition itself is never assumed while it is being proved, so a false
one such as ``post(!result || !reach(a, b))`` is never proved. (The forward
declaration lets the postcondition name the predicate.)

``constexpr`` as spec
---------------------

Any ``constexpr`` function is usable in ``pre``/``post`` **directly** — no separate ``spec``
re-declaration:

.. code-block:: cpp

   constexpr int square(int x) { return x * x; }

   int area(int side)
     pre(side >= 0 && side <= 1000)
     post(result == square(side))
   { return side * side; }

One body does double duty: the same ``constexpr`` runs at execution time and defines the spec, so
the two can never silently diverge (Verus requires a separate ``spec fn``). A lifted ``constexpr``
keeps **machine** integer semantics — honest overflow — unlike an explicit ``spec`` (mathematical
``Int``); see :doc:`../../language/integers`.
