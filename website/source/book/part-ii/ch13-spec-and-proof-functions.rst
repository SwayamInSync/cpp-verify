Chapter 13 — Spec and proof functions
=====================================

**Spec** functions (mathematical)
---------------------------------

.. cppverify-example: label fibo

.. code-block:: cpp

   cv::spec int fibo(int n)
     cv::decreases(n)
   {
     if (n <= 1) return n;
     return fibo(n - 1) + fibo(n - 2);
   }

Use in contracts:

.. cppverify-example: with fibo

.. code-block:: cpp

   int client(int n)
     cv::pre(n >= 0 && n <= 40)
     cv::post(cv::result == fibo(n));

``fibo`` is not compiled. Integers are **mathematical** (unbounded) inside ``cppverify::spec``.
Because it has no compiled form, a spec can be called only from contracts, ghost
code, and other spec or proof functions; ``return fibo(n);`` in an executable
body is a compile error. In ghost or proof code, ``int f = fibo(n);`` converts
the unbounded value to ``int``, and the verifier checks that it fits.

**Proof** functions (lemmas)
----------------------------

.. cppverify-example: with fibo

.. code-block:: cpp

   cv::proof void fibo_nonneg(int n)
     cv::pre(n >= 0)
     cv::post(fibo(n) >= 0)
     cv::decreases(n)
   {
     if (n >= 2) {
       fibo_nonneg(n - 1);
       fibo_nonneg(n - 2);
     }
   }

   cv::proof void lemma(int i, int j)
     cv::pre(i <= j)
     cv::post(fibo(i) <= fibo(j))
     cv::decreases(j - i)
   {
     if (i < j) {
       lemma(i, j - 1);        // fibo(i) <= fibo(j - 1)
       if (j >= 2)
         fibo_nonneg(j - 2);   // so fibo(j - 1) <= fibo(j)
     }
   }

A lemma's body is its proof: each call is the induction hypothesis at a
smaller measure, or another lemma. Call lemmas from ``cppverify::ghost { ... }`` blocks
in executable functions.

Proof functions are isolated from runtime state: they may update local proof
variables, but cannot write pointees/globals or call executable functions.
Every proof-only loop needs ``cppverify::decreases``. The same erased-state rules apply to
inline ``cppverify::ghost`` blocks, which also cannot return from their executable
enclosing function.

Soft preconditions (``cppverify::recommends``)
----------------------------------------------

A ``cppverify::spec`` function stays **total**, but ``cppverify::recommends`` flags likely misuse. It generates no
call-site obligation; the verifier only **warns** when a call may violate it:

.. code-block:: cpp

   cv::spec int safe_div(int a, int b)
     cv::recommends(b != 0)
   { return a / b; }

Opacity: fuel, ``cppverify::reveal``, ``cppverify::hide``
---------------------------------------------------------

A recursive ``cppverify::spec`` is finitely transparent by default (fuel 1), so its
defining equation cannot send Z3 into a matching loop.
``cppverify::reveal_with_fuel(f, n)`` raises the depth when a proof needs more (the
``safe_fib`` walkthrough uses it). ``cppverify::reveal`` / ``cppverify::hide`` toggle a spec's
transparency for the rest of a function:

.. code-block:: cpp

   cv::spec int triple(int x) { return 3 * x; }

   int f(int x)
     cv::pre(x >= 0 && x <= 10)
     cv::post(cv::result == triple(x))
   {
     cv::ghost { cv::reveal(triple); }            // reveal_with_fuel(f, n) for recursive specs
     return x + x + x;
   }

   int g(int x)
     cv::pre(x >= 0 && x <= 10)
     cv::post(cv::result == x + x + x)
   {
     cv::ghost { cv::hide(triple); }              // keep triple opaque; prove without unfolding it
     return x + x + x;
   }

Use the smallest fuel that exposes the recurrence needed at the current proof
site. If a proof function has already supplied a finite table or step lemma,
``cppverify::hide(f)`` can suppress irrelevant recursive equations while the imported
postconditions remain available. Hiding a spec keeps its definition out of
proofs, never out of the program's meaning: a counterexample must still fail
under the real definition, and an obligation that only the hidden definition
would settle is reported as ``spec.hidden``. The full-range factorial and Fibonacci
acceptance tests use this pattern to retain exact mathematical specifications
without making solver time depend on unnecessary unfolding.

See also :doc:`ch17-backends-modular-calls`.

Termination of recursive specs
------------------------------

A recursive ``cppverify::spec`` needs ``cppverify::decreases``, and every recursive call must lower
the measure: a single measure must stay nonnegative and strictly decrease; for
a tuple, the first component that changes must stay nonnegative and decrease.
A spec's definition becomes a fact only once the spec is known to terminate,
so the termination proof cannot use it. Each recursive call must decrease the
measure whatever the spec's other calls return:

.. cppverify-example: unresolved nested

.. code-block:: cpp

   cv::spec int ack(int m, int n)
     cv::decreases(m, n)                     // verified: m decides the outer call
   {
     return m <= 0 ? n + 1
          : n <= 0 ? ack(m - 1, 1)
          : ack(m - 1, ack(m, n - 1));
   }

   cv::spec int nested(int n)
     cv::decreases(n)                        // unresolved: needs nested(n - 1) < n,
   {                                     // a fact about nested itself
     return n <= 0 ? 0 : 1 + nested(nested(n - 1));
   }

A recursive call inside ``cppverify::forall`` or ``cppverify::exists`` must decrease the measure
for every value of the bound variable. Spec functions may call each other in a
cycle when they share a measure of the same length and every call within the
cycle lowers it; the termination proof treats all of them as opaque:

.. code-block:: cpp

   cv::spec bool is_odd(int n);
   cv::spec bool is_even(int n) cv::decreases(n) { return n <= 0 ? n == 0 : is_odd(n - 1); }
   cv::spec bool is_odd(int n)  cv::decreases(n) { return n <= 0 ? false : is_even(n - 1); }

A spec whose termination is not established has no definition, so a proof
that relies on it is reported as not verified with reason
``spec.termination`` rather than as verified.

Proof and executable functions may also call each other in a cycle under the
same rule, with calls inside the cycle reasoned about through the callees'
contracts.

A spec takes no ``cppverify::pre``, ``cppverify::modifies``, or ``cppverify::aliases``: it is defined for every
argument, and ``cppverify::recommends`` states its intended domain.

A spec's ``cppverify::post`` is a property of its value at every argument, proved
together with its termination by well-founded induction on the measure: a
recursive call may assume the post only where its measure is lower than the
caller's. That is what lets a nested call terminate:

.. code-block:: cpp

   cv::spec int g(int n)
     cv::decreases(n)
     cv::post(cv::result >= 0 && cv::result <= (n < 0 ? 0 : n))
   {
     return n <= 0 ? 0 : g(g(n - 1));   // g(n - 1) < n by the post
   }

   cv::spec int m91(int n)                  // McCarthy's 91 function
     cv::decreases(n > 100 ? 0 : 101 - n)
     cv::post(n > 100 ? cv::result == n - 10 : cv::result == 91)
   {
     return n > 100 ? n - 10 : m91(m91(n + 11));
   }

Every application of the spec then carries its post, so ``m91(n) == 91``
for ``n <= 100`` needs no unfolding. A post that fails is reported; a proof
that relied on it is reported with reason ``spec.post``, or
``spec.termination`` for a recursive spec, whose termination may have used
it. A non-recursive spec is unfolded at its calls, so its post matters where
it is hidden.

A post holds at the applications a proof names and also at those inside the
unfoldings it receives, as Dafny's function postconditions do. With the post
on the spec, the monotonicity lemma above needs no separate lemma for
nonnegativity: ``fib(j - 1) <= fib(j)`` needs ``fib(j - 2) >= 0``, and only
the unfolding of ``fib(j)`` names ``fib(j - 2)``.

.. code-block:: cpp

   cv::spec int fib(int n)
     cv::decreases(n)
     cv::post(cv::result >= 0)
   {
     return n <= 0 ? 0 : n == 1 ? 1 : fib(n - 2) + fib(n - 1);
   }

   cv::proof void fib_monotone(int i, int j)
     cv::pre(i <= j)
     cv::post(fib(i) <= fib(j))
     cv::decreases(j - i)
   {
     if (i < j)
       fib_monotone(i, j - 1);
   }

``cppverify::when(c)`` restricts a spec's definition to the domain ``c``. Termination is
checked under ``c`` only, and outside it the spec's value is unspecified:
nothing about it can be proved, and a counterexample that depends on it is
reported as ``counterexample.unchecked``. A post is required, and assumed,
only within the domain:

.. code-block:: cpp

   cv::spec int log2(int n)
     cv::when(n >= 1)
     cv::decreases(n)
     cv::post(cv::result >= 0 && cv::result < n)
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
- **Bounded domains.** For ``cppverify::pre(n >= 0 && n <= 200)``, the solver first proves
  the domain bounded, then receives the definitions across it and checks every
  value. Domains of up to about a thousand values are settled this way.
- **Counterexamples.** A failure is reported only after the counterexample is
  checked against the true definitions, so it never relies on a value the
  solver invented for an unfolded call.
- **Inductions.** When no finite unfolding settles a goal, the verifier tries
  to prove it by induction on its own (below).
- **Counterexamples too large to compute.** When a counterexample needs a
  spec value too large to compute, the verifier tries to confirm it by a
  proof at that input (below).

Automatic induction
~~~~~~~~~~~~~~~~~~~

Unfolding a recursive spec a few levels settles claims about a few values.
A claim about every ``n``, such as ``fibo(n) >= n - 1`` for all ``n >= 3``,
needs induction: show it at ``n`` assuming it at smaller values. When
unfolding leaves a claim unresolved (``spec.fuel``), the verifier tries
inductions by itself before reporting it:

- **Following a recursive spec** that the claim applies (shown as
  ``following fibo``): the claim is assumed at every value smaller in the
  spec's ``cppverify::decreases`` measure, and in particular at the values the spec's own
  recursion visits. ``fibo(n)`` calls ``fibo(n - 1)`` and ``fibo(n - 2)``, so
  the claim is assumed at ``n - 1`` and ``n - 2``. The values are found by
  walking the definition: through the other specs of a mutual recursion, and
  for a call inside ``cppverify::forall`` or ``cppverify::exists``, at every value the quantifier
  ranges over.
- **On an integer variable** (shown as ``on n``): strong induction, the claim
  assumed at every smaller nonnegative value of ``n``.

Everything else stays fixed, and the assumption is the claim exactly as the
function states it, so these never prove a false claim: the measure cannot
decrease forever, which is what the ``cppverify::decreases`` check of each spec shows.
Only proofs are taken from these attempts. None of the lemmas below needs a
body:

.. code-block:: cpp

   cv::spec int fibo(int n)
     cv::decreases(n)
     cv::post(cv::result >= 0)
   {
     if (n <= 0) return 0;
     if (n == 1) return 1;
     return fibo(n - 2) + fibo(n - 1);
   }

   // The claim at n - 1 and n - 2, as fibo recurses.
   cv::proof void grows(int n)
     cv::pre(n >= 3)
     cv::post(fibo(n) >= n - 1)
   {
   }

   cv::spec int total(seq s)
     cv::decreases(s.len())
   {
     return s.len() <= 0 ? 0 : total(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
   }

   // The claim at the shorter sequence total recurses on.
   cv::proof void total_nonneg(seq s)
     cv::pre(cv::forall(k, 0, s.len(), s[k] >= 0))
     cv::post(total(s) >= 0)
   {
   }

   // Mutual recursion: even reaches even(n - 2) through odd.
   cv::spec bool odd(int n);
   cv::spec bool even(int n) cv::decreases(n) { return n <= 0 ? true : odd(n - 1); }
   cv::spec bool odd(int n) cv::decreases(n) { return n <= 0 ? false : even(n - 1); }

   cv::proof void even_mod(int n)
     cv::pre(n >= 0)
     cv::post(even(n) == (n % 2 == 0))
   {
   }

   // A call under forall: the claim at every k the forall ranges over.
   cv::spec bool good(int n) cv::decreases(n) { return n <= 0 || cv::forall(k, 0, n, good(k)); }

   cv::proof void all_good(int n)
     cv::post(good(n))
   {
   }

.. code-block:: text

   Verified: grows [backend=z3] [by induction following fibo]
   Verified: total_nonneg [backend=z3] [by induction following total]
   Verified: even_mod [backend=z3] [by induction following even]
   Verified: all_good [backend=z3] [by induction following good]

The suffix ``[by induction following fibo]`` says which induction proved
the claim (JSON ``"induction": "following fibo"``). Assignments in a body are
substituted first, so ``return n * (n + 1);`` with
``cppverify::post(cppverify::result == 2 * sum(n))`` is proved the same way.

Inductions cost time only where a claim would otherwise stay unresolved:
verified and failed claims never try one. Each attempt gets a sixth of
``--timeout``, but at least two seconds (all of ``--timeout`` when that is
shorter, and five seconds when there is no timeout), and the attempts for
one claim stop after two such shares. With the default 30-second timeout an
unresolved claim takes at most 10 seconds more.

**When no induction finds the proof.** The automatic inductions assume the
claim itself. When the recursion changes another argument, the claim at the
smaller value is not the statement the step needs:

.. cppverify-example: unresolved accumulated

.. code-block:: cpp

   cv::spec int accumulate(int n, int acc)
     cv::decreases(n)
   {
     return n <= 0 ? acc : accumulate(n - 1, acc + n);
   }

   cv::spec int sum(int n) cv::decreases(n) { return n <= 0 ? 0 : n + sum(n - 1); }

   cv::proof void accumulated(int n)
     cv::pre(n >= 0 && n <= 25000)
     cv::post(accumulate(n, 0) == sum(n))
   {
   }

.. code-block:: text

   Unresolved: accumulated [backend=z3] [reason=spec.fuel] (proof obligation ...: every counterexample found needs accumulate, sum unfolded at ever larger arguments (the last one needed 21887 unfoldings), so no finite unfolding settles it; prove it by induction in a proof function whose decreases clause shrinks on each recursive call, and call that lemma here; induction following accumulate and induction following sum and induction on n did not prove it; a proof by induction following sum could start from the body 'if (n > 0 && n - 1 >= 0 && n - 1 <= 25000) { accumulated(n - 1); }', with decreases(n))

The message says, in order:

1. what the solver tried: every counterexample it proposed needed the specs
   at ever larger arguments, so no amount of unfolding settles the claim;
2. which inductions the verifier tried, none of which proved it;
3. a body to start a proof by induction from: a call of the function itself
   at each value the recursion reaches, under the condition that reaches it
   and the function's precondition there, with the ``cppverify::decreases`` clause to
   add.

Here the suggested body does not work as it stands: ``accumulate(n, 0)``
continues as ``accumulate(n - 1, n)``, so the claim at ``n - 1``, which is
about ``accumulate(n - 1, 0)``, does not help. The step needs a stronger
statement, about every ``acc``. Prove that as a lemma whose ``cppverify::decreases``
clause shrinks on each recursive call, and call it:

.. code-block:: cpp

   cv::spec int accumulate(int n, int acc)
     cv::decreases(n)
   {
     return n <= 0 ? acc : accumulate(n - 1, acc + n);
   }

   cv::spec int sum(int n) cv::decreases(n) { return n <= 0 ? 0 : n + sum(n - 1); }

   cv::proof void accumulate_adds(int n, long long acc)
     cv::pre(n >= 0 && acc >= 0 && acc + n * n <= 1000000000000)
     cv::post(accumulate(n, acc) == acc + sum(n))
     cv::decreases(n)
   {
     if (n > 0)
       accumulate_adds(n - 1, acc + n);   // the claim at n - 1, for another acc
   }

   cv::proof void accumulated(int n)
     cv::pre(n >= 0 && n <= 25000)
     cv::post(accumulate(n, 0) == sum(n))
   {
     accumulate_adds(n, 0);
   }

.. code-block:: text

   Verified: accumulate_adds [backend=z3]
   Verified: accumulated [backend=z3]

The recursive call is legal only at a smaller measure, and its postcondition
is the induction hypothesis. A proof function computes with machine
integers, so ``acc + n`` is checked for overflow; the precondition bounds it.
Executable code calls a lemma from a ``cppverify::ghost`` block, and a
``cppverify::check`` is proved where it stands and assumed afterwards, so a
chain of assertions in a ghost block works as a step-by-step proof:

.. cppverify-example: fragment

.. code-block:: cpp

   void check(int n)
     cv::pre(n >= 0 && n <= 25000)
   {
     cv::ghost {
       accumulate_adds(n, 0);
       cv::check(accumulate(n, 0) == sum(n));
     }
   }

Counterexamples too large to compute
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A failure is reported only after its counterexample is checked against the
true definitions of the specs, so that it never rests on a value the solver
made up. Checking means computing the specs at the counterexample's input,
and some values are too large for that: ``pow2(1000000000)`` has a billion
bits, and ``fibo(1000000000)`` takes a billion steps. The verifier then tries
to prove, at that input, that the claim fails. With the input fixed, it may
use only facts that are proved: the postconditions of specs, and the
contracts of ``cppverify::proof`` functions whose own verification succeeded. If the
solver proves it, the counterexample is confirmed:

.. cppverify-example: fails small_power

.. code-block:: cpp

   cv::spec int pow2(int n)
     cv::decreases(n)
     cv::post(cv::result >= n + 1)
   {
     return n <= 0 ? 1 : 2 * pow2(n - 1);
   }

   // pow2(n) >= n + 1 > 1000, at inputs of a billion and more.
   cv::proof void small_power(int n)
     cv::pre(n >= 1000000000)
     cv::post(pow2(n) < 1000)
   {
   }

.. code-block:: text

   error: verification failed: small_power (counterexample: n = 1000023594; confirmed by a proof at this input, since its check could not compute pow2(1000023594)) [backend=z3] [reason=counterexample]

The failure rests on the facts the proof used (here ``pow2``'s
postcondition); if one of them is not established, the verdict is not a
failure. When no proved fact settles the claim, the verifier cannot tell a
false claim from a true one that needs a proof, and says both:

.. cppverify-example: unresolved fibo_small

.. code-block:: cpp

   cv::spec int fibo(int n)
     cv::decreases(n)
     cv::post(cv::result >= 0)
   {
     if (n <= 0) return 0;
     if (n == 1) return 1;
     return fibo(n - 2) + fibo(n - 1);
   }

   cv::proof void fibo_small(int n)
     cv::pre(n >= 1000000000)
     cv::post(fibo(n) < 5)
   {
   }

.. code-block:: text

   Unresolved: fibo_small [backend=z3] [reason=spec.fuel] (proof obligation ...: Z3 proposed n = 1000000000 as a counterexample, but checking it needs fibo(1000000000) (the evaluation nesting limit was reached while evaluating fibo), and no proved fact settles it: either the claim is false there, or it is true and needs a proof by induction; induction following fibo and induction on n did not prove it; a proof by induction following fibo could start from the body 'if (n > 0 && n != 1 && n - 2 >= 1000000000 && n - 1 >= 1000000000) { fibo_small(n - 2); fibo_small(n - 1); }', with decreases(n))

Which to do depends on what you believe:

- the claim is true: prove it by induction, starting from the body the
  message shows;
- the claim is false: state the fact that refutes it as a lemma. Here
  ``fibo(n) >= 5`` for ``n >= 5``, proved by induction, makes the
  counterexample confirmed:

.. cppverify-example: fails fibo_small

.. code-block:: cpp

   cv::spec int fibo(int n)
     cv::decreases(n)
     cv::post(cv::result >= 0)
   {
     if (n <= 0) return 0;
     if (n == 1) return 1;
     return fibo(n - 2) + fibo(n - 1);
   }

   cv::proof void fibo_at_least_5(int n)
     cv::pre(n >= 5)
     cv::post(fibo(n) >= 5)
     cv::decreases(n)
   {
     if (n >= 6)
       fibo_at_least_5(n - 1);
   }

   cv::proof void fibo_small(int n)
     cv::pre(n >= 1000000000)
     cv::post(fibo(n) < 5)
   {
   }

.. code-block:: text

   Verified: fibo_at_least_5 [backend=z3]
   error: verification failed: fibo_small (counterexample: n = 1000000000; confirmed by a proof at this input that uses the contract of fibo_at_least_5, since its check could not compute fibo(1000000000)) [backend=z3] [reason=counterexample]

The proof instantiates a lemma where its postcondition speaks of the same
spec application as the claim, here ``fibo_at_least_5`` at
``n = 1000000000``. What it instantiates is what the lemma's verification
proved: its postconditions wherever every assumption its proof started from
holds. These are its preconditions and the ones the verifier adds for its
parameters: a pointer is null or points to valid storage, ``valid(p, n)``
means ``n >= 0`` and ``n`` valid objects, mutable pointers address distinct
objects, and a record parameter satisfies its type invariant. A lemma is
therefore never used where an assumption its proof relied on fails. A
parameter the match leaves open, such as a pointer the conclusion does not
mention, can take any value, so the lemma applies wherever some value meets
those assumptions. A lemma over memory is used the same way:

.. cppverify-example: fails total_negative

.. code-block:: cpp

   cv::spec int total(const int *a, int n)
     cv::reads(a, n)
     cv::decreases(n)
   {
     return n <= 0 ? 0 : total(a, n - 1) + a[n - 1];
   }

   cv::proof void total_nonneg(const int *a, int n)
     cv::pre(valid(a, n) && cv::forall(k, 0, n, a[k] >= 0))
     cv::post(total(a, n) >= 0)
     cv::decreases(n)
   {
     if (n > 0)
       total_nonneg(a, n - 1);
   }

   cv::proof void total_negative(const int *a, int n)
     cv::pre(valid(a, n) && n >= 1000000000)
     cv::pre(cv::forall(k, 0, n, a[k] >= 0))
     cv::post(total(a, n) < 0)
   {
   }

.. code-block:: text

   Verified: total_nonneg [backend=z3]
   error: verification failed: total_negative (counterexample: n = 1000000000, a = 1; confirmed by a proof at this input that uses the contract of total_nonneg, since its check could not compute total(1, 1000000000)) [backend=z3] [reason=counterexample]

Only contracts that are established count: a confirmation runs after every
function is verified, and a lemma that failed, or that rests on a fact that
is not established, is not used. Each confirmation gets one attempt's share
of the time, and only verdicts that would otherwise stay unresolved try one.
In JSON, an unresolved verdict gives the proposed input and the value it
could not compute as ``unchecked_counterexample``, and a confirmed failure
lists the lemmas it used as ``confirmed_with``.

A spec's own ``cppverify::post``, ``cppverify::decreases``, and ``cppverify::reads`` clauses are checked
without a function body to put a lemma call in. A proof block after the
clause gives them one. ``mul`` below is multiplication by repeated
addition; its commutativity needs ``mul(a, b) == a * b`` at both orders,
an induction the verifier does not find by itself:

.. code-block:: cpp

   cv::spec int mul(int a, int b) cv::decreases(b) { return b <= 0 ? 0 : mul(a, b - 1) + a; }

   cv::proof void mul_is(int a, int b)
     cv::post(b < 0 || mul(a, b) == a * b)
     cv::decreases(b)
   {
     if (b > 0)
       mul_is(a, b - 1);
   }

   cv::spec int area(int a, int b)
     cv::post(a < 0 || b < 0 || cv::result == mul(b, a)) by { mul_is(a, b); mul_is(b, a); }
   {
     return mul(a, b);
   }

Without the block, ``spec post: area`` is unresolved (``spec.fuel``); with
it, it is verified. In the block, ``cppverify::result`` is the value the body returns,
and naming the spec at a smaller measure uses the induction hypothesis
there. ``cppverify::decreases(...) by { ... }`` helps a termination proof the same
way, and ``cppverify::reads(p, n) by { ... }`` a frame. The block of an inductive
predicate's postcondition is its induction step.

A block may also call a lemma about the spec itself. The two proofs then
rest on each other, which is sound only as an induction: they form a
cluster, as in Dafny, and must share ``cppverify::decreases`` clauses of one length.
Every call between them lowers the measure, and the lemma sees the spec's
definition and postcondition only where the spec's measure is below its
own. Lexicographic measures put the spec just below the lemma at the same
argument:

.. code-block:: cpp

   cv::proof void total_nonneg(int n);

   cv::spec int total(int n)
     cv::decreases(n, 0)
     cv::post(cv::result >= 0) by { if (n > 0) total_nonneg(n - 1); }
   {
     return n <= 0 ? 0 : total(n - 1) + n;
   }

   cv::proof void total_nonneg(int n)
     cv::decreases(n, 1)
     cv::post(total(n) >= 0)
   {
     if (n > 0)
       total_nonneg(n - 1);
   }

.. code-block:: text

   Verified: spec decreases and post: total
   Verified: total_nonneg [backend=z3]

The lemma unfolds ``total(n)``, since ``(n, 0)`` is below ``(n, 1)``; the
block calls the lemma at ``n - 1``, since ``(n - 1, 1)`` is below
``(n, 0)``. A lemma that would use the spec at the same measure gets
nothing from it, and a block call that does not lower the measure fails
like a non-terminating call. Without shared measures, two proofs that rest
on each other are reported with reason ``proof.cycle``.

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
the spec. ``cppverify::reads(p, n)`` declares the cells ``p[0..n)`` the spec depends on,
and every write outside them then leaves the spec unchanged:

.. code-block:: cpp

   cv::spec int sum(const int *p, int n)
     cv::reads(p, n)
     cv::decreases(n)
   {
     return n <= 0 ? 0 : sum(p, n - 1) + p[n - 1];
   }

   void append(int *p, int n)
     cv::pre(n >= 0 && n <= 100 && valid(p, n + 1))
     cv::modifies(p[n])
     cv::post(sum(p, n) == cv::old(sum(p, n)))   // verified: p[n] is outside p[0..n)
   {
     p[n] = 7;
   }

The clause is checked against the body: every load, under the conditions
that reach it, and every range that a heap-reading callee reads must lie in
the declared cells, so a spec may call another heap-reading spec only if that
spec has a ``cppverify::reads`` clause too. A wrong clause fails with a counterexample,
and a proof that used its frames is reported with reason ``spec.reads``. The
range is a pointer and an element count fixed by the arguments; it cannot
depend on the heap. Several ``cppverify::reads`` clauses declare the union of their
ranges.

Structured proofs: ``by`` and ``cppverify::calc``
-------------------------------------------------

A lemma call in a ghost block adds its postcondition to everything after it.
``cppverify::check(c) by { ... }`` keeps a proof local instead: the block may
call lemmas, assert intermediate facts, and declare locals, and only ``c``
holds afterwards, as with Verus's and Dafny's ``assert ... by``:

.. cppverify-example: label sq

.. code-block:: cpp

   cv::spec int sq(int x) { return x * x; }

   cv::proof void sq_monotone(int a, int b)
     cv::pre(0 <= a && a <= b)
     cv::post(sq(a) <= sq(b))
   {
   }

   int bigger(int a, int b)
     cv::pre(0 <= a && a <= b && b <= 1000)
     cv::post(cv::result == 1)
   {
     cv::check(sq(a) <= sq(b)) by {
       sq_monotone(a, b);
     }
     return 1;
   }

A lemma's precondition is checked where the proof calls it. When the claim
is a ``cppverify::forall``, the block proves it for one arbitrary value of the bound
variable, which it can name (Verus's ``assert forall ... by``):

.. code-block:: cpp

   cv::proof void pair_ordered(const int *a, int n, int i, int j)
     cv::pre(valid(a, n) && n <= 1000 && 0 <= i && i <= j && j < n)
     cv::pre(cv::forall(k, 0, n - 1, a[k] <= a[k + 1]))
     cv::post(a[i] <= a[j])
     cv::decreases(j - i)
   {
     if (i < j)
       pair_ordered(a, n, i, j - 1);
   }

   cv::proof void below_last(const int *a, int n)
     cv::pre(valid(a, n) && n >= 1 && n <= 1000)
     cv::pre(cv::forall(k, 0, n - 1, a[k] <= a[k + 1]))
     cv::post(cv::forall(k, 0, n, a[k] <= a[n - 1]))
   {
     cv::check(cv::forall(k, 0, n, a[k] <= a[n - 1])) by {
       pair_ordered(a, n, k, n - 1);
     }
   }

Inside the block ``k`` lies in ``[0, n)`` and cannot be assigned; a lemma
call there is an instance for that ``k``, and since ``k`` is arbitrary the
whole ``cppverify::forall`` follows. ``cppverify::calc`` chains
such steps, each with an optional proof block, and concludes the relation
between its first and last terms: ``==`` when every step is ``==``, ``<`` (or
``>``) when some step is strict, otherwise ``<=`` (or ``>=``):

.. cppverify-example: with sq

.. code-block:: cpp

   void chain(int a, int b, int c)
     cv::pre(0 <= a && a <= b && b <= c && c <= 1000)
   {
     cv::calc {
       sq(a);
       <= { sq_monotone(a, b); }
       sq(b);
       <= { sq_monotone(b, c); }
       sq(c);
       == c * c;
     }
     cv::check(sq(a) <= c * c);
   }

Quantifiers over all integers
-----------------------------

``cppverify::forall(k, body)`` and ``cppverify::exists(k, body)`` range over all mathematical
integers. They state lemmas without an artificial range and let a caller
instantiate them anywhere:

.. cppverify-example: with sq

.. code-block:: cpp

   cv::proof void sq_nonnegative_all()
     cv::post(cv::forall(k, sq(k) >= 0))
   {
   }

   void uses_lemma(int a)
   {
     cv::ghost { sq_nonnegative_all(); }
     cv::check(sq(a + 7) >= 0);
   }

A counterexample to an unbounded quantifier is certified exactly when its
body depends on the bound variable through memory reads, collection reads,
and comparisons: the body is then constant beyond finitely many values, which
the checker evaluates. Otherwise the result is ``counterexample.unchecked``.

Triggers
--------

The solver uses a quantified fact by instantiating it at terms that match a
*pattern*. Usually it picks the patterns itself; ``cppverify::trigger(term)`` inside the
body chooses one, as Verus's ``#[trigger]`` does:

.. code-block:: cpp

   void positive(const int *a, int n)
     cv::pre(valid(a, n) && n >= 1 && n <= 1000)
     cv::pre(cv::forall(k, 0, n, cv::trigger(a[k]) > 0))
   {
     cv::check(a[n - 1] > 0);
   }

A trigger must be a memory read, a collection read, or a call of a recursive
spec, and must mention a quantified variable; any other mark draws a warning
and is ignored. A trigger whose instances create new matching terms (for
example ``cppverify::trigger(g(k))`` with a fact about ``g(k + 1)``) makes a *matching
loop*, and the query times out. ``--profile-quantifiers`` reports how often
each quantifier of an unresolved query was instantiated, which points at the
culprit (see :doc:`ch16-when-verification-fails`).

``cppverify::choose``
---------------------

``cppverify::choose(k, body)`` is an integer for which ``body`` holds, when there is one,
and otherwise some unspecified integer (Hilbert's ε). ``choose(k, lo, hi,
body)`` chooses in ``[lo, hi)``:

.. code-block:: cpp

   cv::spec int index_of(const int *a, int n, int x)
   {
     return cv::choose(k, 0, n, a[k] == x);
   }

   void found(const int *a, int n, int x)
     cv::pre(valid(a, n) && n >= 1 && n <= 1000)
     cv::pre(cv::exists(k, 0, n, a[k] == x))
   {
     cv::check(0 <= index_of(a, n, x) && index_of(a, n, x) < n);
     cv::check(a[index_of(a, n, x)] == x);
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
     cv::pre(valid(a, n) && n >= 0 && n <= 1000)
     cv::post(0 <= cv::result && cv::result <= n)
   {
     cv::ghost seq seen = cppverify::seq_empty();
     int c = 0;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && 0 <= c && c <= i)
       cv::invariant(seen.len() == i)
       cv::invariant(cv::forall(k, 0, i, seen[k] == a[k]))
       cv::decreases(n - i)
     {
       if (a[i] > 0)
         c = c + 1;
       cv::ghost { seen = seen.push(a[i]); }
     }
     return c;
   }

Spec functions over collections recurse on their size:

.. code-block:: cpp

   cv::spec int sum(seq s)
     cv::decreases(s.len())
   {
     return s.len() <= 0 ? 0 : sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
   }

   cv::proof void sum_push(seq s, int x)
     cv::post(sum(s.push(x)) == sum(s) + x)
   {
   }

A sequence has ``len()``, ``s[i]``, ``push(x)``, ``update(i, x)``,
``reverse()``, ``subrange(lo, hi)``, ``s + t``, and ``contains(x)``.
``update`` and ``reverse`` are themselves spec functions of
``<cppverify.h>``, defined by the other operations; ``reverse`` comes with
its length, ``s.reverse().len() == s.len()``, and other facts about it are
proved by induction (see :doc:`ch20-mathematics-to-code`).

A set has ``insert``, ``remove``, ``contains``, ``unite``, ``intersect``,
``difference``, and ``subset_of``; a multiset counts its elements; a map
has ``insert(k, v)``, ``remove(k)``, ``contains(k)``, and ``m[k]``. Values
compare with ``==`` and ``!=``. Facts about them are proved like any other:

.. code-block:: cpp

   cv::proof void set_facts(set s, int x, int y)
     cv::pre(x != y)
     cv::post(s.insert(x).contains(x))
     cv::post(s.insert(x).remove(y).contains(x))
     cv::post(s.subset_of(s.unite(set_empty().insert(y))))
     cv::post(!s.difference(s).contains(x))
   {
   }

   cv::proof void multiset_facts(multiset m, int x, int y)
     cv::pre(x != y)
     cv::post(m.insert(x).count(x) == m.count(x) + 1)
     cv::post(m.insert(x).count(y) == m.count(y))
     cv::post(m.insert(x).remove(x) == m)
   {
   }

   cv::proof void map_facts(map m, int k, int v, int j)
     cv::pre(j != k)
     cv::post(m.insert(k, v)[k] == v && m.insert(k, v).contains(k))
     cv::post(m.insert(k, v)[j] == m[j])
     cv::post(!m.remove(k).contains(k))
   {
   }

A ghost multiset can stand for the elements a loop has passed, so an
invariant can say what a counter counts:

.. code-block:: cpp

   int count_of(const int *a, int n, int x)
     cv::pre(valid(a, n) && n >= 0 && n <= 1000)
     cv::post(0 <= cv::result && cv::result <= n)
   {
     cv::ghost multiset bag = multiset_empty();
     int c = 0;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && 0 <= c && c <= i)
       cv::invariant(c == bag.count(x))
       cv::decreases(n - i)
     {
       if (a[i] == x)
         c = c + 1;
       cv::ghost { bag = bag.insert(a[i]); }
     }
     return c;
   }

Every operation is total: an index outside ``[0, len())`` reads 0, an update
there changes nothing, ``subrange`` clamps its bounds, and a key outside a
map's domain maps to 0. Sequences are finite; sets, multisets, and maps range
over all integers and may be infinite. Counterexamples show their values, such
as ``s = [4, 3]`` or ``m = {1 -> 7, 4.. -> 2}``. Z3 and cvc5 decide all
four; Lean support for them is planned for a future release.

Inductive predicates
--------------------

Some predicates have no measure: whether ``b`` can be reached from ``a`` by
steps ``x -> x + 1`` and ``x -> 2 * x`` is a question about paths, not about a
smaller argument. ``cppverify::inductive`` makes a ``cppverify::spec`` returning ``bool`` the
*least* predicate its body defines (Dafny's ``least predicate``): true exactly
where a finite derivation shows it.

.. cppverify-example: label reach

.. code-block:: cpp

   cv::spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

   cv::spec bool reach(int a, int b)
     cv::inductive
     cv::post(!cv::result || a < 0 || a <= b)
   {
     return a == b || cv::exists(c, edge(a, c) && reach(c, b));
   }

   cv::proof void three_reaches_twelve()
     cv::post(reach(3, 12))
   {
     cv::check(reach(12, 12));
     cv::check(reach(6, 12));
   }

   cv::proof void no_way_back(int a, int b)
     cv::pre(a >= 0 && b < a)
     cv::post(!reach(a, b))
   {
   }

   cv::proof void wrong_way(int a, int b)
     cv::pre(a >= 0 && reach(a, b))
     cv::post(a < b)
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

How deep a proof sees ``reach`` depends on what it needs, and the verifier
works most of it out itself. With constant arguments the counterexample
check computes the predicate: ``reach(3, 12)`` holds by the derivation
``3 -> 6 -> 12``, and the solver receives the unfoldings along it, so the
proof needs no body. When a verdict still depends on the predicate, the
verifier unfolds the applications inside the unfoldings too, one level more
at a time, up to four levels; ``cppverify::reveal_with_fuel(reach, n)`` asks for ``n``
levels from the start.

.. cppverify-example: with reach

.. code-block:: cpp

   cv::proof void three_reaches_twelve_again() cv::post(reach(3, 12)) {}

   cv::proof void doubles(int b)
     cv::pre(b >= 1)
     cv::post(reach(b, 2 * b + 1))
   {
   }

   cv::proof void far(int b)
     cv::pre(b == 64)
     cv::post(reach(1, b))
   {
     cv::ghost { cv::reveal_with_fuel(reach, 7); }
   }

.. code-block:: text

   Verified: three_reaches_twelve_again [backend=z3]
   Verified: doubles [backend=z3]
   Verified: far [backend=z3]

Each level is an unfolding the verifier proved, so a proof found this way
stands, and a false claim still fails with a checked counterexample. Some
claims no unfolding settles. Where the derivations from an argument go
round a cycle, the predicate is false there, but every unfolding holds just
as well of a predicate that is true on the cycle. The verdict says so
(``spec.fuel``: ``every counterexample found needs ... to hold, but no
derivation shows it``), the verifier does not unfold further, and a
postcondition or a lemma proved by induction supplies the missing step.

A counterexample is checked against what the predicate really means, true
or false. Where its derivations from an argument reach finitely many
arguments, the checker computes it over all of them: every value starts
false and becomes true once the body holds, until nothing changes. Where
they reach infinitely many, ``reach(a, b)`` true is shown by a derivation,
and false by the postcondition: ``reach(5, 3)`` cannot hold because
``5 <= 3`` does not.

The predicate may occur in its body only positively (as a conjunct, a
disjunct, a branch, or under ``cppverify::exists`` or a bounded ``cppverify::forall``), which makes
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

   cv::spec bool ev(int n);
   cv::spec bool od(int n) cv::inductive { return n == 1 || ev(n - 1); }
   cv::spec bool ev(int n) cv::inductive { return n == 0 || od(n - 1); }

   struct node { int value; node *next; };

   // q is reached from p by following next.
   cv::spec bool segment(const node *p, const node *q) cv::inductive {
     return p == q || (p != nullptr && segment(p->next, q));
   }

A postcondition may mention the predicate itself. Transitivity is one: a
derivation of ``reach(a, b)`` extends every path from ``b``:

.. code-block:: cpp

   cv::spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

   cv::spec bool reach(int a, int b);
   cv::spec bool reach(int a, int b)
     cv::inductive
     cv::post(!cv::result || cv::forall(c, !reach(b, c) || reach(a, c)))
   {
     return a == b || cv::exists(c, edge(a, c) && reach(c, b));
   }

   cv::proof void chain(int a, int b, int c)
     cv::pre(reach(a, b) && reach(b, c))
     cv::post(reach(a, c))
   {
   }

In the induction, the premise ``reach(c, b)`` already extends every path
from ``b`` (the induction hypothesis), and ``reach(a, c2)`` follows from
``edge(a, c)`` and ``reach(c, c2)`` by the predicate's proved unfolding. The
postcondition itself is never assumed while it is being proved, so a false
one such as ``cppverify::post(!cppverify::result || !reach(a, b))`` is never proved: it fails, with
a derivation of height 1 where ``a == b``. (The forward declaration lets the
postcondition name the predicate.)

``constexpr`` as spec
---------------------

Any ``constexpr`` function is usable in ``cppverify::pre``/``cppverify::post`` **directly** — no separate ``cppverify::spec``
re-declaration:

.. code-block:: cpp

   constexpr int square(int x) { return x * x; }

   int area(int side)
     cv::pre(side >= 0 && side <= 1000)
     cv::post(cv::result == square(side))
   { return side * side; }

One body does double duty: the same ``constexpr`` runs at execution time and defines the spec, so
the two can never silently diverge (Verus requires a separate ``spec fn``). A lifted ``constexpr``
keeps **machine** integer semantics — honest overflow — unlike an explicit ``cppverify::spec`` (mathematical
``Int``); see :doc:`../../language/integers`.
