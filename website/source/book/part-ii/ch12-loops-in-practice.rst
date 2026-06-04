Chapter 12 — Loops in practice
==============================

Map Part I’s invariant story to CppVerify syntax.

Example skeleton
----------------

.. code-block:: cpp

   while (i < n)
     invariant(0 <= i && i <= n)
     decreases(n - i)
   {
     // ...
     i++;
   }

Place ``invariant`` and ``decreases`` **after** the loop header’s closing ``)``.

What the verifier actually checks
---------------------------------

A loop is verified **modularly** — the verifier never unrolls it. Instead it
discharges three obligations from the invariant ``I`` and measure ``D``:

#. **Establishment.** ``I`` holds when the loop is first reached (from the
   concrete state just before the loop).
#. **Preservation.** Starting from an *arbitrary* state that satisfies
   ``I`` **and** the loop condition, one iteration of the body re-establishes
   ``I``. The state is arbitrary — the verifier forgets ("havocs") every
   variable the loop writes and assumes only ``I``. This is what makes the proof
   cover *all* iterations at once.
#. **Termination.** Under the same arbitrary state, the measure strictly
   decreases and stays non-negative: ``0 <= D_new < D_old``.

After the loop, the verifier continues with ``I && !cond`` — that, and nothing
else, is what it knows about the post-loop state. If you need a fact afterwards,
it has to be in the invariant.

Inductive invariants and machine integers
-----------------------------------------

Because preservation starts from an *arbitrary* ``I``-state, the invariant must
be **inductive**: strong enough to re-prove itself. The classic trap is an
unbounded accumulator under honest machine integers:

.. code-block:: cpp

   // REJECTED: s >= 0 is not inductive.
   int sum(int n) pre(n >= 0 && n <= 1000) post(result >= 0) {
     int s = 0, i = 0;
     while (i < n)
       invariant(i >= 0 && i <= n && s >= 0)   // too weak
       decreases(n - i)
     { s = s + 1; i = i + 1; }
     return s;
   }

From an arbitrary ``s`` satisfying ``s >= 0`` the verifier may pick
``s == INT_MAX``; then ``s + 1`` overflows to a negative number and ``s >= 0`` is
*not* preserved. CppVerify reasons about ``int`` as a real 32-bit type, so it
reports this — it is not a false alarm. The fix is to **bound the accumulator**
so it provably cannot overflow:

.. code-block:: cpp

   invariant(i >= 0 && i <= n && s == i)   // s tracks i, bounded by n -> inductive

``decreases`` is optional
-------------------------

Omit ``decreases`` and the verifier checks establishment and preservation only —
**partial correctness**. The loop is allowed to be one that you have not proven
terminates. Add ``decreases`` to also get a termination proof. (A lexicographic
tuple form ``decreases(a, b)`` is designed but not yet implemented; pass a single
measure.)

Loops after an early return
---------------------------

A loop that follows an early ``return`` verifies normally — its obligations are
only checked on the path that actually reaches it:

.. code-block:: cpp

   int f(int n) pre(n >= 0 && n <= 50) post(result >= 0) {
     if (n == 0) return 0;          // early exit
     int i = 0;
     while (i < n)
       invariant(0 <= i && i <= n)  // not checked on the n == 0 path
       decreases(n - i)
     { i = i + 1; }
     return i;
   }

Common failure modes
--------------------

.. list-table::
   :header-rows: 1
   :widths: 35 65

   * - Symptom
     - Likely fix
   * - Establishment fails
     - Weaken invariant or strengthen pre before loop
   * - Preservation fails
     - Strengthen invariant to include facts needed after body
   * - Termination fails
     - Fix ``decreases`` expression; show it decreases and stays nonnegative

``for`` loops use the same clause placement after the ``for (...)`` part.

Quantified properties
---------------------

A loop usually establishes a property over a *range*. Express that with the bounded quantifiers
``forall(i, lo, hi, e)`` and ``exists(i, lo, hi, e)`` — ``i`` ranges over ``[lo, hi)`` and the
half-open bound is the implicit trigger:

.. code-block:: cpp

   bool nonneg_prefix(int n)
     pre(n >= 0 && n <= 8)
     post(result == forall(i, 0, n, i >= 0))
   { return true; }

Quantifiers are valid anywhere a contract expression is — ``pre``, ``post``, ``invariant`` — which
is how a loop invariant talks about "everything processed so far". MVP supports **bounded**
quantifiers only.

Recursive spec functions in an invariant
----------------------------------------

A common pattern relates the accumulator to a recursive ``spec`` function — the
loop *computes* what the spec *defines*. The invariant ``acc == count(i - 1)``
below says "after processing ``i - 1`` elements, ``acc`` equals the spec's
value":

.. code-block:: cpp

   spec int count(int n)
     decreases(n)
   { if (n <= 0) return 0; return 1 + count(n - 1); }

   // Step lemma: feeds Z3 the one-step recurrence at a symbolic index. It MUST
   // recurse — `reveal_with_fuel` alone does not unfold a spec call at a
   // symbolic argument.
   proof void lemma_count_step(int i)
     pre(i >= 1)
     post(count(i) == 1 + count(i - 1))
     decreases(i)
   {
     reveal_with_fuel(count, 2);
     if (i > 1) { lemma_count_step(i - 1); }
   }

   int compute_count(int n)
     pre(n >= 0 && n <= 10)
     post(result == count(n))
   {
     int acc = 0, i = 1;
     while (i <= n)
       invariant(i >= 1 && i <= n + 1 && acc == count(i - 1))
       decreases(n - i + 1)
     {
       ghost {
         reveal_with_fuel(count, 2);
         lemma_count_step(i);   // supplies count(i) == 1 + count(i - 1)
       }
       acc = acc + 1;
       i = i + 1;
     }
     return acc;
   }

Two rules of thumb for this pattern:

- The **step lemma must be recursive**. Revealing fuel exposes the spec's
  definition, but proving the recurrence at the *symbolic* loop index needs the
  inductive call ``lemma_count_step(i - 1)``. A non-recursive lemma returns
  ``unknown``. (See ``safe_fib``'s ``lemma_fibo_step`` for the canonical form.)
- **Keep specs linear.** ``count(n) == n`` and Fibonacci verify; a spec whose
  body multiplies (``n * factorial(n - 1)``) lands in nonlinear arithmetic, which
  SMT cannot decide, so the prover honestly reports ``unknown``.

