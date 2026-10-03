Chapter 20 — From mathematics to verified code
==============================================

A specification is a mathematical statement and a proof is an argument for
it. This chapter takes arguments you would write on paper and translates
them, one construct at a time, into contracts and proofs that CppVerify
checks. Each example below is complete: it verifies as shown, and the output
is the verifier's.

=====================================  ==============================================
On paper                               In CppVerify
=====================================  ==============================================
:math:`f(n) = \dots f(n-1) \dots`      a ``spec`` function with ``decreases``
Lemma: if :math:`H` then :math:`C`     ``proof void l(...) pre(H) post(C)``
induction on :math:`n`                 the lemma calls itself at a smaller measure
"by Lemma L"                           call ``L`` in a ghost block or a ``by`` block
:math:`a = b \le c < d`                ``calc { a; == b; <= c; < d; }``
definition by cases                    ``behavior(name, case)`` clauses
:math:`\forall k \in [lo, hi).\ P`     ``forall(k, lo, hi, P)``
:math:`\forall k \in \mathbb{Z}.\ P`   ``forall(k, P)``, with ``trigger(...)``
:math:`\exists k.\ P`                  ``exists(k, lo, hi, P)`` or ``exists(k, P)``
"some :math:`k` with :math:`P`"        ``choose(k, lo, hi, P)``
a finite sequence, set, multiset, map  ``cppverify::seq``, ``set``, ``multiset``, ``map``
=====================================  ==============================================

Induction: Gauss's sum
----------------------

Let :math:`S(n) = \sum_{i=0}^{n-1} i`. **Claim:** :math:`2S(n) = n(n-1)` for
every :math:`n \ge 0`. **Proof** by induction on :math:`n`. For :math:`n = 0`
both sides are 0. For :math:`n > 0`,

.. math::

   2S(n) = 2\,(S(n-1) + (n-1)) = (n-1)(n-2) + 2(n-1) = n(n-1),

using the claim for :math:`n - 1` in the second step.

The definition becomes a ``spec`` function, the claim a ``proof`` function,
and the induction a recursive call at a smaller ``decreases`` measure, which
is the induction hypothesis. ``calc`` writes the chain of equalities as it
stands on paper, with the hypothesis cited at the step that uses it:

.. cppverify-example: label S

.. code-block:: cpp

   spec int S(int n)
     decreases(n)
   {
     return n <= 0 ? 0 : S(n - 1) + (n - 1);
   }

   proof void gauss(int n)
     pre(n >= 0)
     post(2 * S(n) == n * (n - 1))
     decreases(n)
   {
     if (n > 0) {
       calc {
         2 * S(n);
         == 2 * (S(n - 1) + (n - 1));
         == { gauss(n - 1); }
         (n - 1) * (n - 2) + 2 * (n - 1);
         == n * (n - 1);
       }
     }
   }

A lemma is used by calling it, which makes its postcondition a fact at that
point. A loop that adds up ``0 + 1 + ... + (n - 1)`` keeps ``s == S(i)`` as
its invariant. To show that ``s + i`` cannot overflow, it needs the closed
form at ``i``, so the body calls the lemma there:

.. cppverify-example: with S

.. code-block:: cpp

   int sum_below(int n)
     pre(n >= 0 && n <= 10000)
     post(2 * result == n * (n - 1))
   {
     int s = 0;
     for (int i = 0; i < n; i = i + 1)
       invariant(0 <= i && i <= n && s == S(i))
       decreases(n - i)
     {
       ghost { gauss(i); }
       s = s + i;
     }
     ghost { gauss(n); }
     return s;
   }

.. code-block:: text

   Verified: spec decreases: S
   Verified: gauss [backend=z3]
   Verified: sum_below [backend=z3]

Without ``ghost { gauss(i); }`` the overflow check knows only ``s == S(i)``,
and ``S(i)`` could be anything:

.. code-block:: text

   gauss.cpp:33:7: Unresolved: sum_below [backend=z3] [reason=spec.fuel]
     (proof obligation ...::overflow@33:7: every counterexample found
     applies S beyond its unfolding fuel and is refuted by its definition
     (then z3 returned unknown: timeout); raise reveal_with_fuel, bound the
     argument, or prove it by induction in a proof function)

The location is the statement ``s = s + i``. The message names the remedy:
the induction is already proved, as ``gauss``, and only needs citing.

For a claim as direct as this one, CppVerify also tries induction by itself
when the solver alone cannot settle a recursive spec (see
:doc:`ch16-when-verification-fails`), and ``gauss`` verifies even with an
empty body. Write the proof anyway when the argument is not a plain
induction on one variable, or to record why the claim holds.

A lemma's facts last until the end of the function. To use one for a single
claim only, prove the claim ``by`` it; nothing else from the block remains:

.. cppverify-example: with S

.. code-block:: cpp

   void bound(int n)
     pre(n >= 0 && n <= 10000)
   {
     contract_assert(2 * S(n) <= n * n) by { gauss(n); }
   }

Chains of inequalities
----------------------

**Claim:** if :math:`0 \le a \le b` then :math:`a^2 \le b^2`. **Proof:**
:math:`a \cdot a \le b \cdot a \le b \cdot b`, multiplying :math:`a \le b`
first by :math:`a \ge 0`, then by :math:`b \ge 0`.

Multiplication by a nonnegative number preserves order; that is a lemma, and
each step cites it:

.. code-block:: cpp

   proof void mul_monotone(int a, int b, int c)
     pre(a <= b && c >= 0)
     post(a * c <= b * c)
   {
   }

   void squares(int a, int b)
     pre(0 <= a && a <= b && b <= 46340)
   {
     calc {
       a * a;
       <= { mul_monotone(a, b, a); }
       b * a;
       <= { mul_monotone(a, b, b); }
       b * b;
     }
     contract_assert(a * a <= b * b);
   }

``calc`` proves each step on its own and concludes the relation between the
first and the last term: here ``a * a <= b * b``. Contract arithmetic is
mathematical, so ``a * a`` in a contract never overflows; the bound on ``b``
matters only for the executable code that might compute it.

Definitions by cases
--------------------

.. math::

   \mathrm{clamp}(x) = \begin{cases} lo & x < lo \\ x & lo \le x \le hi \\
   hi & x > hi \end{cases}

A definition by cases is meaningful when the cases cover every input and do
not overlap. Behaviors state the cases of a contract, and
``complete_behaviors`` and ``disjoint_behaviors`` check exactly those two
conditions:

.. code-block:: cpp

   int clamp(int x, int lo, int hi)
     pre(lo <= hi)
     behavior(below, x < lo)
       post(result == lo)
     behavior(inside, lo <= x && x <= hi)
       post(result == x)
     behavior(above, x > hi)
       post(result == hi)
     complete_behaviors
     disjoint_behaviors
   {
     if (x < lo)
       return lo;
     if (x > hi)
       return hi;
     return x;
   }

Writing ``x <= lo`` for the first case makes two cases overlap at
``x == lo``, and writing ``lo < x`` for the second leaves ``x == lo`` in no
case:

.. code-block:: cpp

   int clamp_overlap(int x, int lo, int hi)
     pre(lo <= hi)
     behavior(below, x <= lo)
       post(result == lo)
     behavior(inside, lo <= x && x <= hi)
       post(result == x)
     behavior(above, x > hi)
       post(result == hi)
     complete_behaviors
     disjoint_behaviors
   {
     if (x < lo)
       return lo;
     if (x > hi)
       return hi;
     return x;
   }

   int clamp_gap(int x, int lo, int hi)
     pre(lo <= hi)
     behavior(below, x < lo)
       post(result == lo)
     behavior(inside, lo < x && x <= hi)
       post(result == x)
     behavior(above, x > hi)
       post(result == hi)
     complete_behaviors
     disjoint_behaviors
   {
     if (x < lo)
       return lo;
     if (x > hi)
       return hi;
     return x;
   }

Both are reported with the input that shows it:

.. code-block:: text

   error: verification failed: clamp_overlap [...::assertion@10:3]
     (counterexample: hi = 0, lo = 0, x = 0)
   error: verification failed: clamp_gap [...::assertion@27:3]
     (counterexample: hi = 0, lo = 0, x = 0)

Universal statements: sorted arrays
-----------------------------------

An array is sorted when :math:`a_i \le a_j` for all :math:`i \le j`. It is
enough to check neighbors: **Claim:** if :math:`a_k \le a_{k+1}` for every
:math:`k`, then :math:`a_i \le a_j` whenever :math:`i \le j`. **Proof** by
induction on :math:`j - i`: :math:`a_i \le a_{j-1} \le a_j`.

.. cppverify-example: label sortedpair

.. code-block:: cpp

   #include <cppverify.h>
   using cppverify::valid;

   proof void sorted_pair(const int *a, int n, int i, int j)
     pre(valid(a, n) && 0 <= i && i <= j && j < n)
     pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
     post(a[i] <= a[j])
     decreases(j - i)
   {
     if (i < j)
       sorted_pair(a, n, i, j - 1);
   }

The lemma's parameters ``i`` and ``j`` play the role of "for all
:math:`i \le j`": a caller instantiates it where it needs it. Binary search
needs the pairwise form at every probe, so it is easiest to assume that form
directly. The invariant says what the search has ruled out:

.. cppverify-example: with sortedpair

.. code-block:: cpp

   int search(const int *a, int n, int x)
     pre(valid(a, n) && 0 <= n && n <= 100000)
     pre(forall(i, 0, n, forall(j, i, n, a[i] <= a[j])))
     post(-1 <= result && result < n)
     post(result >= 0 ? a[result] == x : forall(k, 0, n, a[k] != x))
   {
     int lo = 0;
     int hi = n;
     while (lo < hi)
       invariant(0 <= lo && lo <= hi && hi <= n)
       invariant(forall(k, 0, lo, a[k] < x))
       invariant(forall(k, hi, n, a[k] > x))
       decreases(hi - lo)
     {
       int mid = lo + (hi - lo) / 2;
       if (a[mid] < x)
         lo = mid + 1;
       else if (a[mid] > x)
         hi = mid;
       else
         return mid;
     }
     return -1;
   }

.. code-block:: text

   Verified: sorted_pair [backend=z3]
   Verified: search [backend=z3]

When ``a[mid] < x``, every ``a[k]`` with ``k <= mid`` is at most ``a[mid]``,
so the solver instantiates the sortedness fact at ``j = mid``. A quantified
fact is used only at such instances. The solver finds them by matching the
fact's memory reads against the reads of the program, and CppVerify adds
the instances at reads with constant or offset indices (``a[2]``,
``a[i + 1]``), which solvers do not match by themselves.

Facts about all integers, and triggers
--------------------------------------

Over all integers there are no reads to match, so a quantified fact needs a
*trigger*: the term whose occurrences say where to use it.

.. code-block:: cpp

   spec int pow2(int n)
     decreases(n)
   {
     return n <= 0 ? 1 : 2 * pow2(n - 1);
   }

   void doubles(int a)
     pre(a >= 0 && a <= 50)
     pre(forall(k, k < 0 || trigger(pow2(k)) < pow2(k + 1)))
   {
     contract_assert(pow2(a) < pow2(a + 1));
   }

``trigger(pow2(k))`` makes every ``pow2(t)`` in the proof an instance at
``k = t``; here ``pow2(a)`` gives the fact at ``a``. Each instance mentions
``pow2(k + 1)``, which matches the trigger again: proving ``pow2(a) <
pow2(a + 3)`` this way takes three generations of instances, and a goal the
fact cannot settle can keep instantiating it until the timeout. Such a
*matching loop* shows up in ``--profile-quantifiers`` as a quantifier
instantiated thousands of times (see :doc:`ch16-when-verification-fails`).
Prefer a lemma with a parameter, which is used exactly where it is called,
to a quantified fact whose trigger recreates itself.

A proof function cannot yet prove ``forall(k, ...)`` by induction, since its
body cannot name the bound ``k``; state the lemma for a parameter, as
``sorted_pair`` does, and quantify in the caller's precondition.

Existence and choice
--------------------

**Claim:** a nonempty finite array has a largest element. The constructive
proof is the loop that finds it:

.. cppverify-example: label argmax

.. code-block:: cpp

   int argmax(const int *a, int n)
     pre(valid(a, n) && 1 <= n && n <= 1000)
     post(0 <= result && result < n)
     post(forall(k, 0, n, a[k] <= a[result]))
   {
     int m = 0;
     for (int i = 1; i < n; i = i + 1)
       invariant(1 <= i && i <= n && 0 <= m && m < i)
       invariant(forall(k, 0, i, a[k] <= a[m]))
       decreases(n - i)
     {
       if (a[i] > a[m])
         m = i;
     }
     return m;
   }

A specification may need "the" maximum without an algorithm. ``choose``
names some index that has the property, Hilbert's :math:`\varepsilon`:

.. cppverify-example: with argmax
.. cppverify-example: label maxes

.. code-block:: cpp

   spec int some_max(const int *a, int n)
   {
     return choose(i, 0, n, forall(k, 0, n, a[k] <= a[i]));
   }

   int largest(const int *a, int n)
     pre(valid(a, n) && 1 <= n && n <= 1000)
     post(result == a[some_max(a, n)])
   {
     int m = argmax(a, n);
     contract_assert(exists(i, 0, n, forall(k, 0, n, a[k] <= a[i])));
     return a[m];
   }

The ``contract_assert`` is the existence half of the argument: ``argmax``
returned a witness, so a maximum exists, and therefore ``some_max`` is one.
Two maxima have equal values, so ``a[m] == a[some_max(a, n)]``. Which index
``choose`` picks is not known, though, and a claim that depends on it
fails:

.. cppverify-example: with argmax maxes

.. code-block:: cpp

   int which(const int *a, int n)
     pre(valid(a, n) && 1 <= n && n <= 1000)
     post(result == some_max(a, n))
   {
     return argmax(a, n);
   }

.. code-block:: text

   error: verification failed: which [...::postcondition@3:15]
     (counterexample: result = 0, a = 536, n = 2; trace: call.argmax ...)

In the counterexample both elements are maxima, ``argmax`` returns 0, and
``choose`` picks 1.

Collections: sums over a sequence
---------------------------------

Mathematics talks about finite sequences, sets, and multisets directly.
``<cppverify.h>`` provides them as verification-only values, so a ghost
sequence can record the array a loop has read, and a spec function over it
states what the loop computes:

.. math::

   \mathrm{total}(\langle\rangle) = 0, \qquad
   \mathrm{total}(s \cdot x) = \mathrm{total}(s) + x

.. cppverify-example: label total

.. code-block:: cpp

   #include <cppverify.h>
   using cppverify::seq;
   using cppverify::valid;

   spec int total(seq s)
     decreases(s.len())
   {
     return s.len() <= 0 ? 0 : total(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
   }

   proof void total_empty()
     post(total(cppverify::seq_empty()) == 0)
   {
   }

   proof void total_push(seq s, int x)
     post(total(s.push(x)) == total(s) + x)
   {
   }

   int sum_array(const int *a, int n)
     pre(valid(a, n) && n >= 0 && n <= 100)
     pre(forall(k, 0, n, 0 <= a[k] && a[k] <= 1000))
     post(0 <= result && result <= 1000 * n)
   {
     ghost {
       hide(total);
       total_empty();
     }
     ghost seq seen = cppverify::seq_empty();
     int s = 0;
     for (int i = 0; i < n; i = i + 1)
       invariant(0 <= i && i <= n && 0 <= s && s <= 1000 * i)
       invariant(seen.len() == i && forall(k, 0, i, seen[k] == a[k]))
       invariant(s == total(seen))
       decreases(n - i)
     {
       ghost {
         total_push(seen, a[i]);
         seen = seen.push(a[i]);
       }
       s = s + a[i];
     }
     return s;
   }

The two lemmas are the two equations of the definition, each proved from
the spec's body. The loop uses only them: ``hide(total)`` keeps the
recursive definition out of this function's queries, which would otherwise
unfold it at every sequence in sight. Hiding a definition and citing the
lemmas that matter is the standard remedy when a proof that "should" be
easy times out.

In ghost and proof code a sequence's length and elements are mathematical
integers, like everything in a contract: ``s.subrange(0, s.len() - 1)``
is exact. Storing one in an ``int`` is a conversion that must fit, so
``int x = s[0];`` fails unless a precondition bounds ``s[0]``.

The equivalences between operations hold as expected, for example between
membership and an index:

.. code-block:: cpp

   proof void contains_is_exists(seq s, int x)
     post(s.contains(x) == exists(k, 0, s.len(), s[k] == x))
   {
   }

Sequence induction follows the shape of the definition. **Claim:**
:math:`\mathrm{total}(s \cdot t) = \mathrm{total}(s) + \mathrm{total}(t)`,
by induction on the length of :math:`t`, removing its last element:

.. cppverify-example: with total

.. code-block:: cpp

   proof void total_concat(seq s, seq t)
     post(total(s + t) == total(s) + total(t))
     decreases(t.len())
   {
     if (t.len() > 0)
       total_concat(s, t.subrange(0, t.len() - 1));
   }

.. code-block:: text

   $ cpp-verify concat.cpp
   Verified: spec decreases: total
   Verified: total_concat [backend=z3]

The recursive call is the induction hypothesis for the shorter sequence,
and ``decreases(t.len())`` is what makes the recursion a proof: the
verifier checks that every call lowers it, so the argument is well founded.
The step also needs a fact about sequences: dropping the last element of
``s + t`` leaves ``s`` followed by ``t`` without its last element. The
verifier knows how an element is read from a concatenation, a push, or a
subrange, and how a subrange of a concatenation splits, so it finds that
itself. No solver finds the induction itself; the recursive call is yours,
as in Verus and Dafny.

Sometimes the step needs a sequence equality that the solver does not see.
State it: an equality of sequences that a proof asserts is proved element by
element when need be (equal lengths and equal elements, Verus's ``=~=``), and
from then on it is a fact. A count of occurrences, and its invariance under
``reverse``, show both kinds of step:

.. code-block:: cpp

   spec int count(seq s, int x)
     decreases(s.len())
   {
     return s.len() <= 0
                ? 0
                : count(s.subrange(0, s.len() - 1), x) +
                      (s[s.len() - 1] == x ? 1 : 0);
   }

   proof void count_concat(seq s, seq t, int x)
     post(count(s + t, x) == count(s, x) + count(t, x))
     decreases(t.len())
   {
     if (t.len() > 0)
       count_concat(s, t.subrange(0, t.len() - 1), x);
   }

   proof void count_reverse(seq s, int x)
     post(count(s.reverse(), x) == count(s, x))
     decreases(s.len())
   {
     if (s.len() > 0) {
       seq tail = s.subrange(1, s.len());
       count_reverse(tail, x);
       count_concat(cppverify::seq_of(s[0]), tail, x);
       contract_assert(cppverify::seq_of(s[0]) + tail == s);
     }
   }

``s.reverse()`` is defined as ``tail.reverse().push(s[0])``, so its count is
the count of ``tail`` plus one for ``s[0]`` when it is ``x``. ``count``
removes the *last* element, so ``count_concat`` relates it to the front, and
the asserted equality tells the solver that ``s`` is ``s[0]`` followed by
``tail``; without that line the step stays unresolved with ``spec.fuel``.

``reverse`` states its length (``s.reverse().len() == s.len()``), which its
definition proves by induction when it is checked. A property of its
elements is a lemma like any other:

.. code-block:: cpp

   proof void reverse_index(seq s, long long k)
     pre(0 <= k && k < s.len())
     post(s.reverse()[k] == s[s.len() - 1 - k])
     decreases(s.len())
   {
     if (k < s.len() - 1)
       reverse_index(s.subrange(1, s.len()), k);
   }

When the solver needs help
--------------------------

The examples above use a handful of techniques, which cover most proofs:

- **Cite a lemma where it is needed**, as ``sum_below`` does with
  ``gauss(i)``. A lemma call is an instance chosen by you rather than by
  the solver.
- **Split an argument into steps** with ``calc`` or a few
  ``contract_assert`` statements. Each step is a smaller query.
- **Keep facts local** with ``contract_assert(...) by { ... }``, and keep
  definitions out of the way with ``hide`` once lemmas state what matters.
- **Choose triggers** that the proof mentions and that instances do not
  recreate; check with ``--profile-quantifiers``.
- **State the sequence equality** a step needs, as ``count_reverse`` does:
  a stated equality is proved element by element.
- **Use the other solver.** Z3 and cvc5 have different strengths; a proof
  that times out under one may verify with the other
  (``--backend=cvc5``). Both are exact, and a strict
  ``--backend=portfolio`` asks for agreement.
- **Run obligations separately.** With more than one job (the default uses
  every core), each obligation is also solved on its own, in parallel with
  the combined query; a function whose combined query is hard but whose
  obligations are each easy then verifies at once.
