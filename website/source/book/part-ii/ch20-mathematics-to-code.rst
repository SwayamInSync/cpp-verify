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
:math:`f(n) = \dots f(n-1) \dots`      a ``cppverify::spec`` function with ``cppverify::decreases``
Lemma: if :math:`H` then :math:`C`     ``cppverify::proof void l(...) cppverify::pre(H) cppverify::post(C)``
induction on :math:`n`                 the lemma calls itself at a smaller measure
"by Lemma L"                           call ``L`` in a ghost block or a ``by`` block
:math:`a = b \le c < d`                ``cppverify::calc { a; == b; <= c; < d; }``
definition by cases                    ``cppverify::behavior(name, case)`` clauses
:math:`\forall k \in [lo, hi).\ P`     ``cppverify::forall(k, lo, hi, P)``
:math:`\forall k \in \mathbb{Z}.\ P`   ``cppverify::forall(k, P)``, with ``cppverify::trigger(...)``
:math:`\exists k.\ P`                  ``cppverify::exists(k, lo, hi, P)`` or ``cppverify::exists(k, P)``
"some :math:`k` with :math:`P`"        ``cppverify::choose(k, lo, hi, P)``
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

The definition becomes a ``cppverify::spec`` function, the claim a ``cppverify::proof`` function,
and the induction a recursive call at a smaller ``cppverify::decreases`` measure, which
is the induction hypothesis. ``cppverify::calc`` writes the chain of equalities as it
stands on paper, with the hypothesis cited at the step that uses it:

.. cppverify-example: label S

.. code-block:: cpp

   cv::spec int S(int n)
     cv::decreases(n)
   {
     return n <= 0 ? 0 : S(n - 1) + (n - 1);
   }

   cv::proof void gauss(int n)
     cv::pre(n >= 0)
     cv::post(2 * S(n) == n * (n - 1))
     cv::decreases(n)
   {
     if (n > 0) {
       cv::calc {
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
     cv::pre(n >= 0 && n <= 10000)
     cv::post(2 * cv::result == n * (n - 1))
   {
     int s = 0;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && s == S(i))
       cv::decreases(n - i)
     {
       cv::ghost { gauss(i); }
       s = s + i;
     }
     cv::ghost { gauss(n); }
     return s;
   }

.. code-block:: text

   Verified: spec decreases: S
   Verified: gauss [backend=z3]
   Verified: sum_below [backend=z3]

Without ``cppverify::ghost { gauss(i); }`` the overflow check knows only ``s == S(i)``,
and ``S(i)`` could be anything:

.. code-block:: text

   gauss.cpp:33:7: Unresolved: sum_below [backend=z3] [reason=spec.fuel]
     (proof obligation ...::overflow@33:7: every counterexample the solver
     proposed applies S beyond the unfoldings it was given and is refuted by
     its definition (then z3 returned unknown: timeout); reveal_with_fuel
     settles it if a fixed depth of unfolding does; induction following S
     and induction on i did not prove it; if the claim holds, it needs a
     proof by induction: a recursive proof function that uses it at smaller
     values)

The location is the statement ``s = s + i``. The message says what was
tried: the solver needed ``S`` beyond the unfoldings it was given, and the
inductions the verifier tried by itself did not prove the step, which needs
the closed form rather than the loop's own invariant. The induction it asks
for is already proved, as ``gauss``, and only needs citing.

CppVerify tries induction by itself when the solver alone cannot settle a
recursive spec (section "Automatic induction" of
:doc:`ch13-spec-and-proof-functions`), and ``gauss`` on its own verifies
even with an empty body, ``[by induction following S]``. Write the proof
anyway when the argument is not a plain induction over the spec's
recursion, or to record why the claim holds.

A lemma's facts last until the end of the function. To use one for a single
claim only, prove the claim ``by`` it; nothing else from the block remains:

.. cppverify-example: with S

.. code-block:: cpp

   void bound(int n)
     cv::pre(n >= 0 && n <= 10000)
   {
     cv::check(2 * S(n) <= n * n) by { gauss(n); }
   }

Chains of inequalities
----------------------

**Claim:** if :math:`0 \le a \le b` then :math:`a^2 \le b^2`. **Proof:**
:math:`a \cdot a \le b \cdot a \le b \cdot b`, multiplying :math:`a \le b`
first by :math:`a \ge 0`, then by :math:`b \ge 0`.

Multiplication by a nonnegative number preserves order; that is a lemma, and
each step cites it:

.. code-block:: cpp

   cv::proof void mul_monotone(int a, int b, int c)
     cv::pre(a <= b && c >= 0)
     cv::post(a * c <= b * c)
   {
   }

   void squares(int a, int b)
     cv::pre(0 <= a && a <= b && b <= 46340)
   {
     cv::calc {
       a * a;
       <= { mul_monotone(a, b, a); }
       b * a;
       <= { mul_monotone(a, b, b); }
       b * b;
     }
     cv::check(a * a <= b * b);
   }

``cppverify::calc`` proves each step on its own and concludes the relation between the
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
``cppverify::complete_behaviors`` and ``cppverify::disjoint_behaviors`` check exactly those two
conditions:

.. code-block:: cpp

   int clamp(int x, int lo, int hi)
     cv::pre(lo <= hi)
     cv::behavior(below, x < lo)
       cv::post(cv::result == lo)
     cv::behavior(inside, lo <= x && x <= hi)
       cv::post(cv::result == x)
     cv::behavior(above, x > hi)
       cv::post(cv::result == hi)
     cv::complete_behaviors
     cv::disjoint_behaviors
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
     cv::pre(lo <= hi)
     cv::behavior(below, x <= lo)
       cv::post(cv::result == lo)
     cv::behavior(inside, lo <= x && x <= hi)
       cv::post(cv::result == x)
     cv::behavior(above, x > hi)
       cv::post(cv::result == hi)
     cv::complete_behaviors
     cv::disjoint_behaviors
   {
     if (x < lo)
       return lo;
     if (x > hi)
       return hi;
     return x;
   }

   int clamp_gap(int x, int lo, int hi)
     cv::pre(lo <= hi)
     cv::behavior(below, x < lo)
       cv::post(cv::result == lo)
     cv::behavior(inside, lo < x && x <= hi)
       cv::post(cv::result == x)
     cv::behavior(above, x > hi)
       cv::post(cv::result == hi)
     cv::complete_behaviors
     cv::disjoint_behaviors
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

   using cppverify::valid;

   cv::proof void sorted_pair(const int *a, int n, int i, int j)
     cv::pre(valid(a, n) && 0 <= i && i <= j && j < n)
     cv::pre(cv::forall(k, 0, n - 1, a[k] <= a[k + 1]))
     cv::post(a[i] <= a[j])
     cv::decreases(j - i)
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
     cv::pre(valid(a, n) && 0 <= n && n <= 100000)
     cv::pre(cv::forall(i, 0, n, cv::forall(j, i, n, a[i] <= a[j])))
     cv::post(-1 <= cv::result && cv::result < n)
     cv::post(cv::result >= 0 ? a[cv::result] == x : cv::forall(k, 0, n, a[k] != x))
   {
     int lo = 0;
     int hi = n;
     while (lo < hi)
       cv::invariant(0 <= lo && lo <= hi && hi <= n)
       cv::invariant(cv::forall(k, 0, lo, a[k] < x))
       cv::invariant(cv::forall(k, hi, n, a[k] > x))
       cv::decreases(hi - lo)
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

   cv::spec int pow2(int n)
     cv::decreases(n)
   {
     return n <= 0 ? 1 : 2 * pow2(n - 1);
   }

   void doubles(int a)
     cv::pre(a >= 0 && a <= 50)
     cv::pre(cv::forall(k, k < 0 || cv::trigger(pow2(k)) < pow2(k + 1)))
   {
     cv::check(pow2(a) < pow2(a + 1));
   }

``cppverify::trigger(pow2(k))`` makes every ``pow2(t)`` in the proof an instance at
``k = t``; here ``pow2(a)`` gives the fact at ``a``. Each instance mentions
``pow2(k + 1)``, which matches the trigger again: proving ``pow2(a) <
pow2(a + 3)`` this way takes three generations of instances, and a goal the
fact cannot settle can keep instantiating it until the timeout. Such a
*matching loop* shows up in ``--profile-quantifiers`` as a quantifier
instantiated thousands of times (see :doc:`ch16-when-verification-fails`).
Prefer a lemma with a parameter, which is used exactly where it is called,
to a quantified fact whose trigger recreates itself.

A proof function can prove ``cppverify::forall(k, ...)`` from a lemma
stated for a parameter, as ``sorted_pair`` is: in
``cppverify::check(cppverify::forall(k, lo, hi, P)) by { ... }`` the block
names an arbitrary ``k`` in ``[lo, hi)``, and a lemma call there is the
instance for that ``k`` (``below_last`` in
:doc:`ch13-spec-and-proof-functions`).

Existence and choice
--------------------

**Claim:** a nonempty finite array has a largest element. The constructive
proof is the loop that finds it:

.. cppverify-example: label argmax

.. code-block:: cpp

   int argmax(const int *a, int n)
     cv::pre(valid(a, n) && 1 <= n && n <= 1000)
     cv::post(0 <= cv::result && cv::result < n)
     cv::post(cv::forall(k, 0, n, a[k] <= a[cv::result]))
   {
     int m = 0;
     for (int i = 1; i < n; i = i + 1)
       cv::invariant(1 <= i && i <= n && 0 <= m && m < i)
       cv::invariant(cv::forall(k, 0, i, a[k] <= a[m]))
       cv::decreases(n - i)
     {
       if (a[i] > a[m])
         m = i;
     }
     return m;
   }

A specification may need "the" maximum without an algorithm. ``cppverify::choose``
names some index that has the property, Hilbert's :math:`\varepsilon`:

.. cppverify-example: with argmax
.. cppverify-example: label maxes

.. code-block:: cpp

   cv::spec int some_max(const int *a, int n)
   {
     return cv::choose(i, 0, n, cv::forall(k, 0, n, a[k] <= a[i]));
   }

   int largest(const int *a, int n)
     cv::pre(valid(a, n) && 1 <= n && n <= 1000)
     cv::post(cv::result == a[some_max(a, n)])
   {
     int m = argmax(a, n);
     cv::check(cv::exists(i, 0, n, cv::forall(k, 0, n, a[k] <= a[i])));
     return a[m];
   }

The ``cppverify::check`` is the existence half of the argument: ``argmax``
returned a witness, so a maximum exists, and therefore ``some_max`` is one.
Two maxima have equal values, so ``a[m] == a[some_max(a, n)]``. Which index
``cppverify::choose`` picks is not known, though, and a claim that depends on it
fails:

.. cppverify-example: with argmax maxes

.. code-block:: cpp

   int which(const int *a, int n)
     cv::pre(valid(a, n) && 1 <= n && n <= 1000)
     cv::post(cv::result == some_max(a, n))
   {
     return argmax(a, n);
   }

.. code-block:: text

   error: verification failed: which [...::postcondition@3:15]
     (counterexample: result = 0, a = 536, n = 2; trace: call.argmax ...)

In the counterexample both elements are maxima, ``argmax`` returns 0, and
``cppverify::choose`` picks 1.

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

   using cppverify::seq;
   using cppverify::valid;

   cv::spec int total(seq s)
     cv::decreases(s.len())
   {
     return s.len() <= 0 ? 0 : total(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
   }

   cv::proof void total_empty()
     cv::post(total(cppverify::seq_empty()) == 0)
   {
   }

   cv::proof void total_push(seq s, int x)
     cv::post(total(s.push(x)) == total(s) + x)
   {
   }

   int sum_array(const int *a, int n)
     cv::pre(valid(a, n) && n >= 0 && n <= 100)
     cv::pre(cv::forall(k, 0, n, 0 <= a[k] && a[k] <= 1000))
     cv::post(0 <= cv::result && cv::result <= 1000 * n)
   {
     cv::ghost {
       cv::hide(total);
       total_empty();
     }
     cv::ghost seq seen = cppverify::seq_empty();
     int s = 0;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && 0 <= s && s <= 1000 * i)
       cv::invariant(seen.len() == i && cv::forall(k, 0, i, seen[k] == a[k]))
       cv::invariant(s == total(seen))
       cv::decreases(n - i)
     {
       cv::ghost {
         total_push(seen, a[i]);
         seen = seen.push(a[i]);
       }
       s = s + a[i];
     }
     return s;
   }

The two lemmas are the two equations of the definition, each proved from
the spec's body. The loop uses only them: ``cppverify::hide(total)`` keeps the
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

   cv::proof void contains_is_exists(seq s, int x)
     cv::post(s.contains(x) == cv::exists(k, 0, s.len(), s[k] == x))
   {
   }

Sequence induction follows the shape of the definition. **Claim:**
:math:`\mathrm{total}(s \cdot t) = \mathrm{total}(s) + \mathrm{total}(t)`,
by induction on the length of :math:`t`, removing its last element:

.. cppverify-example: with total

.. code-block:: cpp

   cv::proof void total_concat(seq s, seq t)
     cv::post(total(s + t) == total(s) + total(t))
     cv::decreases(t.len())
   {
     if (t.len() > 0)
       total_concat(s, t.subrange(0, t.len() - 1));
   }

.. code-block:: text

   $ cpp-verify concat.cpp
   Verified: spec decreases: total
   Verified: total_concat [backend=z3]

The recursive call is the induction hypothesis for the shorter sequence,
and ``cppverify::decreases(t.len())`` is what makes the recursion a proof: the
verifier checks that every call lowers it, so the argument is well founded.
The step also needs a fact about sequences: dropping the last element of
``s + t`` leaves ``s`` followed by ``t`` without its last element. The
verifier knows how an element is read from a concatenation, a push, or a
subrange, and how a subrange of a concatenation splits, so it finds that
itself. CppVerify's automatic induction also proves ``total_concat`` with an
empty body, ``[by induction following total]``, but slowly (about two
minutes with four jobs); the recursive call states the induction hypothesis
and makes the proof fast and robust.

Sometimes the step needs a sequence equality that the solver does not see.
State it: an equality of sequences that a proof asserts is proved element by
element when need be (equal lengths and equal elements, Verus's ``=~=``), and
from then on it is a fact. A count of occurrences, and its invariance under
``reverse``, show both kinds of step:

.. code-block:: cpp

   cv::spec int count(seq s, int x)
     cv::decreases(s.len())
   {
     return s.len() <= 0
                ? 0
                : count(s.subrange(0, s.len() - 1), x) +
                      (s[s.len() - 1] == x ? 1 : 0);
   }

   cv::proof void count_concat(seq s, seq t, int x)
     cv::post(count(s + t, x) == count(s, x) + count(t, x))
     cv::decreases(t.len())
   {
     if (t.len() > 0)
       count_concat(s, t.subrange(0, t.len() - 1), x);
   }

   cv::proof void count_reverse(seq s, int x)
     cv::post(count(s.reverse(), x) == count(s, x))
     cv::decreases(s.len())
   {
     if (s.len() > 0) {
       seq tail = s.subrange(1, s.len());
       count_reverse(tail, x);
       count_concat(cppverify::seq_of(s[0]), tail, x);
       cv::check(cppverify::seq_of(s[0]) + tail == s);
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

   cv::proof void reverse_index(seq s, long long k)
     cv::pre(0 <= k && k < s.len())
     cv::post(s.reverse()[k] == s[s.len() - 1 - k])
     cv::decreases(s.len())
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
- **Split an argument into steps** with ``cppverify::calc`` or a few
  ``cppverify::check`` statements. Each step is a smaller query.
- **Keep facts local** with ``cppverify::check(...) by { ... }``, and keep
  definitions out of the way with ``cppverify::hide`` once lemmas state what matters.
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
