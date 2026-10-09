Contract expressions
====================

- ``cppverify::result`` — return value; **postconditions only**
- ``cppverify::old(expr)`` — value at function entry; **postconditions and loop invariants**
- ``cppverify::forall(i, lo, hi, body)`` — bounded ∀ over ``i in [lo, hi)``
- ``cppverify::exists(i, lo, hi, body)`` — bounded ∃ over ``i in [lo, hi)``
- ``cppverify::forall(i, body)`` / ``cppverify::exists(i, body)`` — over all mathematical integers
- ``cppverify::trigger(term)`` — in a quantifier body: the pattern that instantiates it
- ``cppverify::choose(i, body)`` / ``cppverify::choose(i, lo, hi, body)`` — some integer satisfying
  ``body`` (in ``[lo, hi)``), when one exists
- collection operations of ``<cppverify.h>`` (``s.len()``, ``s[i]``,
  ``a.contains(x)``, ``m[k]``, ...)

Must be contextually ``bool`` where used as conditions.

The range ``[lo, hi)`` may be **symbolic** (e.g. ``cppverify::forall(i, 0, n, ...)``).
A bounded quantifier reaches the solver as a quantifier, whatever its range:
the ``cppverify::trigger`` marks in its body become its patterns, and without
them the solver chooses its own. This is what lets a loop invariant talk about a
whole array range (see :doc:`pointers`). Proving a ``cppverify::forall`` over a symbolic
range (the common case for loop invariants and postconditions) is well supported;
*proving* an ``cppverify::exists`` over a symbolic range is currently incomplete and may
report ``unknown`` — supply the witness when you need one.

Quantifiers without bounds range over all integers; a counterexample to one is
certified when its body depends on the bound variables through linear
arithmetic, comparisons, memory or collection reads, and other quantifiers,
nested to any depth (the checker decides it as Presburger arithmetic).
``cppverify::trigger(term)`` marks a memory read, collection read, or recursive spec call
that mentions a bound variable as the quantifier's pattern; other marks are
ignored with a warning. ``--profile-quantifiers`` shows which quantifiers an
unresolved query instantiated most. ``cppverify::choose`` and the collections exist only
for verification. See :doc:`../book/part-ii/ch13-spec-and-proof-functions`.

``cppverify::old`` is valid in postconditions and loop invariants, where it denotes the
function's entry state. ``cppverify::result`` is only valid in postconditions and cannot
occur inside ``cppverify::old`` because a return value has no function-entry state.
Contract arithmetic is mathematical: ``+``, ``-``, ``*``, ``/``, ``%``, and
unary ``-`` in a contract are exact, while ``cppverify::proof`` and executable code use
machine integers (see :doc:`integers`).

Examples
--------

``cppverify::old`` and ``cppverify::result`` relate the state after the call to the state before,
and bounded quantifiers state facts about every element of a range, or
about one:

.. code-block:: cpp

   void increment(int *p)
     cv::pre(p != nullptr && *p < 1000)
     cv::modifies(*p)
     cv::post(*p == cv::old(*p) + 1)
   {
     *p = *p + 1;
   }

   int index_of(const int *a, int n, int x)
     cv::pre(valid(a, n) && 0 <= n && n <= 1000)
     cv::post(cv::result == -1 || (0 <= cv::result && cv::result < n && a[cv::result] == x))
     cv::post(cv::result != -1 || cv::forall(k, 0, n, a[k] != x))
   {
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && cv::forall(k, 0, i, a[k] != x))
       cv::decreases(n - i)
     {
       if (a[i] == x)
         return i;
     }
     return -1;
   }

   cv::proof void has_zero(const int *a, int n)
     cv::pre(valid(a, n) && n >= 3 && a[2] == 0)
     cv::post(cv::exists(k, 0, n, a[k] == 0))
   {
   }

Without bounds a quantifier ranges over every integer, ``cppverify::trigger`` names
the term that instantiates it, and ``cppverify::choose`` picks a witness:

.. code-block:: cpp

   cv::spec int sq(int x) { return x * x; }

   cv::proof void sq_nonnegative()
     cv::post(cv::forall(k, sq(k) >= 0))
   {
   }

   cv::proof void positives(const int *a, int n)
     cv::pre(valid(a, n) && n >= 4)
     cv::pre(cv::forall(k, 0, n, cv::trigger(a[k]) > 0))
     cv::post(a[3] > 0)
   {
   }

   cv::spec int half(int n) { return cv::choose(k, 2 * k == n); }

   cv::proof void half_of_ten()
     cv::post(2 * half(10) == 10)
   {
   }

The collections of ``<cppverify.h>`` are values of mathematical integers:

.. code-block:: cpp

   cv::proof void collections(seq s, set a, multiset m, map f)
     cv::post(s.push(7).len() == s.len() + 1 && s.push(7)[s.len()] == 7)
     cv::post(a.insert(3).contains(3) && !a.remove(3).contains(3))
     cv::post(a.subset_of(a.unite(a.insert(4))))
     cv::post(m.insert(5).insert(5).count(5) == m.count(5) + 2)
     cv::post(f.insert(1, 9).contains(1) && f.insert(1, 9)[1] == 9)
   {
   }

.. code-block:: text

   Verified: collections [backend=z3]

``subrange(lo, hi)`` is the half-open slice ``[lo, hi)`` and ``+`` concatenates; equal
lengths and equal elements make two sequences equal:

.. code-block:: cpp

   cv::proof void slices(seq s, seq t)
     cv::pre(s.len() >= 2)
     cv::post(s.subrange(0, 1) + s.subrange(1, s.len()) == s)
     cv::post((s + t).subrange(0, s.len()) == s)
     cv::post(s.subrange(1, s.len()).len() == s.len() - 1)
   {
   }
