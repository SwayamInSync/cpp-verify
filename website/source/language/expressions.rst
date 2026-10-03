Contract expressions
====================

- ``result`` — return value; **postconditions only**
- ``old(expr)`` — value at function entry; **postconditions and loop invariants**
- ``forall(i, lo, hi, body)`` — bounded ∀ over ``i in [lo, hi)``
- ``exists(i, lo, hi, body)`` — bounded ∃ over ``i in [lo, hi)``
- ``forall(i, body)`` / ``exists(i, body)`` — over all mathematical integers
- ``trigger(term)`` — in a quantifier body: the pattern that instantiates it
- ``choose(i, body)`` / ``choose(i, lo, hi, body)`` — some integer satisfying
  ``body`` (in ``[lo, hi)``), when one exists
- collection operations of ``<cppverify.h>`` (``s.len()``, ``s[i]``,
  ``a.contains(x)``, ``m[k]``, ...)

Must be contextually ``bool`` where used as conditions.

The range ``[lo, hi)`` may be **symbolic** (e.g. ``forall(i, 0, n, ...)``): a small
concrete range is unrolled, otherwise a real quantifier is emitted with the
heap-access terms as triggers. This is what lets a loop invariant talk about a
whole array range (see :doc:`pointers`). Proving a ``forall`` over a symbolic
range (the common case for loop invariants and postconditions) is well supported;
*proving* an ``exists`` over a symbolic range is currently incomplete and may
report ``unknown`` — use a concrete range, or supply the witness, when you need
one.

Quantifiers without bounds range over all integers; a counterexample to one is
certified when its body depends on the bound variables through linear
arithmetic, comparisons, memory or collection reads, and other quantifiers,
nested to any depth (the checker decides it as Presburger arithmetic).
``trigger(term)`` marks a memory read, collection read, or recursive spec call
that mentions a bound variable as the quantifier's pattern; other marks are
ignored with a warning. ``--profile-quantifiers`` shows which quantifiers an
unresolved query instantiated most. ``choose`` and the collections exist only
for verification. See :doc:`../book/part-ii/ch13-spec-and-proof-functions`.

``old`` is valid in postconditions and loop invariants, where it denotes the
function's entry state. ``result`` is only valid in postconditions and cannot
occur inside ``old`` because a return value has no function-entry state.
Contract arithmetic is mathematical: ``+``, ``-``, ``*``, ``/``, ``%``, and
unary ``-`` in a contract are exact, while ``proof`` and executable code use
machine integers (see :doc:`integers`).

Examples
--------

``old`` and ``result`` relate the state after the call to the state before,
and bounded quantifiers state facts about every element of a range, or
about one:

.. code-block:: cpp

   void increment(int *p)
     pre(p != nullptr && *p < 1000)
     modifies(*p)
     post(*p == old(*p) + 1)
   {
     *p = *p + 1;
   }

   int index_of(const int *a, int n, int x)
     pre(valid(a, n) && 0 <= n && n <= 1000)
     post(result == -1 || (0 <= result && result < n && a[result] == x))
     post(result != -1 || forall(k, 0, n, a[k] != x))
   {
     for (int i = 0; i < n; i = i + 1)
       invariant(0 <= i && i <= n && forall(k, 0, i, a[k] != x))
       decreases(n - i)
     {
       if (a[i] == x)
         return i;
     }
     return -1;
   }

   proof void has_zero(const int *a, int n)
     pre(valid(a, n) && n >= 3 && a[2] == 0)
     post(exists(k, 0, n, a[k] == 0))
   {
   }

Without bounds a quantifier ranges over every integer, ``trigger`` names
the term that instantiates it, and ``choose`` picks a witness:

.. code-block:: cpp

   spec int sq(int x) { return x * x; }

   proof void sq_nonnegative()
     post(forall(k, sq(k) >= 0))
   {
   }

   proof void positives(const int *a, int n)
     pre(valid(a, n) && n >= 4)
     pre(forall(k, 0, n, trigger(a[k]) > 0))
     post(a[3] > 0)
   {
   }

   spec int half(int n) { return choose(k, 2 * k == n); }

   proof void half_of_ten()
     post(2 * half(10) == 10)
   {
   }

The collections of ``<cppverify.h>`` are values of mathematical integers:

.. code-block:: cpp

   proof void collections(seq s, set a, multiset m, map f)
     post(s.push(7).len() == s.len() + 1 && s.push(7)[s.len()] == 7)
     post(a.insert(3).contains(3) && !a.remove(3).contains(3))
     post(a.subset_of(a.unite(a.insert(4))))
     post(m.insert(5).insert(5).count(5) == m.count(5) + 2)
     post(f.insert(1, 9).contains(1) && f.insert(1, 9)[1] == 9)
   {
   }

.. code-block:: text

   Verified: collections [backend=z3]

``subrange(lo, hi)`` is the half-open slice ``[lo, hi)`` and ``+`` concatenates; equal
lengths and equal elements make two sequences equal:

.. code-block:: cpp

   proof void slices(seq s, seq t)
     pre(s.len() >= 2)
     post(s.subrange(0, 1) + s.subrange(1, s.len()) == s)
     post((s + t).subrange(0, s.len()) == s)
     post(s.subrange(1, s.len()).len() == s.len() - 1)
   {
   }
