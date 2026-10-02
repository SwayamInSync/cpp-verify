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
