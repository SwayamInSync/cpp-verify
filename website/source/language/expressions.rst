Contract expressions
====================

- ``result`` — return value; **postconditions only**
- ``old(expr)`` — pre-state value; **postconditions**
- ``forall(i, lo, hi, body)`` — bounded ∀ over ``i in [lo, hi)``
- ``exists(i, lo, hi, body)`` — bounded ∃ over ``i in [lo, hi)``

Must be contextually ``bool`` where used as conditions.

The range ``[lo, hi)`` may be **symbolic** (e.g. ``forall(i, 0, n, ...)``): a small
concrete range is unrolled, otherwise a real quantifier is emitted with the
half-open bound as the implicit trigger. This is what lets a loop invariant talk
about a whole array range (see :doc:`pointers`).

``old`` is only valid in postconditions (and nested expressions there). ``result`` is only valid
in postconditions. Integer operators follow the function kind: ``spec`` uses mathematical integers;
``proof`` and executable code use machine integers (see :doc:`integers`).