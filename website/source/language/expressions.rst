Contract expressions
====================

- ``result`` — return value; **postconditions only**
- ``old(expr)`` — pre-state value; **postconditions**
- ``forall(i, lo, hi, body)`` — bounded ∀
- ``exists(i, lo, hi, body)`` — bounded ∃

Must be contextually ``bool`` where used as conditions.

``old`` is only valid in postconditions (and nested expressions there). ``result`` is only valid
in postconditions. Integer operators follow the function kind: ``spec`` uses mathematical integers;
``proof`` and executable code use machine integers (see :doc:`integers`).