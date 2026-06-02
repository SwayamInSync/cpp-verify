Contract expressions
====================

- ``result`` — return value; **postconditions only**
- ``old(expr)`` — pre-state value; **postconditions**
- ``forall(i, lo, hi, body)`` — bounded ∀
- ``exists(i, lo, hi, body)`` — bounded ∃

Must be contextually ``bool`` where used as conditions.