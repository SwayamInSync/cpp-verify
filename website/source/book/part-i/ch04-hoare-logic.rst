Chapter 4 — Hoare logic
=======================

**Hoare logic** (Tony Hoare, 1969) is the standard way to attach logical formulas to programs.
The central object is the **Hoare triple**.

The Hoare triple
----------------

.. figure:: /_static/diagrams/hoare-triple.svg
   :align: center
   :figclass: book-figure
   :alt: Hoare triple with precondition P, statement S, and postcondition Q

Written :math:`\{P\}\,S\,\{Q\}`:

- ``P`` — **precondition** (what we assume before ``S`` runs)
- ``S`` — a statement or sequence
- ``Q`` — **postcondition** (what we guarantee after ``S`` finishes, if it terminates)

**Partial correctness:** we do not promise termination yet; we promise *if* ``S`` terminates and ``P`` held at the start, then ``Q`` holds at the end.

Assignment rule (intuition)
---------------------------

After ``x = e``, any fact that mentions ``x`` must be updated. The classic **weakest precondition**
of assignment ``x := e`` with postcondition ``Q`` is:

.. code-block:: text

   Q[x := e]   // substitute e for x in Q

Example: after ``x = y + 1``, to know ``x > 0``, it suffices to know ``y + 1 > 0`` beforehand.

Sequence rule
-------------

If :math:`\{P\}S_1\{R\}` and :math:`\{R\}S_2\{Q\}`, then :math:`\{P\}S_1; S_2\{Q\}`.
The intermediate formula ``R`` links the two steps — often the post of the first equals the pre of the second.

Conditional rule
----------------

To prove :math:`\{P\}\textbf{if }(c)\,S_1\textbf{ else }S_2\{Q\}`:

- Prove :math:`\{P \land c\}S_1\{Q\}`
- Prove :math:`\{P \land \lnot c\}S_2\{Q\}`

This matches how you reason about ``if/else`` on paper.

Modular function calls
----------------------

For a call to ``f`` with contract ``requires P_f``, ``ensures Q_f``:

- **Caller** must prove the precondition ``P_f`` at the call site.
- **Caller** may assume ``Q_f`` after the call (with return value wired to ``result`` in CppVerify).

.. figure:: /_static/diagrams/modular-verification.svg
   :align: center
   :figclass: book-figure
   :alt: Caller proves callee precondition and assumes postcondition; callee proves body separately

The callee’s **source body is not needed** at the call site — only its contract. That is how large programs scale.

