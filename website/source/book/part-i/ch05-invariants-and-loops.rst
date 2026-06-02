Chapter 5 — Invariants and loops
=================================

Loops repeat. Testing loops samples a few iteration counts; verification needs a **single formula**
true on every iteration — a **loop invariant**.

The three obligations
---------------------

For loop condition ``cond``, invariant ``I``, and body ``B``:

.. figure:: /_static/diagrams/loop-invariant-lifecycle.svg
   :align: center
   :figclass: book-figure
   :alt: Loop invariant establishment at entry, preservation each iteration, exit when I and not cond

1. **Establishment** — ``I`` holds when we first reach the loop.
2. **Preservation** — if ``I`` and ``cond`` hold, running one iteration of ``B`` yields ``I`` again.
3. **Exit** — when the loop stops, we have ``I`` and ``not cond``. That is what we use to prove goals after the loop.

Example: ascending index
------------------------

.. code-block:: cpp

   int i = 0;
   while (i < n) {
     // body uses i
     i++;
   }

A typical invariant: ``0 <= i && i <= n``.

- **Establishment:** ``i == 0`` gives ``0 <= i`` and ``i <= n`` if ``n >= 0``.
- **Preservation:** if ``i < n``, after ``i++`` still ``i <= n`` and ``i`` increased.
- **Exit:** ``i >= n`` and ``i < n`` false ⇒ ``i == n``.

Finding invariants
------------------

Invariants are the creative part of loop proofs. Strategies:

- **Define a relation** between variables (``s == sum of first i elements``).
- **Bounds** on indices (``0 <= i <= n``).
- **Copy of the post** — sometimes the postcondition, weakened, is invariant.

Too weak an invariant fails **preservation**; too strong fails **establishment**.

Termination measures
--------------------

Invariants alone give **partial** correctness. To prove the loop **terminates**, use a
**variant** (termination measure) that:

- Is bounded below (often ``>= 0``)
- **Strictly decreases** each iteration while the loop runs

Example: ``decreases(n - i)`` in a loop where ``i`` increases toward ``n``.

CppVerify will check both invariant preservation and measure decrease (Part II).

