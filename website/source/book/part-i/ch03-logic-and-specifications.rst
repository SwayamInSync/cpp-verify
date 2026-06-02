Chapter 3 — Logic and specifications
====================================

Specifications are written in **logic**: formulas built from comparisons, Boolean connectives,
and quantifiers. The patterns below recur throughout the rest of the book.

Predicates and states
---------------------

A **predicate** is a formula that can be true or false depending on variable values.
A **program state** assigns values to variables (``x = 3``, ``y = -1``, …).

Example predicates about integers ``x`` and ``y``:

.. code-block:: text

   x >= 0
   x < y
   x >= 0 && y >= 0        // conjunction (AND)
   x == 0 || y == 0        // disjunction (OR)
   !(x == y)                 // negation (NOT)

Implication — the heart of contracts
------------------------------------

**Implication** :math:`P \Rightarrow Q` reads “if ``P`` then ``Q``.”

- When ``P`` is false, the implication is **vacuously true** (we make no promise in impossible worlds).
- When ``P`` is true, ``Q`` must hold.

Function contracts will have the shape:

.. code-block:: text

   precondition P  ==>  (code ensures) postcondition Q

Equivalently: **every call** that satisfies ``P`` must leave the world satisfying ``Q`` (if the call terminates).

Quantifiers (preview)
---------------------

To say “every element of the array is non-negative”:

.. code-block:: text

   forall i in [0, n) . arr[i] >= 0

To say “there exists an index with value ``target``”:

.. code-block:: text

   exists i in [0, n) . arr[i] == target

CppVerify uses bounded ``forall`` / ``exists`` syntax in contracts; the idea is standard first-order logic
over integers and arrays.

Abstraction in specifications
-----------------------------

Good specifications are **stable** under implementation changes:

.. list-table::
   :header-rows: 1

   * - Too concrete
     - Better
   * - ``result == (x < 0 ? -x : x)``
     - ``result >= 0``
   * - “uses a while loop”
     - “returns the sum of 0..n”

Abstract specs let you replace algorithms without changing callers’ proofs.

