Chapter 14 — Pointers, frames, and modifies
===========================================

Apply Part I’s frame and aliasing ideas in C++.

Swap with contract
------------------

.. code-block:: cpp

   void swap(int* a, int* b)
     pre(a != nullptr && b != nullptr)
     modifies(*a, *b)
     post(*a == old(*b) && *b == old(*a))
   {
     int t = *a; *a = *b; *b = t;
   }

``old(*b)`` is the value at ``b`` at function entry.

Aliasing
--------

- Distinct mutable pointer parameters are assumed **non-aliased** by default.
- Use ``aliases(dst, src)`` when aliasing is allowed.

Buffers and arrays
------------------

Pointer arithmetic (``*(p + i)``) and subscripting (``p[i]``) read and write
indexed heap locations. The heap maps addresses to values, so distinct indices
are distinct cells: a store to ``p[k]`` leaves ``p[i]`` alone whenever ``i != k``.
``modifies(*p)`` frames the whole region reachable through ``p``.

To state a property of a whole range, put a **bounded quantifier** in the loop
invariant and the postcondition — the half-open bound ``[lo, hi)`` is the trigger.
A buffer-zeroing loop proves its full postcondition this way:

.. code-block:: cpp

   void zero(int* p, int n)
     pre(p != nullptr && n >= 0 && n <= 1000)
     modifies(*p)
     post(forall(i, 0, n, p[i] == 0))
   {
     int j = 0;
     while (j < n)
       invariant(0 <= j && j <= n && forall(i, 0, j, p[i] == 0))
       decreases(n - j)
     { p[j] = 0; j = j + 1; }
   }

The invariant ``forall(i, 0, j, p[i] == 0)`` says "everything written so far is
zero"; preservation across the store uses the disjointness of ``p[j]`` from each
earlier ``p[i]``, and at exit (``j == n``) it yields the postcondition.

A subtle point shows up when a loop relates **two** buffers, as in a copy:

.. code-block:: cpp

   // copying d from s is correct only when the ranges do not overlap -- which is
   // exactly why the C standard library has both memcpy and memmove.
   pre(... && (d + n <= s || s + n <= d))   // explicit non-overlap

Without that precondition the verifier is right to reject the copy: a store to
``d[j]`` could clobber some ``s[i]`` still to be read. (Copy loops may also report
``unknown`` for now — the two-buffer quantified reasoning needs solver trigger
guidance that is still being tuned.)

Type invariants
---------------

A ``type_invariant`` attaches a property to a struct that every function may assume of its
parameters — a frame condition on *values* rather than memory. Declare it after the fields it names:

.. code-block:: cpp

   struct Point {
     int x;
     int y;
     type_invariant(x >= 0 && x <= 1000 && y >= 0 && y <= 1000);
   };

   int sum(Point p)
     post(result >= 0 && result <= 2000)
   { return p.x + p.y; }            // the invariant on x, y is assumed here

It is injected as a precondition at the first use of an invariant field, for by-value and reference
parameters, so callers must establish it. See :doc:`../../language/structs`.

See :doc:`../../language/limitations` for the supported pointer and heap feature set.

