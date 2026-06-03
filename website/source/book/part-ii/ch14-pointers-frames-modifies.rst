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

