Chapter 7 — Memory, aliasing, and frame conditions
==================================================

Pointers make two programs **interact through memory**. Verification must say not only *what*
values are returned, but *what memory changed*.

Two pointers **alias** if they refer to overlapping storage (``p == q`` or ``p`` points into the same array as ``q``).

Why aliasing matters
--------------------

.. code-block:: cpp

   void swap(int* a, int* b) {
     int t = *a; *a = *b; *b = t;
   }

If ``a`` and ``b`` alias (same address), the “swap” fails. Callers must know whether ``&x`` and ``&y`` are distinct.

Frame conditions (``modifies``)
-------------------------------

A **frame** lists what a function may change. Anything **not** listed should be unchanged (in the model).

Example contract shape:

.. code-block:: text

   modifies(*a, *b)
   post(*a == old(*b) && *b == old(*a))

``old`` refers to the pre-call heap/value. The frame tells callers ``*c`` for unrelated ``c`` is untouched.

Heap models (conceptual)
------------------------

Many verifiers model memory as a **map** from addresses to values:

- Read ``*p`` ≈ lookup at ``p``
- Write ``*p = v`` ≈ update map at ``p``

CppVerify uses array theory in Z3 internally (Part II). You write normal C++; the heap is implicit.

Default non-aliasing
--------------------

To keep call-site proofs tractable, CppVerify assumes distinct **mutable** pointer parameters do not alias unless you opt out with ``aliases(p, q)``.

