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

If ``a`` and ``b`` alias (the same address), this swap still leaves the value as it was, which is
what swapping a value with itself means. Code that combines the two values is less forgiving, as
the swap by sums at the end of this chapter shows. Callers must know whether ``&x`` and ``&y`` are
distinct.

Frame conditions (``cppverify::modifies``)
------------------------------------------

A **frame** lists what a function may change. Anything **not** listed should be unchanged (in the model).

The swap with its contract:

.. code-block:: cpp

   void swap(int *a, int *b)
     cv::pre(a != nullptr && b != nullptr)
     cv::modifies(*a, *b)
     cv::post(*a == cv::old(*b) && *b == cv::old(*a))
   {
     int t = *a; *a = *b; *b = t;
   }

.. code-block:: text

   Verified: swap [backend=z3]

``cppverify::old`` refers to the pre-call heap/value. The frame tells callers ``*c`` for unrelated ``c`` is untouched.

Heap models (conceptual)
------------------------

Many verifiers model memory as a **map** from addresses to values:

- Read ``*p`` ≈ lookup at ``p``
- Write ``*p = v`` ≈ update map at ``p``

CppVerify uses array theory in Z3 internally (Part II). You write normal C++; the heap is implicit.

Default non-aliasing
--------------------

To keep call-site proofs tractable, CppVerify assumes that two pointer or reference parameters
address different objects when at least one of them is mutable, and each caller must show it; a
caller of ``swap`` above that passes one pointer twice, ``swap(p, p)``, fails its call's
``aliasing`` check.
``cppverify::aliases(p, q)`` opts a pair out, and the body must then be correct when they are the
same. The swap by sums is not:

.. cppverify-example: fails swap_by_sums

.. code-block:: cpp

   void swap_by_sums(int *a, int *b)
     cv::aliases(a, b)
     cv::pre(a != nullptr && b != nullptr)
     cv::pre(0 <= *a && *a <= 1000 && 0 <= *b && *b <= 1000)
     cv::modifies(*a, *b)
     cv::post(*a == cv::old(*b) && *b == cv::old(*a))
   {
     *a = *a + *b; *b = *a - *b; *a = *a - *b;
   }

.. code-block:: text

   sums.cpp:6:30: error: verification failed: swap_by_sums [postcondition] [backend=z3] [reason=counterexample]
       6 |   cv::post(*a == cv::old(*b) && *b == cv::old(*a))
         |            ~~~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~
   sums.cpp:6:30: note: counterexample: a = 1, b = 1
   sums.cpp:8:6: note: stores 2000 at address 1
       8 |   *a = *a + *b; *b = *a - *b; *a = *a - *b;
         |      ^
   sums.cpp:8:20: note: stores 0 at address 1
       8 |   *a = *a + *b; *b = *a - *b; *a = *a - *b;
         |                    ^
   sums.cpp:8:34: note: stores 0 at address 1
       8 |   *a = *a + *b; *b = *a - *b; *a = *a - *b;
         |                                  ^

With ``a == b`` the first statement doubles the value and the second sets it to 0.

