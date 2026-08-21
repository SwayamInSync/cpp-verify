Binary search
=============

The overflow-safe midpoint, and the one that is not.

Binary search is the standard example of an algorithm that is easy to state and
easy to get wrong. Jon Bentley's *Programming Pearls* published the broken form
and it stood for two decades; ``java.util.Arrays.binarySearch`` shipped it for
nine years before Joshua Bloch wrote `Nearly All Binary Searches and Mergesorts
Are Broken <https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/>`_
in 2006.

The defect is one line:

.. code-block:: cpp

   int mid = (lo + hi) / 2;

For a large array ``lo + hi`` exceeds ``INT_MAX``. In C++ signed overflow is
undefined behavior, so the program has no defined meaning at all -- the division
never gets the chance to bring the value back into range.

What CppVerify does with it
---------------------------

Nothing in the contract asks for an overflow check. Core expression definedness
is always on, so the encoder generates the obligation itself and it fails:

.. code-block:: text

   error: verification failed: bsearch_broken
     (counterexample: lo = 1073741825, hi = 1073741826)

Those two values sum to 2,147,483,651, which is ``INT_MAX + 4``. The verifier
did not merely report that something might overflow; it produced the concrete
state that does.

Replacing the midpoint with the standard safe form makes the same function
verify:

.. code-block:: cpp

   int mid = lo + (hi - lo) / 2;

What is proved
--------------

For every ``n`` and every input satisfying the precondition:

- termination, via the ``decreases`` clause on the search range;
- memory safety -- every ``a[mid]`` read lies inside the declared extent;
- definedness -- no signed overflow anywhere, the midpoint included;
- the result is ``-1`` or a valid index into the buffer.

What is not proved
------------------

That a non-negative result points at the key, and that ``-1`` means the key is
absent. Both need the array's sortedness as a nested quantifier
(``forall i <= j. a[i] <= a[j]``). The isolated instantiation lemmas verify, but
the inductive loop obligation did not close within 900 seconds. This is
incomplete automation, not a proved property, and it is not claimed as one. See
:doc:`/language/limitations`.

Normalization
-------------

``return mid`` inside the loop is not expressible today -- return statements
inside loops are unsupported -- so a found index is recorded in ``res`` and the
live range is collapsed to end the search. That restructures the control flow,
not the algorithm.

Reproduce
---------

.. code-block:: bash

   ./build/bin/cpp-verify --check-ub clang/test/Verify/suite/binary_search_pass.cpp
   ./build/bin/cpp-verify --check-ub clang/test/Verify/suite/binary_search_overflow_fail.cpp

Both are lit tests in ``clang/test/Verify/suite/``; the second is expected to
fail closed.
