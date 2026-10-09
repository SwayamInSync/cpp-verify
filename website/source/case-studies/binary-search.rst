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

.. cppverify-example: fragment

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

   error: verification failed: bsearch_broken [...::overflow@...]
     (counterexample: lo = 1073741824, hi = 1073741824)

Those two values sum to 2,147,483,648, which is ``INT_MAX + 1``. The verifier
did not merely report that something might overflow; it named the check that
fails and produced the concrete state that breaks it. The solver chooses the
witness, so another version may report a different pair with the same
overflow.

Replacing the midpoint with the standard safe form makes the same function
verify:

.. cppverify-example: fragment

.. code-block:: cpp

   int mid = lo + (hi - lo) / 2;

What is proved
--------------

For every ``n`` and every input satisfying the precondition:

- termination, via the ``cppverify::decreases`` clause on the search range;
- memory safety -- every ``a[mid]`` read lies inside the declared extent;
- definedness -- no signed overflow anywhere, the midpoint included;
- the result is ``-1`` or a valid index into the buffer.

This is what ``binary_search_pass.cpp`` proves. Its contract does not say
that a non-negative result points at the key, or that ``-1`` means the key is
absent.

The full functional specification
---------------------------------

The full functional specification verifies too, in about a second. Section
"Universal statements: sorted arrays" of
:doc:`/book/part-ii/ch20-mathematics-to-code` proves it: sortedness is the
precondition ``cppverify::forall(i, 0, n, cppverify::forall(j, i, n, a[i] <= a[j]))``,
the postcondition is
``cppverify::result >= 0 ? a[cppverify::result] == x : cppverify::forall(k, 0, n, a[k] != x)``,
and the loop returns ``mid`` when it finds the key.

Reproduce
---------

.. code-block:: bash

   ./build/bin/cpp-verify clang/test/Verify/suite/binary_search_pass.cpp
   ./build/bin/cpp-verify clang/test/Verify/suite/binary_search_overflow_fail.cpp

Both are lit tests in ``clang/test/Verify/suite/``; the second is expected to
fail closed.
