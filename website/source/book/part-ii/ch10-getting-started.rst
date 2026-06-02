Chapter 10 — Getting started
============================

After :doc:`../../index` (install), you will have ``cpp-verify`` and ``clang++`` under ``build/bin/``.

Verify a source file:

.. code-block:: bash

   ./build/bin/cpp-verify myfile.cpp

Compile with contract checking enabled:

.. code-block:: bash

   ./build/bin/clang++ -std=c++17 -fverify-contracts -c myfile.cpp -o myfile.o

Contract keywords require ``-fverify-contracts``. The standalone verifier enables it automatically.
To compile without running the solver, add ``-fno-verify`` (see :doc:`../../language/tooling`).