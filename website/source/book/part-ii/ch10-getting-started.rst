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
To compile (or just syntax-check) without running the solver, use ``-fno-verify`` — it skips the
SMT step and implies ``-fverify-contracts``, giving a fast syntax/semantics-only check
(see :doc:`../../language/tooling`).