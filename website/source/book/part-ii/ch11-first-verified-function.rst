Chapter 11 — Your first verified function
=========================================

We connect Part I’s Hoare triple to CppVerify syntax.

The program
-----------

.. code-block:: cpp

   int abs(int x)
     pre(true)
     post(result >= 0)
   {
     return x < 0 ? -x : x;
   }

- ``pre(true)`` — weakest precondition; any caller may call.
- ``post(result >= 0)`` — ``result`` is the return value (Part I: postcondition).
- The verifier must prove: assuming ``true`` and the implementation, ``result >= 0`` follows.

Run verification
----------------

.. code-block:: bash

   ./build/bin/cpp-verify abs.cpp

What the verifier did (conceptually)
------------------------------------

1. Built a VC: ``true`` and path facts about ``x`` imply ``result >= 0``.
2. Asked Z3: is ``(facts ∧ ¬(result >= 0))`` unsatisfiable?
3. **Unsat** ⇒ verified.

If you return ``x`` unchanged, Z3 finds a model with ``x = -1`` — counterexample.

Compile the same file
---------------------

.. code-block:: bash

   clang++ -std=c++17 -fverify-contracts -c abs.cpp -o abs.o

Verification runs in parallel; ghost code is stripped — no runtime contract overhead.

Larger programs compose **modularly**: callee contracts are assumed at call sites, including nested
calls such as ``return f(g(x))`` (see :doc:`ch17-backends-modular-calls`).

