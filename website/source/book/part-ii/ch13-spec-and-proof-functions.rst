Chapter 13 — Spec and proof functions
=====================================

**Spec** functions (mathematical)
---------------------------------

.. code-block:: cpp

   spec int fibo(int n)
     decreases(n)
   {
     if (n <= 1) return n;
     return fibo(n - 1) + fibo(n - 2);
   }

Use in contracts:

.. code-block:: cpp

   int client(int n)
     pre(n >= 0 && n <= 40)
     post(result == fibo(n));

``fibo`` is not compiled. Integers are **mathematical** (unbounded) inside ``spec``.

**Proof** functions (lemmas)
----------------------------

.. code-block:: cpp

   proof void lemma(int i, int j)
     pre(i <= j)
     post(fibo(i) <= fibo(j))
     decreases(j - i)
   { /* ghost proof */ }

Call from ``ghost { ... }`` blocks in executable functions.

``constexpr`` in contracts
--------------------------

Existing ``constexpr`` helpers work in ``pre``/``post`` with **machine** integer semantics — see :doc:`../../language/integers`.

