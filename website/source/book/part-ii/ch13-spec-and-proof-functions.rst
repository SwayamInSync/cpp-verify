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

**Fuel** and **hide/reveal** control how much recursive spec body is inlined:

.. code-block:: cpp

   ghost { reveal_with_fuel(fact, 2); }   // bounded unfolding
   ghost { hide(triple); }               // opaque spec application

See also :doc:`ch17-backends-modular-calls`.

``constexpr`` in contracts
--------------------------

Existing ``constexpr`` helpers work in ``pre``/``post`` with **machine** integer semantics — see :doc:`../../language/integers`.

