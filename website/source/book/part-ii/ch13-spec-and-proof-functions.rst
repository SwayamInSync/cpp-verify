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

Soft preconditions (``recommends``)
-----------------------------------

A ``spec`` function stays **total**, but ``recommends`` flags likely misuse. It generates no
call-site obligation; the verifier only **warns** when a call may violate it:

.. code-block:: cpp

   spec int safe_div(int a, int b)
     recommends(b != 0)
   { return a / b; }

Opacity: fuel, ``reveal``, ``hide``
-----------------------------------

A recursive ``spec`` is opaque by default (unfolded with fuel 1) so its axiom does not send Z3 into
a matching loop; ``reveal_with_fuel(f, n)`` raises the depth when a proof needs more (the ``safe_fib``
walkthrough uses it). ``reveal`` / ``hide`` toggle a spec's transparency for the rest of a function:

.. code-block:: cpp

   spec int triple(int x) { return 3 * x; }

   int f(int x)
     pre(x >= 0 && x <= 10)
     post(result == triple(x))
   {
     ghost { reveal(triple); }            // reveal_with_fuel(f, n) for recursive specs
     return x + x + x;
   }

   int g(int x)
     pre(x >= 0 && x <= 10)
     post(result == x + x + x)
   {
     ghost { hide(triple); }              // keep triple opaque; prove without unfolding it
     return x + x + x;
   }

See also :doc:`ch17-backends-modular-calls`.

``constexpr`` as spec
---------------------

Any ``constexpr`` function is usable in ``pre``/``post`` **directly** — no separate ``spec``
re-declaration:

.. code-block:: cpp

   constexpr int square(int x) { return x * x; }

   int area(int side)
     pre(side >= 0 && side <= 1000)
     post(result == square(side))
   { return side * side; }

One body does double duty: the same ``constexpr`` runs at execution time and defines the spec, so
the two can never silently diverge (Verus requires a separate ``spec fn``). A lifted ``constexpr``
keeps **machine** integer semantics — honest overflow — unlike an explicit ``spec`` (mathematical
``Int``); see :doc:`../../language/integers`.

