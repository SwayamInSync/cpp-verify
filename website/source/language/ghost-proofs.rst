Ghost, spec, and proofs
=======================

Ghost statements
----------------

- ``ghost { }`` — proof-only block; stripped at compile time
- ``contract_assert(e)`` — emit a verification condition at this point
- ``reveal_with_fuel(f, n)`` — unfold recursive spec ``f`` up to depth ``n`` (ghost blocks only)
- ``reveal(f)`` / ``hide(f)`` — make spec ``f`` transparent / opaque for the rest of the
  enclosing function (ghost blocks only)

Spec and proof functions
------------------------

- ``spec`` / ``proof`` functions are **not compiled** — their bodies are definitions/lemmas
  for the verifier only.
- ``spec`` integers are **mathematical** (unbounded ``Int``); ``proof`` integers are machine.
- ``recommends(expr)`` (``spec`` only) is a **soft** precondition: it does not generate call-site
  obligations, but the verifier warns when a call may not satisfy it.

.. code-block:: cpp

   spec int safe_div(int a, int b)
     recommends(b != 0)
   { return a / b; }

Opacity and fuel
----------------

A recursive ``spec`` is **opaque** by default (unfolded with fuel 1) so its defining axiom does not
send Z3 into a matching loop; ``reveal_with_fuel(f, n)`` raises the depth when a proof needs more.
``reveal`` / ``hide`` toggle a spec's transparency for the rest of a function:

.. code-block:: cpp

   int f(int x)
     pre(x >= 0 && x <= 10)
     post(result == triple(x))
   {
     ghost { reveal(triple); }   // hide(triple) makes it opaque again
     return x + x + x;
   }

``constexpr`` as spec
---------------------

Any ``constexpr`` function is usable directly in contracts — no separate ``spec`` declaration. It
keeps **machine** integer semantics (see :doc:`integers`):

.. code-block:: cpp

   constexpr int square(int x) { return x * x; }

   int area(int side)
     pre(side >= 0 && side <= 1000)
     post(result == square(side))
   { return side * side; }
