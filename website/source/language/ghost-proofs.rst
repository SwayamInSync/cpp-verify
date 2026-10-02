Ghost, spec, and proofs
=======================

Ghost statements
----------------

- ``ghost { }`` — proof-only block; stripped at compile time
- ``ghost T x = e;`` — ghost variable in the function's scope; later ghost
  code, assertions, and loop invariants may name it, executable code may not
- ``contract_assert(e)`` — emit a verification condition at this point; once
  proved, ``e`` holds for the rest of the function
- ``contract_assert(e) by { ... }`` — prove ``e`` from a local proof whose
  other facts (lemma posts, assertions, locals) do not escape it
- ``contract_assert(forall(k, lo, hi, p)) by { ... }`` — prove ``p`` for one
  arbitrary ``k`` in ``[lo, hi)``, which the block may read but not assign;
  the ``forall`` holds afterwards
- ``calc { e0; op { ... } e1; ... }`` — a chain of steps, each proved like
  an assert-by, concluding the combined relation between ``e0`` and the last
  term
- ``reveal_with_fuel(f, n)`` — unfold recursive spec ``f`` up to depth ``n`` (ghost blocks only)
- ``reveal(f)`` / ``hide(f)`` — make spec ``f`` transparent / opaque for the rest of the
  enclosing function (ghost blocks only)

Because a ghost block is erased, it cannot change anything observed by the
compiled program. Assignments are limited to variables declared inside ghost
code (including their direct ``.field`` members). Writes through pointers,
references to global state, calls to executable functions, and ``return`` from
the enclosing function are rejected. A loop in ghost code must carry a
``decreases`` clause so nontermination cannot make the executable continuation
unreachable only in the proof model.

Spec and proof functions
------------------------

- ``spec`` / ``proof`` functions are **not compiled** — their bodies are definitions/lemmas
  for the verifier only.
- A ``spec`` function may be called only from contracts, ghost code, and other ``spec`` or
  ``proof`` functions. Clang rejects a reference from executable code (a function body, an
  initializer, a default argument), which would otherwise fail to link.
- ``spec`` integers are **mathematical** (unbounded ``Int``); ``proof`` integers are machine.
  Storing a spec result in a ghost or ``proof`` variable converts it to that machine type, and
  the value must fit (see :doc:`integers`).
- ``recommends(expr)`` (``spec`` only) is a **soft** precondition: it does not generate call-site
  obligations, but the verifier warns when a call may not satisfy it.

Proof functions may update their own local values and call other proof
functions, but cannot write executable memory/global state or call executable
functions. Their loops require ``decreases`` just like recursive proof calls.

.. code-block:: cpp

   spec int safe_div(int a, int b)
     recommends(b != 0)
   { return a / b; }

Specs that read memory
----------------------

A ``spec`` may read memory through its pointer parameters, for example to
specify a reduction. It must not write memory. The verifier evaluates each call
in the heap state a load at that point would read: the current state, the
entry state inside ``old(...)``, and the call-site state when a callee contract
is instantiated.

.. code-block:: cpp

   spec int sum(const int* p, int n) decreases(n)
   { if (n <= 0) return 0; return sum(p, n - 1) + p[n - 1]; }

   int total(const int* p, int n)
     pre(n >= 0 && n <= 1000 && valid(p, n))
     pre(forall(j, 0, n, -1000 <= p[j] && p[j] <= 1000))
     post(result == sum(p, n))
   {
     int acc = 0, i = 0;
     while (i < n)
       invariant(0 <= i && i <= n && acc == sum(p, i))
       invariant(-1000 * i <= acc && acc <= 1000 * i)
       decreases(n - i)
     { acc = acc + p[i]; i = i + 1; }
     return acc;
   }

A heap-reading spec has no ``reads`` frame yet: after a write, the verifier
relates the new value to the old one only by unfolding the definition, so a
symbolic-length reduction is not automatically preserved across unrelated
writes.

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
