Ghost, spec, and proofs
=======================

Ghost statements
----------------

- ``cppverify::ghost { }`` — proof-only block; stripped at compile time
- ``cppverify::ghost T x = e;`` — ghost variable in the function's scope; later ghost
  code, assertions, and loop invariants may name it, executable code may not
- ``cppverify::check(e)`` — emit a verification condition at this point; once
  proved, ``e`` holds for the rest of the function
- ``cppverify::check(e) by { ... }`` — prove ``e`` from a local proof whose
  other facts (lemma posts, assertions, locals) do not escape it
- ``cppverify::check(cppverify::forall(k, lo, hi, p)) by { ... }`` — prove ``p`` for one
  arbitrary ``k`` in ``[lo, hi)``, which the block may read but not assign;
  the ``cppverify::forall`` holds afterwards
- ``cppverify::calc { e0; op { ... } e1; ... }`` — a chain of steps, each proved like
  an assert-by, concluding the combined relation between ``e0`` and the last
  term
- ``cppverify::reveal_with_fuel(f, n)`` — unfold recursive spec ``f`` up to depth ``n``,
  or an inductive predicate ``f`` ``n`` levels below each application a proof
  names, in the whole enclosing function; a statement accepted anywhere in a
  function body, inside a ghost block or not
- ``cppverify::reveal(f)`` / ``cppverify::hide(f)`` — make spec ``f`` transparent / opaque in the whole
  enclosing function, wherever the statement appears in its body (inside a
  ghost block or not)

Because a ghost block is erased, it cannot change anything observed by the
compiled program. Assignments are limited to variables declared inside ghost
code (including their direct ``.field`` members). Writes through pointers,
references to global state, calls to executable functions, and ``return`` from
the enclosing function are rejected. A loop in ghost code must carry a
``cppverify::decreases`` clause so nontermination cannot make the executable continuation
unreachable only in the proof model.

.. code-block:: cpp

   cv::spec int sq(int x) { return x * x; }

   cv::proof void sq_monotone(int a, int b)
     cv::pre(0 <= a && a <= b)
     cv::post(sq(a) <= sq(b))
   {
   }

   void ordered_squares(int a, int b)
     cv::pre(0 <= a && a <= b && b <= 1000)
   {
     cv::check(a <= b);
     cv::check(sq(a) <= sq(b)) by { sq_monotone(a, b); }
     cv::ghost { int t = sq(b); cv::check(t >= 0); }
   }

   cv::proof void pair_ordered(const int *a, int n, int i, int j)
     cv::pre(valid(a, n) && n <= 1000 && 0 <= i && i <= j && j < n)
     cv::pre(cv::forall(k, 0, n - 1, a[k] <= a[k + 1]))
     cv::post(a[i] <= a[j])
     cv::decreases(j - i)
   {
     if (i < j)
       pair_ordered(a, n, i, j - 1);
   }

   void last_is_largest(const int *a, int n)
     cv::pre(valid(a, n) && 1 <= n && n <= 1000)
     cv::pre(cv::forall(k, 0, n - 1, a[k] <= a[k + 1]))
   {
     cv::check(cv::forall(k, 0, n, a[k] <= a[n - 1])) by {
       pair_ordered(a, n, k, n - 1);
     }
   }

   void chain(int a, int b, int c)
     cv::pre(0 <= a && a <= b && b <= c && c <= 1000)
   {
     cv::calc {
       sq(a);
       <= { sq_monotone(a, b); }
       sq(b);
       <= { sq_monotone(b, c); }
       sq(c);
     }
     cv::check(sq(a) <= sq(c));
   }

In ``last_is_largest`` the block proves the body for one ``k``, and the
``cppverify::forall`` holds after it; the lemma's own facts stay inside the block.

Spec and proof functions
------------------------

- ``cppverify::spec`` / ``cppverify::proof`` functions are **not compiled** — their bodies are definitions/lemmas
  for the verifier only.
- A ``cppverify::spec`` function may be called only from contracts, ghost code, and other ``cppverify::spec`` or
  ``cppverify::proof`` functions. Clang rejects a reference from executable code (a function body, an
  initializer, a default argument), which would otherwise fail to link.
- ``cppverify::spec`` integers are **mathematical** (unbounded ``Int``); ``cppverify::proof`` integers are machine.
  Storing a spec result in a ghost or ``cppverify::proof`` variable converts it to that machine type, and
  the value must fit (see :doc:`integers`).
- ``cppverify::recommends(expr)`` (``cppverify::spec`` only) is a **soft** precondition: it does not generate call-site
  obligations; when an executable function that calls the spec fails verification, the verifier
  warns where a call in it may not satisfy it.
- ``cppverify::post(expr)`` on a ``cppverify::spec`` is proved with its termination, by well-founded induction on its
  measure, and then holds at every application: those a proof names and those inside the
  unfoldings it receives (``fib(j - 2) >= 0`` from the unfolding of ``fib(j)``), as Dafny's
  function postconditions do. See :doc:`../book/part-ii/ch13-spec-and-proof-functions`.

Proof functions may update their own local values and call other proof
functions, but cannot write executable memory/global state or call executable
functions. Their loops require ``cppverify::decreases`` just like recursive proof calls.

.. code-block:: cpp

   cv::spec int safe_div(int a, int b)
     cv::recommends(b != 0)
   { return a / b; }

``cppverify::when(c)`` restricts where the body defines a spec: outside ``c`` its value
is left open (an uninterpreted function of its arguments), and termination
is checked only inside:

.. code-block:: cpp

   cv::spec int safe_inverse(int x)
     cv::when(x != 0)
   {
     return 1000 / x;
   }

   cv::proof void inverse_of_ten()
     cv::post(safe_inverse(10) == 100)
   {
   }

Specs that read memory
----------------------

A ``cppverify::spec`` may read memory through its pointer parameters, for example to
specify a reduction. It must not write memory. The verifier evaluates each call
in the heap state a load at that point would read: the current state, the
entry state inside ``cppverify::old(...)``, and the call-site state when a callee contract
is instantiated.

.. code-block:: cpp

   cv::spec int sum(const int* p, int n) cv::decreases(n)
   { if (n <= 0) return 0; return sum(p, n - 1) + p[n - 1]; }

   int total(const int* p, int n)
     cv::pre(n >= 0 && n <= 1000 && valid(p, n))
     cv::pre(cv::forall(j, 0, n, -1000 <= p[j] && p[j] <= 1000))
     cv::post(cv::result == sum(p, n))
   {
     int acc = 0, i = 0;
     while (i < n)
       cv::invariant(0 <= i && i <= n && acc == sum(p, i))
       cv::invariant(-1000 * i <= acc && acc <= 1000 * i)
       cv::decreases(n - i)
     { acc = acc + p[i]; i = i + 1; }
     return acc;
   }

Without a frame, that a reduction over a symbolic length keeps its value
across an unrelated write must be proved by induction over the spec, which
the verifier tries automatically at a cost in solver time.
``cppverify::reads(p, n)`` declares the cells ``p[0..n)`` the spec depends on and
gives that fact directly. The verifier checks it against the body (every
load, and every range a heap-reading callee reads, lies inside), and callers
then keep every application across a store outside those cells without
unfolding:

.. code-block:: cpp

   cv::spec int sum_of(const int *p, int n)
     cv::reads(p, n)
     cv::decreases(n)
   {
     return n <= 0 ? 0 : sum_of(p, n - 1) + p[n - 1];
   }

   void unrelated(int *p, int n, int *q)
     cv::pre(valid(p, n) && 0 <= n && n <= 1000 && q != nullptr)
     cv::modifies(*q)
     cv::post(sum_of(p, n) == cv::old(sum_of(p, n)))
   {
     *q = 0;
   }

``q`` is a different object from ``p``'s buffer (distinct mutable pointer
parameters do not alias), so the store lies outside the frame. A failed
``cppverify::reads`` check is reported as ``spec reads failed: f`` for a spec ``f``, and every proof that
relied on the frame is ``Unresolved`` with reason ``spec.reads``.

Opacity and fuel
----------------

A recursive ``cppverify::spec`` is **opaque** by default (unfolded with fuel 1) so its defining axiom does not
send Z3 into a matching loop; ``cppverify::reveal_with_fuel(f, n)`` raises the depth when a proof needs more.
``cppverify::reveal`` / ``cppverify::hide`` make a spec transparent / opaque in the whole function,
wherever the statement appears:

.. code-block:: cpp

   cv::spec int triple(int x) { return x + x + x; }

   int f(int x)
     cv::pre(x >= 0 && x <= 10)
     cv::post(cv::result == triple(x))
   {
     cv::ghost { cv::reveal(triple); }
     return x + x + x;
   }

   int g(int x)
     cv::pre(x >= 0 && x <= 10)
     cv::post(cv::result == 3 * x)
   {
     cv::ghost { cv::hide(triple); }   // this proof needs no definition of triple
     return x + x + x;
   }

With fuel 1 a proof sees one unfolding of each application it names, so
``pow2(3) == 8`` needs three more:

.. code-block:: cpp

   cv::spec int pow2(int n) cv::decreases(n) { return n <= 0 ? 1 : 2 * pow2(n - 1); }

   void eight()
   {
     cv::ghost { cv::reveal_with_fuel(pow2, 4); }
     cv::check(pow2(3) == 8);
   }

Fuel is local to the function that raises it. For an inductive predicate,
``cppverify::reveal_with_fuel(P, n)`` unfolds the applications inside its unfoldings
``n`` levels deep, and the verifier also deepens on its own, up to four
levels, when a verdict still depends on the predicate (see
:ref:`inductive predicates <inductive-predicates>`).

Proof blocks for spec clauses
-----------------------------

A spec's ``cppverify::post``, ``cppverify::decreases``, and ``cppverify::reads`` clauses are checked by the
verifier, and a spec body is an expression with no room for proof steps. A
proof block gives them room: ``cppverify::post(Q) by { ... }`` runs ghost code in the
check of ``Q``, after the facts that check assumes and before its
obligations.

.. code-block:: cpp

   cv::spec int mul(int a, int b) cv::decreases(b) { return b <= 0 ? 0 : mul(a, b - 1) + a; }

   cv::proof void mul_is(int a, int b)
     cv::post(b < 0 || mul(a, b) == a * b)
     cv::decreases(b)
   {
     if (b > 0)
       mul_is(a, b - 1);
   }

   // Commutativity of mul: the solver needs the lemma at both orders.
   cv::spec int area(int a, int b)
     cv::post(a < 0 || b < 0 || cv::result == mul(b, a)) by { mul_is(a, b); mul_is(b, a); }
   {
     return mul(a, b);
   }

   // Termination by a measure the lemma explains.
   cv::spec int zig(int a, int b)
     cv::decreases(mul(a, b)) by { if (a > 0 && b > 0) { mul_is(a, b); mul_is(b - 1, a); } }
   {
     return a <= 0 || b <= 0 ? 0 : 1 + zig(b - 1, a);
   }

- In a ``cppverify::post`` block, ``cppverify::result`` is the value the body returns.
- Naming the spec at a smaller measure in a block, as in
  ``cppverify::check(tri(n - 1) >= 0);``, uses the induction hypothesis
  there; at a measure that is not smaller it assumes nothing.
- The block is ghost code: it may declare and assign its own locals,
  branch, assert, and call proof functions, whose preconditions it must
  establish. It cannot return, write memory, or assign a parameter.
- Only a spec's definition takes proof blocks; other functions put their
  proof in their bodies.
- A block may use a lemma about the spec itself when both have
  ``cppverify::decreases`` clauses of one length (a cluster, as in Dafny): the block's
  call must lower the measure, and the lemma uses the spec's definition and
  postcondition only where the spec's measure is below the lemma's. With
  ``cppverify::decreases(n, 0)`` on the spec and ``cppverify::decreases(n, 1)`` on the lemma, the
  lemma unfolds the spec at ``n`` and the block calls the lemma at
  ``n - 1``. Without shared measures, proofs that rest on each other are
  ``Unresolved`` with reason ``proof.cycle``.

.. _inductive-predicates:

Inductive predicates
--------------------

``cppverify::inductive`` makes a ``cppverify::spec`` returning ``bool`` the *least* predicate its
body defines, as Dafny's ``least predicate``: it holds exactly where a finite
derivation shows it, so it needs no ``cppverify::decreases``.

.. code-block:: cpp

   cv::spec bool even(int n)
     cv::inductive
     cv::post(!cv::result || (n >= 0 && n % 2 == 0))
   {
     return n == 0 || even(n - 2);
   }

- ``even(-2)`` is false: it would need ``even(-4)``, and so on forever, which
  no finite derivation provides.
- The body returns a condition (under ``if``/``else`` at most) in which the
  predicate occurs only positively: as a conjunct or disjunct, a branch of
  ``?:``, under ``cppverify::exists``, or under a bounded ``cppverify::forall``. It takes no
  ``cppverify::decreases`` or ``cppverify::when``, and it may read memory (each application is
  unfolded in the memory state it is applied in). Predicates that apply
  each other are defined together; a predicate never applies itself through
  a spec that is not inductive.
- Proofs see the predicate through its body, unfolded once at each
  application, both ways: naming an application, as in
  ``cppverify::check(even(2));``, unfolds it to ``2 == 0 || even(0)``.
- The verifier unfolds further where a verdict needs it. An application at
  constant arguments, such as ``cppverify::post(even(4))``, is decided before solving,
  and the solver receives the unfoldings along the derivation found. A
  verdict that still depends on the predicate is retried with the
  applications inside the unfoldings unfolded as well, one level more at a
  time, up to four levels. ``cppverify::reveal_with_fuel(even, n)`` asks for ``n``
  levels from the start, and ``cppverify::reveal(even)`` gives the definition instead
  of unfoldings. Each level is a proved unfolding, so a proof found this way
  stands.
- That unfolding is a theorem, and the verifier proves it for each predicate
  before any proof may use it, with three generated proofs: monotonicity
  (a derivation of some height is one of every greater height), case
  analysis (the predicate implies its body), and introduction (its body
  implies the predicate). ``Verified: inductive predicate: even`` reports
  that they hold. If one fails it is reported (as ``even (introduction)``,
  for example), and the predicate and every proof that uses it are
  ``Unresolved`` with reason ``spec.inductive``.
- ``cppverify::post(!cppverify::result || Q)`` states what every derivation satisfies. It is proved
  by induction on derivations (a failure reads ``spec post by induction
  failed``) and holds wherever the predicate does. ``Q`` may mention the
  predicate itself, as transitivity does:
  ``cppverify::post(!cppverify::result || cppverify::forall(c, !reach(b, c) || reach(a, c)))``; there the
  predicate is seen through its proved unfolding, never through the
  postcondition being proved. A proof block on it is the induction step:
  it runs for a derivation whose premises already satisfy ``Q``.
- A counterexample is checked against the predicate's true meaning either
  way: when its derivations from an argument reach finitely many arguments,
  by computing the predicate over all of them; otherwise by finding a
  derivation (true) or by a proved postcondition that excludes the argument
  (false), on which the failure then rests. Undecided, the message names
  the application, such as ``whether odd(4) holds``.
- When no unfolding settles a claim, the reason says what the claim needs.
  Where the predicate's derivations from an argument go round a cycle
  (``linked`` over a list whose cell points to itself), it is false there,
  but every unfolding also holds of a predicate true on the cycle. A claim
  that needs it false is then ``spec.fuel`` with ``every counterexample
  found needs linked(..., 0, 1) to hold, but no derivation shows it``:
  only induction shows it, so state what derivations satisfy as a
  postcondition (``!cppverify::result || Q``) or prove it by induction in a proof
  function. The verifier does not unfold further in that case, since no
  unfolding can help. ``backend.invalid-result`` is reserved for a solver
  answer that contradicts a fact it was given.

``constexpr`` as spec
---------------------

A non-recursive, loop-free ``constexpr`` function without its own contract is usable directly in contracts — no separate
``cppverify::spec`` declaration. It keeps **machine** integer semantics (see :doc:`integers`):

.. code-block:: cpp

   constexpr int square(int x) { return x * x; }

   int area(int side)
     cv::pre(side >= 0 && side <= 1000)
     cv::post(cv::result == square(side))
   { return side * side; }

A ``constexpr`` function with ``cppverify::pre``/``cppverify::post`` clauses stays an
executable function and cannot appear in a contract.
