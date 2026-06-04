Structs and type invariants
===========================

Contracts may read fields of by-value (and reference) struct/class parameters with ordinary
member syntax:

.. code-block:: cpp

   struct Rect { int w; int h; };

   int area(Rect r)
     pre(r.w >= 0 && r.w <= 1000 && r.h >= 0 && r.h <= 1000)
     post(result >= 0)
   { return r.w * r.h; }

``type_invariant``
------------------

A ``type_invariant`` states a property every instance of a type maintains. Declare it **after** the
fields it names (it is parsed in place):

.. code-block:: cpp

   struct Point {
     int x;
     int y;
     type_invariant(x >= 0 && x <= 1000 && y >= 0 && y <= 1000);
   };

   int sum(Point p)
     post(result >= 0 && result <= 2000)
   { return p.x + p.y; }            // x, y in [0, 1000] are assumed from the invariant

Semantics:

- The invariant is injected as a **precondition** at the first use of an invariant field, for
  by-value and reference (``Point``, ``const Point&``) parameters. Because it is a precondition,
  callers must establish it when they pass such a value.
- It is **not** injected for raw pointer-to-struct parameters (their fields are heap loads).
- **Returns are checked**: when a function returns a struct value of an invariant-bearing type,
  the verifier asserts the invariant holds for the returned value. Building and returning a struct
  whose fields violate the invariant is a verification error.

.. code-block:: cpp

   struct Box { int w; int h; type_invariant(w >= 0 && h >= 0); };

   Box make(int a, int b)
     pre(a >= 0 && a <= 50 && b >= 0 && b <= 50)   // drop b >= 0 and this fails
   { Box x; x.w = a; x.h = b; return x; }          // invariant asserted here

The invariant may be temporarily broken **inside** the function while you assign fields one at a
time — it is only required to hold at the return (the encapsulation boundary), not after each
individual field write.

View functions
--------------

Define ``spec`` functions that expose a mathematical view of a struct, then write contracts against
the view rather than the layout:

.. code-block:: cpp

   struct Arr { int data[100]; int len; };

   spec int size(Arr a) { return a.len; }
