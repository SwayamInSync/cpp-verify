Pointers
========

- Heap modeled internally as a Z3 array from mathematical addresses to
  width-neutral integer cells
- ``modifies(*p, ...)`` — frame
- ``aliases(p, q)`` — allow aliasing
- Implicit ``p != q`` for distinct mutable parameters

Example:

.. code-block:: cpp

   void write(int *p, int v)
     pre(p != nullptr)
     modifies(*p)
     post(*p == v)
   {
     *p = v;
   }

Buffers and array indexing
--------------------------

Pointer arithmetic and subscripting are supported: ``*(p + i)`` and ``p[i]`` (read
and write) lower to indexed heap accesses. Distinct indices are distinct
locations, so storing to ``p[k]`` leaves ``p[i]`` unchanged for ``i != k`` — the
verifier gets this from array theory:

.. code-block:: cpp

   void set(int* p, int i, int j, int v)
     pre(p != nullptr && i != j && p[j] == 5)
     modifies(*p)
     post(p[i] == v && p[j] == 5)        // p[j] is preserved
   { p[i] = v; }

Within a verified function body, ``modifies(*p)`` authorizes the **whole
region** rooted at ``p`` — a write to any ``p[i]`` is covered. A write through
a *different* base pointer that is not in ``modifies`` is still rejected.

To reason about a whole range, use a bounded quantifier in the loop invariant and
postcondition (the half-open bound ``[lo, hi)`` is the implicit trigger). A
fill/zero loop verifies end-to-end:

.. code-block:: cpp

   void zero(int* p, int n)
     pre(p != nullptr && n >= 0 && n <= 1000)
     modifies(*p)
     post(forall(i, 0, n, p[i] == 0))
   {
     int j = 0;
     while (j < n)
       invariant(0 <= j && j <= n && forall(i, 0, j, p[i] == 0))
       decreases(n - j)
     { p[j] = 0; j = j + 1; }
   }

Two-buffer copy loops (``memcpy``-style) also verify, given an explicit
**non-overlap** precondition that the source and destination ranges are disjoint
(``d + n <= s || s + n <= d``). Without it the copy is rejected — storing to the
destination could clobber a source cell still to be read, exactly the C
``memcpy`` vs ``memmove`` distinction:

.. code-block:: cpp

   void copy(int* d, int* s, int n)
     pre(d != nullptr && s != nullptr && n >= 0 && n <= 1000 &&
         (d + n <= s || s + n <= d))      // ranges disjoint
     modifies(*d)
     post(forall(i, 0, n, d[i] == s[i]))
   {
     int j = 0;
     while (j < n)
       invariant(0 <= j && j <= n && forall(i, 0, j, d[i] == s[i]))
       decreases(n - j)
     { d[j] = s[j]; j = j + 1; }
   }

Addresses are reasoned about as mathematical integers, so range conditions like
the non-overlap above are exact (no wraparound). Array indices used in
disjointness facts should be bounded (as in real buffer code); an *unbounded*
pure-disequality disjointness (``i != k`` with no range) may report ``unknown``
(see :doc:`limitations`).

Frames also preserve unrelated objects across a write:

.. code-block:: cpp

   void write_result(int *out, int *preserved, int value)
     pre(out != nullptr && preserved != nullptr)
     modifies(*out)
     post(*out == value)
     post(*preserved == old(*preserved))
   {
     *out = value;
   }

Distinct mutable pointer parameters are non-aliasing by default. The
``modifies(*out)`` clause permits the store and frames ``*preserved`` at its
entry value.

See :doc:`../book/part-ii/ch14-pointers-frames-modifies`.