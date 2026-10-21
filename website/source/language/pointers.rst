Pointers
========

- Heap modeled internally as a Z3 array from mathematical addresses to
  width-neutral integer cells
- ``cppverify::modifies(*p, ...)`` — frame
- ``cppverify::aliases(p, q)`` — allow aliasing
- Implicit object-range disjointness for distinct mutable pointer/reference
  parameters

Example:

.. code-block:: cpp

   void write(int *p, int v)
     cv::pre(p != nullptr)
     cv::modifies(*p)
     cv::post(*p == v)
   {
     *p = v;
   }

Scalar lvalue references
------------------------

Contracted executable free functions support scalar ``T&`` and ``const T&``
parameters for boolean, integral, and enum referents:

.. code-block:: cpp

   void swap_values(int& left, int& right)
     cv::modifies(left, right)
     cv::post(left == cv::old(right) && right == cv::old(left))
   {
     int temporary = left;
     left = right;
     right = temporary;
   }

The VCR parameter is an immutable address. Reading ``left`` loads the heap,
assignment stores through the address, and ``cppverify::old(left)`` reads the entry heap.
CppVerify adds a non-null and live entry precondition for each reference, and
verifies the body as reading the referent initialized; a call that passes
storage not yet initialized is ``Unresolved`` (``construct.unsupported``). Mutable pointer/reference parameter pairs are object-range disjoint
by default (over whole ``valid(p, n)`` extents);
``cppverify::aliases(left, right)`` permits same-object aliasing.

Out-parameters
~~~~~~~~~~~~~~

A function is verified as if it read its reference and pointer parameters'
storage, so every such parameter must refer to initialized storage at a call.
C++ requires less: a function that writes its parameter before reading it,
an out-parameter, may receive storage that is not initialized yet. Until a
contract can say that a function writes a parameter first, such a call is
``Unresolved`` with reason ``construct.unsupported``: neither proved nor
reported as a failure.

.. cppverify-example: unresolved seven
.. cppverify-example: fails read_too_early

.. code-block:: cpp

   void init(int &out)
     cv::modifies(out)
     cv::post(out == 7)
   {
     out = 7;
   }

   int seven()
     cv::post(cv::result == 7)
   {
     int a;
     init(a);
     return a;
   }

   int seven_initialized()
     cv::post(cv::result == 7)
   {
     int a = 0;
     init(a);
     return a;
   }

   int read_too_early()
     cv::post(cv::result == 3)
   {
     int a;
     int &r = a;
     int copy = r;
     r = 3;
     return copy;
   }

.. code-block:: text

   Verified: init [backend=z3]
   out.cpp:12:3: Unresolved: seven [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: binding a reference or pointer parameter to storage that is not initialized, since the callee is verified as reading initialized storage)
   Verified: seven_initialized [backend=z3]
   out.cpp:29:3: error: verification failed: read_too_early [...::initialization@29:3] (...) [backend=z3] [reason=counterexample]

- Initializing the storage before the call, as ``seven_initialized`` does, is
  the way to verify such code today.
- The same holds for an element of a local array (``init(arr[0])``), for
  storage from ``new int`` passed to a pointer parameter before anything
  writes it (``int *p = new int; init_ptr(p);``), and for a function that
  returns a pointer to storage not initialized yet.
- A local reference may bind storage that is not initialized, as C++ allows,
  and a write through it initializes the object. A read before the first
  write is a real error, reported where it happens, as in ``read_too_early``.

Before 0.2 each of these calls was a reported failure (``verification failed:
... initialization``), and ``int a; init(a);`` stopped the whole file with
``error: seven: read of uninitialized local value: a``.

Aliasing between parameters
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The default is a precondition every caller must establish. A function that
works when its parameters share storage says so with ``cppverify::aliases``, and its
body is then verified for both cases:

.. cppverify-example: fails same_cell_wrong

.. code-block:: cpp

   void copy_or_self(int *dst, int *src)
     cv::aliases(dst, src)
     cv::pre(dst != nullptr && src != nullptr)
     cv::modifies(*dst)
     cv::post(*dst == cv::old(*src))
   {
     *dst = *src;
   }

   void copy_one(int *dst, int *src)
     cv::pre(dst != nullptr && src != nullptr)
     cv::modifies(*dst)
     cv::post(*dst == cv::old(*src))
   {
     *dst = *src;
   }

   void same_cell(int *p)
     cv::pre(p != nullptr)
     cv::modifies(*p)
     cv::post(*p == cv::old(*p))
   {
     copy_or_self(p, p);
   }

   void same_cell_wrong(int *p)
     cv::pre(p != nullptr)
     cv::modifies(*p)
   {
     copy_one(p, p);   // fails: the aliasing check at this call
   }

``cppverify::modifies(left)`` names the referent, a single scalar object, so a call
changes only that cell. A provenance-backed automatic or dynamic scalar actual
is framed as one exact cell after the callee passes the structural non-escape
scan.

A reference argument may also be an initialized ordinary scalar local:

.. code-block:: cpp

   void set_value(int& target, int value)
     cv::modifies(target)
     cv::post(target == value)
   {
     target = value;
   }

   void set_pointer(int* target, int value)
     cv::pre(target != nullptr)
     cv::modifies(*target)
     cv::post(*target == value)
   {
     set_value(*target, value);
   }

   int set_local(int value)
     cv::post(cv::result == value)
   {
     int local = 0;
     int& alias = local;
     set_value(alias, value);
     return local;
   }

Only address-required scalar locals are spilled from scalar SSA. They use fresh
automatic lifetime identities, target size/alignment, byte ownership,
liveness, and initialization. Local bindings snapshot the address, may chain,
and cannot escape. Each automatic object's lifetime ends at the closing brace
of its block and on each early return.

A reference may bind to a field or a fixed-array element, of a promoted local
object or of a parameter's buffer. Conditional bindings, temporaries,
reference returns, address-taking, rvalue references, and non-scalar
referents fail closed. Addressable declarations inside loops and ``cppverify::old`` of an automatic local/local
binding are rejected, while an outer automatic local and a local reference
declared inside a loop are supported. Requiring initialized storage excludes
output-only references to an indeterminate object for now.
Recursion that stores through a pointer or reference parameter, or uses
automatic objects, is supported; recursion through a function that allocates
or frees storage is ``construct.unsupported``.

Buffers and array indexing
--------------------------

Pointer arithmetic and subscripting are supported: ``*(p + i)`` and ``p[i]``
(read and write) lower to indexed heap accesses. Addresses use target bytes, so
each ``T*`` step is scaled by Clang's target ``sizeof(T)``; field selection adds
the target record-layout byte offset. Distinct indices are therefore distinct
locations, so storing to ``p[k]`` leaves ``p[i]`` unchanged for ``i != k`` —
the verifier gets this from array theory:

.. code-block:: cpp

   void set(int* p, int i, int j, int v)
     cv::pre(valid(p, 1000) && i != j)
     cv::pre(0 <= i && i < 1000 && 0 <= j && j < 1000)
     cv::pre(p[j] == 5)
     cv::modifies(*p)
     cv::post(p[i] == v && p[j] == 5)        // p[j] is preserved
   { p[i] = v; }

.. note::

   Addresses are byte-scaled, so separating ``p[i]`` from ``p[j]`` means
   separating ``4*i`` from ``4*j``. The default integer encoding derives that
   from ``i != j`` alone. With ``--int-encoding=bitvector`` it needs range
   reasoning about sign extension that bit-vector solvers do not do well, and
   the bit-vector attempt can time out on such a query; the verifier then
   retries it in the default encoding.

Within a verified function body, ``cppverify::modifies(*p)`` authorizes the **whole
region** rooted at ``p`` — a write to any ``p[i]`` is covered. A write through
a *different* base pointer that is not in ``cppverify::modifies`` is still rejected.

A ``cppverify::modifies`` footprint is one of:

- a **cell**: ``p[i]``, ``p->field``, a field or array element inside the
  record ``p`` addresses (``p->inner.x``, ``p->buf[i]``), or a reference, at
  its exact address;
- a **range** ``p[lo : n]``: the ``n`` elements from ``p[lo]``, half-open
  ``[lo, lo + n)`` (Clang's array-section syntax), and likewise
  ``p->buf[lo : n]`` for an array member (:doc:`structs`);
- a **region** ``*p``: the object ``p`` addresses, which is its
  ``valid(p, n)`` extent when it has one and otherwise one object.

At a **modular call** the caller's heap changes only inside the callee's
footprints, instantiated with the arguments; every other cell keeps its value.
A callee writing a range or a whole slice frames the rest of the buffer:

.. code-block:: cpp

   void zero_middle(int* p, int n, int lo, int len)
     cv::pre(valid(p, n) && n >= 0 && n <= 1000 && 0 <= lo && 0 <= len &&
         lo + len <= n)
     cv::modifies(p[lo : len])
     cv::post(cv::forall(i, lo, lo + len, p[i] == 0))
   {
     int j = lo;
     while (j < lo + len)
       cv::invariant(lo <= j && j <= lo + len && cv::forall(i, lo, j, p[i] == 0))
       cv::modifies(p[lo : len])
       cv::decreases(lo + len - j)
     { p[j] = 0; j = j + 1; }
   }

   void keeps_rest(int* p, int n)
     cv::pre(valid(p, n) && n >= 4 && n <= 1000)
     cv::modifies(*p)
     cv::post(p[0] == cv::old(p[0]) && p[3] == cv::old(p[3]))
     cv::post(p[1] == 0 && p[2] == 0)
   {
     zero_middle(p, n, 1, 2);
   }

Each callee footprint must lie within the caller's own frame, cell by cell,
whichever pointer reaches it. A callee that writes its one object
(``cv::modifies(*p)``) may be passed a cell the caller may write, or a copy of
a pointer into an object the caller may write:

.. cppverify-example: fails set_fourth

.. code-block:: cpp

   void put(int *p, int v)
     cv::pre(p != nullptr)
     cv::modifies(*p)
     cv::post(*p == v)
   {
     *p = v;
   }

   void set_third(int *a)
     cv::pre(cv::valid(a, 4))
     cv::modifies(a[2])
     cv::post(a[2] == 5 && a[1] == cv::old(a[1]))
   {
     put(a + 2, 5);
   }

   void set_through_copy(int *a)
     cv::pre(cv::valid(a, 4))
     cv::modifies(*a)
     cv::post(a[2] == 5)
   {
     int *q = a + 2;
     put(q, 5);
   }

   void set_fourth(int *a)
     cv::pre(cv::valid(a, 4))
     cv::modifies(a[2])
   {
     put(a + 3, 5);
   }

.. code-block:: text

   Verified: put [backend=z3]
   Verified: set_third [backend=z3]
   Verified: set_through_copy [backend=z3]
   frames.cpp:30:3: error: verification failed: set_fourth [...::frame@30:3] (counterexample: a [ssa=a_0] [type=pointer] = 1; trace: call.put@30:3 arg0=13 arg1=5) [backend=z3] [reason=counterexample]

``set_fourth`` may write only ``a[2]``, at address 9 when ``a`` is 1, but
passes ``a + 3``, address 13. A pointer-taking
callee with no explicit ``cppverify::modifies`` that may write memory is treated as
writing the whole heap, which cannot fit inside an explicit caller frame; an
unframed caller may still call it. Under ``--no-check-ub`` a region footprint
also forgets the whole heap. The whole-heap fallback can lose a true fact
about an unrelated object, but it cannot prove a false one.

To reason about a whole range, use a bounded quantifier in the loop invariant and
postcondition. The solver chooses the terms that instantiate it, unless a
``cppverify::trigger`` names one (see :doc:`expressions`). A fill/zero loop
verifies end-to-end:

.. code-block:: cpp

   void zero(int* p, int n)
     cv::pre(valid(p, n) && n >= 0 && n <= 1000)
     cv::modifies(*p)
     cv::post(cv::forall(i, 0, n, p[i] == 0))
   {
     int j = 0;
     while (j < n)
       cv::invariant(0 <= j && j <= n && cv::forall(i, 0, j, p[i] == 0))
       cv::decreases(n - j)
     { p[j] = 0; j = j + 1; }
   }

A loop writes only the objects its stores and calls reach, so every other
object keeps its value without an invariant saying so. A loop may also state
what it writes with ``cppverify::modifies`` after its invariants (ACSL's ``loop
assigns``); the footprints are read in each iteration's state, so
``cppverify::modifies(p[0 : j])`` describes the prefix written so far.

The objects a store reaches are found from where its pointer came from, not
its spelling: every pointer variable has origins, the objects it may address
(see *Pointer origins* below). A pointer that walks through a buffer still
writes only that buffer, and a pointer chosen among several parameters writes
one of their objects:

.. code-block:: cpp

   void fill_walk(int *a, int n, int *count)
     cv::pre(valid(a, n) && n >= 0 && n <= 1000 && valid(count, 1))
     cv::modifies(*a)
     cv::post(cv::forall(k, 0, n, a[k] == 7))
     cv::post(*count == cv::old(*count))
   {
     int *q = a;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && q == a + i)
       cv::invariant(cv::forall(k, 0, i, a[k] == 7))
       cv::decreases(n - i)
     {
       *q = 7;
       q = q + 1;
     }
   }

   void clear_one(int *a, int *b, int *c, int n, bool first)
     cv::pre(valid(a, n) && valid(b, n) && valid(c, 1) && n >= 1 && n <= 1000)
     cv::modifies(*a, *b)
     cv::post(*c == cv::old(*c))
   {
     int *p = first ? a : b;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n)
       cv::decreases(n - i)
     {
       p[i] = 0;
     }
   }

Both verify without an invariant about ``*count`` or ``*c``.

Two-buffer copy loops (``memcpy``-style) need the source and destination
ranges to be disjoint; otherwise storing to the destination could clobber a
source cell still to be read, exactly the C ``memcpy`` vs ``memmove``
distinction. ``valid(d, n)`` and ``valid(s, n)`` extents provide this
automatically: the implicit non-aliasing default treats each declared extent
as the pointer's complete object, so the two extents are disjoint unless a
pointer is null or an extent is empty, and every caller must prove that. An
``cppverify::aliases(d, s)`` pair keeps the single-object rule and may overlap.

.. code-block:: cpp

   void copy(int* d, const int* s, int n)
     cv::pre(valid(d, n) && valid(s, n) && n >= 0 && n <= 1000)
     cv::modifies(*d)
     cv::post(cv::forall(i, 0, n, d[i] == s[i]))
   {
     int j = 0;
     while (j < n)
       cv::invariant(0 <= j && j <= n && cv::forall(i, 0, j, d[i] == s[i]))
       cv::decreases(n - j)
     { d[j] = s[j]; j = j + 1; }
   }

Addresses are reasoned about as mathematical integers, so range conditions like
the non-overlap above are exact (no wraparound).

Same-array pointer difference
-----------------------------

Pointer-pointer subtraction is supported in executable code when both
positions are proved to belong to one array object:

.. code-block:: cpp

   long distance(int *p, int n, int i, int j)
     cv::pre(valid(p, n) && p != nullptr && n >= 0 &&
         0 <= i && i <= n && 0 <= j && j <= n)
     cv::post(cv::result == i - j)
   {
     return (p + i) - (p + j);
   }

The operands must have the same complete pointee type. Two null pointers
differ by 0, as C++ defines; otherwise the operands must have one origin, and
each must lie in its origin's object: a ``valid(p, n)`` marker supplies the
extent and each position must lie in the closed interval ``[0, n]``; the
inclusive endpoint is the legal one-past position. CppVerify subtracts
target-byte addresses, divides by ``sizeof(T)``, proves that the mathematical
element distance is representable by the target ``ptrdiff_t``, and only then
materializes the machine result. Signed, unsigned, and target-width indices
follow their C++ machine representations. A position may be stepped or
copied any number of times, in a loop or not:

.. code-block:: cpp

   int length_of(const char *s, int n)
     cv::pre(valid(s, n) && n >= 1 && n <= 1000)
     cv::post(0 <= cv::result && cv::result < n)
   {
     const char *p = s;
     while (p < s + (n - 1) && *p != 0)
       cv::invariant(s <= p && p <= s + (n - 1))
       cv::decreases(s + (n - 1) - p)
     {
       p = p + 1;
     }
     return p - s;
   }

Without a declared extent, a direct abstract parameter or represented scalar
dynamic allocation has only its complete-object positions ``0`` and ``1``.
Local dynamic aliases establish one origin through their shared, nonzero
lifetime identity. Two different parameters may point into one caller array,
which the object model cannot express, so a difference between them (or
between pointers that may come from either) is ``construct.unsupported``:
neither proved nor reported as an error. Proving ``left == right`` does not
change that.

Two null pointers differ by 0, as C++ defines ([expr.add]/5); a difference
with one null operand is undefined and fails:

.. cppverify-example: fails one_null

.. code-block:: cpp

   long two_nulls(const int *p, const int *q)
     cv::pre(p == nullptr && q == nullptr)
     cv::post(cv::result == 0)
   {
     return p - q;
   }

   long one_null(const int *p, const int *q)
     cv::pre(p == nullptr && q != nullptr)
   {
     return p - q;
   }

.. code-block:: text

   Verified: two_nulls [backend=z3]
   nulls.cpp:11:3: error: verification failed: one_null [...::pointer-difference@11:3] (counterexample: p [ssa=p_0] [type=pointer] = 0, q [ssa=q_0] [type=pointer] = 1; ...) [backend=z3] [reason=counterexample]

Before 0.2, ``two_nulls`` failed the same way.

A difference with one null operand, a dangling operand, a position outside
its object, or a distance that does not fit ``ptrdiff_t`` fails with a
counterexample. A difference of pointers loaded from memory, pointer compound
assignment (``p += k``), and a pointer difference inside a ``cv::spec`` or
lifted ``constexpr`` function are rejected: the run stops with an error naming
the construct, for example ``error: gap: pointer difference in spec or lifted
constexpr functions is unsupported``.

Local scalar dynamic storage
----------------------------

Ordinary scalar ``new``/``delete`` is supported for a direct local pointer.
Allocation state is SSA-versioned: the verifier records the
owning byte range, liveness, target size/alignment, and initialization. It
therefore rejects use-after-delete, double-delete, overlap between simultaneous
allocations, and uninitialized reads:

.. code-block:: cpp

   int roundtrip(int value)
     cv::post(cv::result == value)
   {
     int *p = new int;
     *p = value;
     int observed = *p;
     delete p;
     return observed;
   }

Its identity propagates through matching-typed local copies, reassignment,
conditional selection, direct ``nullptr`` assignment, and branch merges.
Deleting through any alias invalidates all aliases of that lifetime.
Type-erasing/indirect copies, general arithmetic, and pointer reassignment or
allocation/free in a loop body remain unsupported. The same-object difference
fragment above is the only dynamic pointer arithmetic exception. A
restricted interface admits direct scalar access and acyclic direct-pointer
forwarding through matching parameters of verified, non-allocating executable
callees. A direct/conditional/null pointer result may retain caller-owned
provenance when its contract relates the result to those inputs.

A separate inferred factory effect admits the exact live initialized base of
one fresh scalar allocation (or null) from a body-present acyclic function.
Direct and local-alias forwarding compose, and the caller may mutate or delete
the result. Contracts still state null correlation and pointee values. No
contract or external declaration can claim freshness: uninitialized, freed,
arithmetic-derived, multiply allocated, secondarily escaped, recursive, and
type-erased results fail closed. See
:doc:`dynamic-storage` for the complete boundary.

Buffer bounds with ``valid``
----------------------------

Memory accesses are checked by default (``--no-check-ub`` turns it off).
``valid(p, n)`` in a precondition says that ``p`` points to ``n`` objects,
``p[0]`` to ``p[n - 1]``. ``<cppverify.h>`` provides it for every pointee
type:

.. code-block:: cpp

   using cppverify::valid;

   int get(const int* p, int n, int i)
     cv::pre(valid(p, n) && 0 <= i && i < n)
     cv::post(cv::result == p[i])
   { return p[i]; }

   int past_end(const int* p, int n)
     cv::pre(valid(p, n) && n >= 1)
   { return p[n]; }

.. code-block:: text

   Verified: get [backend=z3]
   error: verification failed: past_end [...::bounds@10:10]

The marker means ``n >= 0``. A positive extent also means ``p`` is non-null and
abstractly valid; an extent of zero permits null. Every ``p[i]`` or ``*(p + i)``
access rooted at that parameter must then prove ``0 <= i < n``, and pointer
arithmetic must stay in ``[0, n]``: ``p + n`` is the one-past position, which
may be formed and compared but not read. The marker must occur as a positive
top-level conjunction clause of a ``cppverify::pre`` with a bare complete-object pointer,
and each pointer may have only one marker; ambiguous forms (under ``||``,
``!``, or a conditional, or a second marker for one pointer) fail closed.

Where the marker may appear
~~~~~~~~~~~~~~~~~~~~~~~~~~~

``valid(p, n)`` is not a condition that a state satisfies or violates. In a
precondition it declares the extent the caller provides, and the verifier
checks every access against that extent; that is its whole meaning. Written
anywhere else (a ``cppverify::post``, a loop invariant, a ``cppverify::check``,
ghost code, or a spec function) it would be a condition that always holds, so
a claim made with it would verify without saying anything. That is an error
for the function, which is then not verified; the other functions of the file
still are:

.. cppverify-example: rejects

.. code-block:: cpp

   int *start_of(int *buf)
     cv::pre(valid(buf, 4))
     cv::post(valid(cv::result, 4))
   {
     return buf;
   }

.. code-block:: text

   error: start_of: valid(p, n) declares an extent only as a top-level condition of a cppverify::pre, and has no meaning in a postcondition

The message ends with the place it found the marker: a postcondition, a loop
invariant, a ``cppverify::check``, ghost code, or a spec function. The same
holds for a marker you declare yourself as a spec named ``valid``.

To tell callers where a result points, relate it to a parameter whose extent
they know; their own precondition then covers the accesses through it:

.. code-block:: cpp

   int *start_of(int *buf)
     cv::pre(valid(buf, 4))
     cv::post(cv::result == buf)
   {
     return buf;
   }

   int fourth(int *a)
     cv::pre(valid(a, 4) && a[3] == 7)
     cv::post(cv::result == 7)
   {
     int *q = start_of(a);
     return q[3];
   }

.. code-block:: text

   Verified: start_of [backend=z3]
   Verified: fourth [backend=z3]

An extent declared by the precondition holds for the whole function, so a
loop invariant does not repeat it. The invariant bounds the index, and each
access is checked against the extent:

.. code-block:: cpp

   int sum4(const int *a, int n)
     cv::pre(valid(a, n) && n >= 0 && n <= 4)
     cv::pre(cv::forall(k, 0, n, 0 <= a[k] && a[k] <= 100))
     cv::post(0 <= cv::result && cv::result <= 100 * n)
   {
     int s = 0;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && 0 <= s && s <= 100 * i)
       cv::decreases(n - i)
     {
       s = s + a[i];
     }
     return s;
   }

.. code-block:: text

   Verified: sum4 [backend=z3]

With ``--no-check-ub`` every marker, in a precondition too, folds to ``true``
with a warning, and a misplaced one is not an error.

``valid`` exists only for verification, like the spec collections of the same
header; Sema rejects it in executable code. Write ``cppverify::valid`` or add
``using cppverify::valid;``. Programs written before the header may declare
the marker themselves, and that form keeps working: a ``cppverify::spec`` function named
``valid`` with a pointer and an integer parameter is the same marker.

.. code-block:: cpp

   cv::spec bool valid(const long* p, int n) { return true; }

   long last(const long* a, int n)
     cv::pre(valid(a, n) && n >= 1)
   { return a[n - 1]; }

A user declaration covers only its own pointer type, so one is needed per
pointee type; the header's template covers all of them.

A pointer without a marker addresses a single object, as Frama-C's ``\valid``
guards and Verus permissions require: ``p[1]`` through ``int *p`` fails, and
so does forming ``p + 10`` from ``valid(p, 2)``, since pointer arithmetic must
stay within the object's closed range ``[0, n]``. The object of a pointer is
the one its origin names, below; when its origin is unknown it is some
parameter's object, or the object at a base known to be valid such as a
callee's result.

Pointer origins
---------------

Every pointer variable has, at every point, its origins: the objects it may
address, as CompCert's memory blocks and Frama-C's base addresses. A pointer
parameter starts with the object it addresses on entry and a global's address
with the global. Pointer arithmetic keeps the origin, assignment copies it,
and branches and loops join the possibilities, so ``q = first ? a : b`` has
the origins ``a`` and ``b``. A pointer loaded from memory or returned by a
call has no known origin.

An access or a step must stay in its origin's object. A pointer that came
from ``a`` and moved one past its end is rejected there even when another
object happens to start at that address, as C++ requires. A pointer
difference needs one origin, and a loop writes only its stores' origins.

Inside a loop, the verifier proves two facts for you: a pointer the loop
moves stays a whole number of elements from its origin's start, and a pointer
that may have either of two origins keeps one of them. An invariant still
states addresses, and an address alone does not say where a pointer came
from. When a walker may be in either of two objects, tie it to the condition
that chose:

.. code-block:: cpp

   void clear_chosen(int *a, int *b, int n, bool s)
     cv::pre(valid(a, n) && valid(b, n) && n >= 1 && n <= 1000)
     cv::modifies(*a, *b)
   {
     int *q = s ? a : b;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && (s ? q == a + i : q == b + i))
       cv::decreases(n - i)
     {
       *q = 0;
       q = q + 1;
     }
   }

With only ``q == a + i || q == b + i``, the invariant would allow ``q`` one
past the end of ``a`` at the start of ``b`` while it came from ``a``, and the
store there would be rejected.

The same marker composes across modular calls. An argument for a parameter
with ``valid(q, length)`` must have its ``length`` elements in one of the
caller's objects: passing ``p + offset`` from ``valid(p, n)`` requires
``0 <= offset``, ``0 <= length``, and ``offset + length <= n``. An empty slice
may start at ``p + n``. The argument may be computed in any way, as a copy, a
choice, a pointer stepped in a loop, or a callee's result whose contract says
where it points; the elements must lie in the objects it may address:

.. cppverify-example: fails third

.. code-block:: cpp

   int first(const int *p, int n)
     cv::pre(cv::valid(p, n) && n >= 1)
     cv::post(cv::result == p[0])
   {
     return p[0];
   }

   int second(const int *a, const int *b, bool from_a)
     cv::pre(cv::valid(a, 4) && cv::valid(b, 3))
     cv::post(cv::result == (from_a ? a[1] : b[0]))
   {
     const int *q = from_a ? a + 1 : b;
     return first(q, 3);
   }

   int third(const int *a)
     cv::pre(cv::valid(a, 4))
   {
     const int *q = a + 2;
     return first(q, 3);
   }

.. code-block:: text

   Verified: first [backend=z3]
   Verified: second [backend=z3]
   slices.cpp:20:3: error: verification failed: third [...::bounds@20:3] (counterexample: a [ssa=a_0] [type=pointer] = 1, q [ssa=q_1] [type=pointer] = 9; trace: call.first@20:3 arg0=9 arg1=3) [backend=z3] [reason=counterexample]

``third`` passes three elements from ``a + 2``, of which only two are in
``a``: with ``a`` at address 1, ``q`` is 9, and the call would read up to
address 21, past ``a``'s end at 17. Read-only slice calls preserve the heap, including
acyclic chains of read-only callees; exact-cell effects such as
``cppverify::modifies(q[0])``, ranges, and a whole-slice ``cppverify::modifies(*q)`` are also
supported, and frame every cell of ``p`` outside the slice.

With ``--no-check-ub``, dereferences must still be non-null and live, but
accesses are not checked against objects. Parameter pointers use abstract
entry-state allocation and initialization assumptions. Concrete identity,
liveness, alignment, and initialization are available only for promoted
automatic objects (address-taken scalar locals, fixed local arrays, and their
enclosing records) and for the bounded scalar allocation and inferred
fresh-owned return subset. Their provenance is first-class across supported
local values and checked scalar call/return interfaces, but abstract buffers
and general pointer interfaces remain unsupported.

Frames also preserve unrelated objects across a write:

.. code-block:: cpp

   void write_result(int *out, int *preserved, int value)
     cv::pre(out != nullptr && preserved != nullptr)
     cv::modifies(*out)
     cv::post(*out == value)
     cv::post(*preserved == cv::old(*preserved))
   {
     *out = value;
   }

Distinct mutable pointer/reference parameters are non-aliasing by default. The
``cppverify::modifies(*out)`` clause permits the store and frames ``*preserved`` at its
entry value.

See :doc:`../book/part-ii/ch14-pointers-frames-modifies`.