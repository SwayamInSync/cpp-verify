Dynamic storage
===============

CppVerify has a deliberately bounded, sound model for local scalar
``new``/``delete``. It tracks allocation ownership, lifetime, alignment,
extent, and initialization in SSA-versioned metadata rather than treating
``valid_ptr`` as a timeless predicate.

Supported forms
---------------

The current surface accepts ordinary throwing scalar ``new`` for complete,
non-volatile integer or enumeration objects in executable contracted
functions. The result must directly initialize a local raw pointer:

.. code-block:: cpp

   int roundtrip(int value)
     post(result == value)
   {
     int *p = new int(value);
     int observed = *p;
     delete p;
     return observed;
   }

Direct initialization and value initialization create initialized storage.
Default initialization does not:

.. code-block:: cpp

   int write_before_read(int value)
     post(result == value)
   {
     int *p = new int;       // the pointee is uninitialized
     *p = value;             // this store marks it initialized
     int observed = *p;
     delete p;
     return observed;
   }

   int zero_initialized()
     post(result == 0)
   {
     int *p = new int();     // value-initialized to zero
     int observed = *p;
     delete p;
     return observed;
   }

Multiple simultaneously live scalar allocations are proved disjoint. A later
allocation may reuse storage after ``delete`` without contradicting facts about
the earlier lifetime.

Safety obligations
------------------

The verifier maintains these logical maps alongside the value heap:

``allocation[address]``
   The unique lifetime identity that owns each target byte.

``base[identity]``
   The numeric base address chosen for that lifetime.

``live[identity]``
   Whether that lifetime is active.

``initialized[address]``
   Whether reading the scalar cell is defined.

``size[identity]`` and ``alignment[identity]``
   Target-layout metadata derived from Clang.

On a successful normal ``new`` path, the chosen base is non-null, satisfies the
target alignment, and does not overlap any currently live allocation byte. The
allocation map and metadata receive fresh SSA versions. The direct local
pointer retains the identity of the lifetime that produced it. A load or store
requires the byte owner to match that identity and the identity to remain live;
a load additionally requires initialization. ``delete`` requires the matching
identity and its exact base, then updates a new liveness version to ``false``.

An allocator may later choose the same numeric address. That replacement gets
a different identity, so the old pointer does not become valid again even when
``old_pointer == replacement`` numerically.

Consequently, all of these are rejected:

.. code-block:: cpp

   int use_after_delete() post(true) {
     int *p = new int(1);
     delete p;
     return *p;              // use after lifetime
   }

   int double_delete() post(true) {
     int *p = new int(1);
     delete p;
     delete p;               // no live allocation remains
     return 0;
   }

   int uninitialized_read() post(true) {
     int *p = new int;
     return *p;              // no preceding store
   }

The ordinary throwing allocation failure path exits exceptionally, so it does
not reach a normal postcondition. Exception handling itself is not in the
verified subset.

Current boundary
----------------

Dynamic pointers are intentionally local and non-escaping in this checkpoint.
The direct allocation variable may be dereferenced, stored through, compared
for equality, converted to ``bool``, and passed to scalar ``delete``. It may not
currently be copied, reassigned, returned, passed across a function-call
boundary, used in pointer arithmetic or subscripting, or stored in an
aggregate. Functions that allocate cannot yet also accept pointer parameters,
and allocation/deallocation inside loop bodies is rejected.

Also unsupported are ``new[]``/``delete[]``, nothrow or placement allocation,
non-scalar objects and destructors, modular allocation-returning functions,
and general pointer subtraction. These cases fail closed instead of falling
back to the abstract parameter-pointer model.

Pointer parameters remain abstract interface objects. Their implicit validity
and initialization assumptions are not derived from a concrete caller
allocation, and ``valid(p, n)`` remains the explicit buffer-extent marker. See
:doc:`pointers` and :doc:`limitations`.
