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

A direct, type-preserving local pointer copy carries the same identity:

.. code-block:: cpp

   int alias_write(int value) post(result == value) {
     int *owner = new int;
     int *alias = owner;
     *alias = value;
     int observed = *owner;
     delete alias;
     return observed;
   }

Deleting through either name ends the shared lifetime. Every alias then becomes
dangling, so dereferencing ``owner`` after ``delete alias`` is rejected.

Contracted scalar callees
-------------------------

A live initialized allocation pointer may cross one modular boundary when the
callee is a verified in-translation-unit executable function with a direct,
matching-typed pointer parameter. The callee may compare or directly
dereference that parameter, and may write it under ``modifies(*p)``:

.. code-block:: cpp

   void write_value(int *target, int value)
     pre(target != nullptr)
     modifies(*target)
     post(*target == value)
   {
     *target = value;
   }

   int modular_write(int value) post(result == value) {
     int *p = new int(0);
     write_value(p, value);
     int observed = *p;
     delete p;
     return observed;
   }

The caller substitutes the allocation's lifetime identity into the callee
precondition, so stale and uninitialized arguments fail at the call site.
Owned dynamic storage also satisfies the caller-side frame containment check.

This is deliberately a **scalar** interface. A callee receiving a dynamic
pointer may not offset, subscript, copy, forward, return, or deallocate it.
Nested executable/spec calls and ghost use of the pointer are also rejected.
Pointer-returning callees, proof functions, and body-less external contract
interfaces are rejected because their provenance/lifetime effects cannot yet
be represented.
Ordinary modular heap framing still applies: a read helper that must return the
entry value should state ``post(result == old(*p))``.

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
The direct allocation variable and direct local aliases with the same
unqualified pointee type may be dereferenced, stored through when the C++ type
permits, compared for equality, converted to ``bool``, and passed to scalar
``delete``. They may enter the restricted verified scalar callee boundary
above. Pointer reassignment, conditional or type-erasing copies, return,
general/spec/external call crossing, arithmetic, subscripting, and aggregate
storage remain unsupported. Functions that allocate cannot yet also accept
pointer parameters, and allocation/deallocation inside loop bodies is rejected.

Also unsupported are ``new[]``/``delete[]``, nothrow or placement allocation,
non-scalar objects and destructors, modular allocation-returning functions,
and general pointer subtraction. These cases fail closed instead of falling
back to the abstract parameter-pointer model.

Pointer parameters remain abstract interface objects. Their implicit validity
and initialization assumptions are not derived from a concrete caller
allocation, and ``valid(p, n)`` remains the explicit buffer-extent marker. See
:doc:`pointers` and :doc:`limitations`.
