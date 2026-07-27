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

``issued[identity]``
   Whether that lifetime token has ever been allocated, preventing reuse.

``initialized[address]``
   Whether reading the scalar cell is defined.

``size[identity]`` and ``alignment[identity]``
   Target-layout metadata derived from Clang.

On a successful normal ``new`` path, the chosen base is non-null, satisfies the
target alignment, and does not overlap any currently live allocation byte. The
allocation map and metadata receive fresh SSA versions. A first-class
provenance companion travels with each supported local pointer value. A load or
store requires the byte owner to match that companion and its identity to remain
live; a load additionally requires initialization. ``delete`` requires the
matching identity and its exact base, then updates a new liveness version to
``false``.

An allocator may later choose the same numeric address. That replacement gets
a different identity, so the old pointer does not become valid again even when
``old_pointer == replacement`` numerically.

Matching-type local copies, assignments, conditional selections, and
``nullptr`` assignments update the address and provenance companions together:

.. code-block:: cpp

   int alias_write(int value) post(result == value) {
     int *first = new int(0);
     int *owner = new int;
     int *alias = first;
     alias = owner;
     *alias = value;
     int observed = *owner;
     delete alias;
     delete first;
     return observed;
   }

Deleting through either name ends the shared lifetime. Every alias then becomes
dangling, so dereferencing ``owner`` after ``delete alias`` is rejected.

Contracted scalar interfaces
----------------------------

A live initialized allocation pointer may cross a checked modular interface
when the callee is a verified in-translation-unit executable function with a
direct, matching-typed pointer parameter. The callee may compare or directly
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
Owned dynamic storage satisfies the caller-side frame containment check only
when the current provenance equals an identity actually allocated by that
caller.

The checked interface may forward the direct pointer through an acyclic chain
of verified scalar callees. Scalar values loaded from it may also pass through
verified executable or pure spec helpers. Every reached body is scanned against
the same direct-scalar rule; an offset, subscript, pointer copy, recursive scan
cycle, or pointer-result intermediate makes the outer dynamic call fail closed.

A verified callee may return the direct dynamic formal, ``nullptr``, or a
conditional selection of direct dynamic formals. ``VCallStmt`` gives the
pointer result a separate SSA provenance output. Generated result
validity/initialization clauses bind that output to the current byte owner, and
a contract such as ``post(result == source)`` preserves the source identity:

.. code-block:: cpp

   int *identity(int *source)
     pre(source != nullptr)
     post(result == source)
     post(*result == old(*source))
   {
     return source;
   }

   int returned_alias(int value) post(result == value) {
     int *owner = new int(value);
     int *alias = identity(owner);
     int observed = *alias;
     delete alias;
     return observed;
   }

The pointee postcondition above is needed because an ordinary pointer-taking
modular call conservatively forgets the value heap unless its contract restores
the value. Provenance alone proves which live object the pointer denotes; it
does not invent a value-preservation promise.

This remains deliberately a **scalar** interface. The callee may not offset,
subscript, copy, rebind, or deallocate the dynamic formal. Pointer-returning
calls nested inside the callee, proof functions, body-less external contracts,
ghost use, allocation inside the callee, type erasure, and a returned local
pointer copy are rejected. A weak pointer-result contract may be read as an
arbitrary valid pointer, but cannot gain caller-owned ``modifies`` or
``delete`` authority without proving equality to an owned result.
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

Dynamic allocations remain local and non-escaping in this checkpoint.
Matching-pointee local pointer values may be copied, reassigned, selected by a
conditional, or set directly to ``nullptr``. Their provenance follows the value
through branch SSA merges. They may be dereferenced, stored through when the C++
type permits, compared for equality, converted to ``bool``, deleted, and passed
through the checked verified scalar interfaces above. A matching result may
return an alias of caller-owned storage; the callee still cannot allocate and
return a new lifetime.

Type-erasing or indirect copies, returned local copies, nested pointer-result
calls, proof/external boundaries, general arithmetic, subscripting, aggregate
storage, and pointer reassignment inside loops remain unsupported. The bounded
same-object difference described in :doc:`pointers` may use a direct dynamic
base or its inline ``+0``/``+1`` position because the lifetime identity proves
the common origin. Functions that
allocate cannot yet also accept pointer parameters, and allocation/deallocation
inside loop bodies is rejected.

Also unsupported are ``new[]``/``delete[]``, nothrow or placement allocation,
non-scalar objects and destructors, modular allocation-returning functions,
and general array pointer subtraction. These cases fail closed instead of
falling back to the abstract parameter-pointer model.

Pointer parameters remain abstract interface objects. Their implicit validity
and initialization assumptions are not derived from a concrete caller
allocation, and ``valid(p, n)`` remains the explicit buffer-extent marker. See
:doc:`pointers` and :doc:`limitations`.
