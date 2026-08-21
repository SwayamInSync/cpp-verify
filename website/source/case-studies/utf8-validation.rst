UTF-8 validation
================

Proving a decoder cannot be tricked.

UTF-8 decoding sits in the core of every C++ text stack -- ICU, Qt, simdjson,
Boost.Locale, every JSON parser. It is also the classic algorithm whose
*rejections* matter more than its acceptances. A decoder that returns the right
answer for well-formed input and quietly accepts malformed input is not a
correct decoder; it is a security hole.

Two ways to get it wrong
------------------------

**Overlong encodings.** Table 3-7 of the Unicode standard starts two-byte
sequences at lead byte ``C2``, not ``C0``. ``C0`` and ``C1`` can only ever
encode a code point below U+0080 -- one that already has a shorter form.
Accepting them lets an attacker spell an ASCII character in two bytes and slip
it past a filter that inspects raw bytes. This is the IIS Unicode
directory-traversal bug and `CVE-2008-2938
<https://nvd.nist.gov/vuln/detail/CVE-2008-2938>`_ in Tomcat: ``/`` written as
``C0 AF`` survives a check for ``../`` and becomes ``/`` after the check has
run.

**Surrogates.** U+D800 through U+DFFF exist only so UTF-16 can address the
supplementary planes. They are not Unicode scalar values and no well-formed
UTF-8 sequence encodes one. Table 3-7 enforces this by capping the second byte
at ``9F`` when the lead byte is ``ED``. Drop that one constraint and the decoder
emits a surrogate, which every downstream stage assuming "this is a scalar
value" is entitled to mishandle.

What is proved
--------------

The decoder implements Table 3-7 verbatim. The theorem is not "it decodes
correctly" but "it cannot be tricked":

- every accepted result is a Unicode scalar value, ``0 .. 0x10FFFF``;
- no accepted result is a surrogate, ``0xD800 .. 0xDFFF``;
- no accepted sequence is overlong -- a length-*k* sequence always carries a
  code point that genuinely requires *k* bytes;
- the consumed length never exceeds the bytes actually available;
- every read lies inside the declared extent, and no arithmetic overflows.

The last two come from the always-on definedness obligations and ``--check-ub``
extents; nothing in the contract asks for them.

The defects, injected and caught
--------------------------------

Each companion changes exactly one thing and is rejected with a concrete
witness.

.. list-table::
   :header-rows: 1
   :widths: 34 30 36

   * - Injected defect
     - Counterexample
     - Meaning
   * - Lead-byte floor ``C2`` becomes ``C0``
     - ``result = 64``
     - ``@`` smuggled as a two-byte overlong sequence
   * - ``ED`` second-byte ceiling removed
     - ``result = 55296``
     - exactly U+D800, the first surrogate

Neither counterexample was guessed. Both are the solver's own witness to the
failing postcondition, reported at the source location of the contract clause
that broke.

Reproduce
---------

.. code-block:: bash

   ./build/bin/cpp-verify --check-ub clang/test/Verify/suite/utf8_validate_pass.cpp
   ./build/bin/cpp-verify --check-ub clang/test/Verify/suite/utf8_overlong_fail.cpp
   ./build/bin/cpp-verify --check-ub clang/test/Verify/suite/utf8_surrogate_fail.cpp

All three are lit tests; the latter two are expected to fail closed.
