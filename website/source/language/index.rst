Language reference
==================

Compact lookup for contract syntax and semantics. For a guided introduction, start with
:doc:`../book/index`; for backends and ``cpp-verify`` flags, see :doc:`../book/part-ii/ch17-backends-modular-calls`
and :doc:`tooling`.

Examples on these pages write the constructs through the alias ``cv`` and use the
names of ``<cppverify.h>`` (``valid``, ``seq``, ``set``, ``multiset``, ``map``, ...)
unqualified, as a file does after::

   namespace cv = cppverify;
   using namespace cppverify;

``<cppverify.h>`` itself needs no ``#include`` (see :doc:`syntax`).

Every example is compiled and verified by the test suite
(``website/scripts/check-doc-examples.py``), and where a page shows verdicts, the example must
give them.

.. toctree::
   :maxdepth: 1

   syntax
   expressions
   functions-loops
   ghost-proofs
   structs
   pointers
   dynamic-storage
   integers
   tooling
   limitations