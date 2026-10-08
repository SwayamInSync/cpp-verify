Part II — CppVerify
===================

These chapters cover verified C++ in practice: the toolchain, contract syntax, common proof
patterns, backends (Z3, BMC, editable Lean certification), modular calls, how to respond when verification fails,
and proving freedom from undefined behavior.

The examples in these chapters write the constructs through the alias ``cv``
(``cv::pre``, ``cv::check``, ...) and use the names of ``<cppverify.h>`` (``valid``,
``seq``, ``set``, ``multiset``, ``map``, ...) unqualified, as a file does after
``namespace cv = cppverify;`` and ``using namespace cppverify;``. The header itself needs
no ``#include``. Each example is compiled and verified by the test suite, and where a
chapter shows verdicts, the example must give them.

.. figure:: /_static/diagrams/cppverify-workflow.svg
   :align: center
   :figclass: book-figure
   :alt: Verify and compile paths from the same source

.. toctree::
   :maxdepth: 1

   ch09-why-cppverify
   ch10-getting-started
   ch11-first-verified-function
   ch12-loops-in-practice
   ch13-spec-and-proof-functions
   ch14-pointers-frames-modifies
   ch15-toolchain-and-flags
   ch16-when-verification-fails
   ch17-backends-modular-calls
   ch18-undefined-behavior
   ch19-dynamic-storage
   ch20-mathematics-to-code