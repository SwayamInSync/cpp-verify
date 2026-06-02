Chapter 9 — Why CppVerify on Clang
==================================

**CppVerify** extends the Clang C++ frontend so contracts are parsed and type-checked like ordinary
code—not embedded in comments or external annotation files.

The niche
---------

.. list-table::
   :header-rows: 1
   :widths: 18 18 18 18 28

   * - Tool
     - Parser
     - C++
     - Contracts
     - Notes
   * - Frama-C
     - Custom
     - Limited
     - ACSL comments
     - C-oriented
   * - VCC
     - Custom
     - Dead
     - Macros
     - C only
   * - VeriFast
     - Custom
     - No
     - Annotations
     - Not C++
   * - Verus
     - Rust
     - No
     - First-class
     - Rust only
   * - **CppVerify**
     - **Clang**
     - **Native subset**
     - **Keywords**
     - **Sema-typed**

Contracts go through the same type checker as your program. ``post(result == fibo(n))`` knows the return type of ``fibo``.

Architecture in one picture
---------------------------

.. figure:: /_static/diagrams/cppverify-pipeline.svg
   :align: center
   :figclass: book-figure
   :alt: Pipeline from AST through VCR and passive IR, weakest precondition, Z3, to result

Two outputs from one frontend:

.. figure:: /_static/diagrams/cppverify-workflow.svg
   :align: center
   :figclass: book-figure
   :alt: Parallel verify path and compile path from one Clang AST

