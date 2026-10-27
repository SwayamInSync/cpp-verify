Release notes
=============

cpp-verify follows `Semantic Versioning <https://semver.org>`_. While the major
version is 0, a minor release (0.2.0) may change the contract language or the
meaning of a verdict, always with a migration path; a patch release (0.1.1)
fixes bugs and soundness issues without changing the language, and may move to
a newer point release of the same LLVM major. Moving to a new LLVM major
release changes what C++ the compiler accepts, so it takes a minor release.
``cpp-verify --version`` reports the release, the LLVM release it is built on,
and the backend versions. A build from ``main`` between releases reports the
next release with ``-dev``.

The data formats keep versions of their own, listed with each release.

0.2.0 (in development)
----------------------

The changes on ``main`` since 0.1.1, which 0.2.0 will ship. Each entry says
what 0.1.1 did and what happens now; the page it links shows an example with
the verifier's output.

Wrong results fixed
~~~~~~~~~~~~~~~~~~~

These made 0.1.1 report ``Verified`` for a claim that is false, or compile a
program that cannot work.

**A clause takes one expression.** ``cv::post(cv::result >= 0 cv::result <= 10)``,
with its ``&&`` missing, kept the first condition and dropped the rest without
a word, so the clause checked less than it said. Anything after a clause's
expression is now an error (:doc:`language/syntax`).

**Recursion through** ``cppverify::choose``. A call inside a choose's body was not
seen as a call of the function the choose is in, so a spec that applied
itself there skipped its termination check, and its contradictory definition
let a false claim verify. The call is now checked like any other recursive
call (:doc:`book/part-ii/ch13-spec-and-proof-functions`).

**Archive replay reports proved obligations, not** ``Verified``. Replay printed
``Verified`` for every module whose obligations held, although a source
verdict also rests on facts an archive does not carry, such as a callee's
contract. It now prints ``Proved obligations: f (dependencies not checked in
replay)``, JSON status ``proved-obligations`` (:doc:`language/tooling`).

**Results that rest on Lean proofs.** With ``--lean-fallback`` and
``--lean-certify``, a spec whose termination check was sent to Lean counted
as terminating before Lean checked it. So a caller that used the spec's
definition stayed ``Verified`` when the Lean proof failed, and when another
function failed, which skipped certification. A function proved in Lean was
``Certified`` although it relied on a contract nothing establishes, such as
one without a definition. No result proved in Lean got the vacuity checks,
so a goal that held only because no execution reached it was ``Certified``
too. Certification now runs whatever else failed, before the facts verdicts
rest on are settled: a Lean result rests on the callee contracts and spec
facts its module uses, as a solver's does, and gets the same qualifiers and
vacuity checks (:doc:`book/part-ii/ch17-backends-modular-calls`).

**A spec reads exact values.** A value a spec body read through a pointer kept
its machine type, so ``p[0] + p[1]`` wrapped: a proof that the sum of
``2147483647`` and ``1`` is negative verified. Such reads are now mathematical
integers, as the rest of a spec is (:doc:`language/ghost-proofs`).

**Quantifiers in executable code are errors.** ``cv::forall`` and ``cv::exists``
outside contracts and ghost code compiled to an undefined value while the
verifier read them as quantifiers. They are now an error, as ``cv::choose``
already was (:doc:`language/expressions`).

**Spec functions in generic lambdas are errors.** A spec function called in a
generic lambda compiled, and the program failed to link. It is now reported
where it is written (:doc:`language/ghost-proofs`).

**Extent markers outside a precondition are errors.** ``valid(p, n)`` declares
an extent only as a top-level condition of a precondition. Anywhere else it
meant ``true``, so ``cv::post(valid(cv::result, 4))`` verified for a function
that returns ``nullptr``. In a postcondition, a loop invariant, a
``cppverify::check``, ghost code, or a spec function it is now an error for
that function (:doc:`language/pointers`).

**Contracts must be defined.** A contract is C++, evaluated where the function
is called and where it returns, but 0.1.1 never checked that it was defined
there: a precondition was only assumed, and the reads of a postcondition, a
loop invariant, or a ``cppverify::check`` were not checked against extents. The
logic defines what C++ does not, so a trusted ``cv::post(1000 / cv::result >
0)`` excluded a result of 0, and a caller that divided by that result
verified. Each clause is now checked where it is evaluated: preconditions in
order, each where the ones before it hold; postconditions in the state the
function returns in, or for a trusted function or one without a definition in
every state its frame allows; and every clause with the memory checks of the
body. A clause that may be undefined fails as ``contract of f``, and callers
that rely on it are ``Unresolved`` with reason ``callee.contract``. A contract
that tests a condition after using it, as ``cv::pre(a / b > 0 && b != 0)``
does, needs the test first (:doc:`language/functions-loops`).

**Clang's own analyses.** ``noexcept`` of a contract expression crashed or hung
the compiler, as did a contract expression in a C++98 constant; the static
analyzer reported nothing after a ghost block; libclang hid the constructs;
and a contract expression in a template's signature produced a malformed
symbol. Each now behaves by the construct's meaning (:doc:`language/tooling`).

**Lean certification against proofs in bad faith.** Certification compiled
``Check.lean``, which imports the user's modules, and read the text that its
``example : G := G_proof`` and ``#print axioms`` printed. So a few macros in
``User.lean`` that rewrote those two commands certified proofs of ``True`` for
a false postcondition, and so did a theorem of the goal added by a command
with ``debug.skipKernelTC`` and checked by no kernel, in the proof file or in a
module it imports. Certification now checks the compiled modules with a
program that elaborates none of the user's source: the kernel replays every
module of the project a proof imports, into one environment with the
toolchain's modules imported once, the proof's type must be exactly its goal, and its axioms are collected from the constants it uses. A failing
proof also no longer fails every function of the project: each function is
certified on its own goals (:doc:`book/part-ii/ch17-backends-modular-calls`).

**Lean goals keep their grouping.** The Lean export placed parentheses by a
precedence table of its own, not Lean's, so ``(a ^ b) + 1`` became
``a_0 ^^^ b_0 + 1``, which Lean reads as ``a ^^^ (b + 1)``. With
``r = (a ^ b) + 1`` and ``s = a ^ (b + 1)``, a Lean proof certified the false
``cppverify::check(r == s)``. A term of numerals alone was read in Lean's
``Nat``, so a proof certified ``cppverify::check(2 - 3 == 0)`` too, ``2 - 3``
being 0 there. Machine division by zero meant Lean's 0, not the value the
solvers and the counterexample checker give. Every operator now keeps its
grouping under Lean's precedence, every numeral has its type
(``(3 : Int)``), and division by zero is SMT-LIB's (``BitVec.smtUDiv``,
``BitVec.smtSDiv``)
(:doc:`book/part-ii/ch17-backends-modular-calls`).

Failures that were not real
~~~~~~~~~~~~~~~~~~~~~~~~~~~

These made 0.1.1 report a failure, or reject a function, for C++ that is
correct.

**Loops that never repeat.** A loop whose condition is the constant false, as in
``do { ... } while (0)`` macros, forgot the state it changed, and the code
after it could fail for values it never produces. Its state now carries over
(:doc:`language/functions-loops`).

**Loops that initialize local storage.** Every iteration of a loop after the
first saw the local storage the earlier ones wrote as uninitialized, so a
loop filling a local array failed its ``initialization`` check, at the
invariant that stated what it had written or at a read after the loop. What
was initialized before a loop now stays initialized, and an invariant holds
at the head of each iteration with its definedness, which shows the elements
it reads initialized and in bounds (:doc:`language/functions-loops`).

**Loops that write local storage.** A loop that wrote a local array, a local
record, a ``new`` object, or a local through a reference forgot the value of
every object, so a claim about a local the loop never touches failed after
it. Such a loop now writes only the objects it stores to, as a loop over
parameters always did (:doc:`language/functions-loops`).

**Calls that write a record.** A call whose footprint is a record
parameter's object, as a member function's default ``modifies(*this)`` is,
framed its bytes with a quantified relation, and a claim the call
falsifies often ended ``solver.timeout`` instead of a counterexample. The
object is now its leaves, each one cell, and such a claim fails in a few
seconds (:doc:`language/structs`).

**Null minus null.** The difference of two null pointers failed its
``pointer-difference`` check; it is 0, as C++ defines (:doc:`language/pointers`).

**C++20 shifts.** A signed left shift followed the C++17 rule in every mode, so
``-1 << 1`` failed under ``-std=c++20``. From C++20 it is the value C++20
defines (:doc:`language/integers`).

**Enumeration ranges.** A value of an enumeration without a fixed underlying
type could take values outside its range, so true claims failed with values
such as ``c = 4294967295``. Every such value is now assumed to be in the
range C++ gives it (:doc:`language/integers`).

**Values read through** ``new`` **pointers.** ``*p + 1`` on a pointer from ``new``
was rejected as arithmetic on the pointer; values read through such a
pointer are now ordinary integers (:doc:`language/dynamic-storage`).

**Out-parameters.** Passing storage that is not initialized yet to a function
that writes it (``int a; init(a);``) was a failure, or stopped the file. A
reference or pointer parameter whose storage the body writes before it reads
it is now an out-parameter: callers may pass storage not yet initialized,
the function's reads of it are checked against what it wrote, and the parts
it writes on every path, and those its postconditions read, are initialized
after a call. A call that passes such storage to a parameter the callee may
read first is ``Unresolved`` with reason ``construct.unsupported``
(:doc:`language/pointers`). A constructor that calls a member function
writing its object no longer fails its frame check.

**One condition, one choice.** Every ``cv::choose`` was a choice of its own, so
``cv::choose(k, k > n) == cv::choose(k, k > n)`` failed with a counterexample,
and so did a choice over memory compared across a write to another object.
Chooses whose conditions are written alike are now one choice, a choice
keeps its value across a write that leaves what its condition reads as it
was, and a counterexample may give one choice two values only where
something it reads differs (:doc:`book/part-ii/ch13-spec-and-proof-functions`).

**Choices in counterexamples.** A counterexample could use a value of
``cv::choose`` that its body excludes, so true claims about a choice failed.
Every choice a counterexample uses is now checked against its body
(:doc:`book/part-ii/ch13-spec-and-proof-functions`).

**Reads clauses over a choice.** A spec whose body applies ``cv::choose`` to
memory failed its ``cppverify::reads`` check (``calls choose, which reads the
heap without a reads clause``), although its frame held every cell the choice
reads. The check now follows the loads of the choice's body, and the facts a
spec's checks assume, its induction hypothesis included, reach the
applications inside a choice too (:doc:`language/ghost-proofs`).

**Vacuity findings of downgraded results.** A result that is ``Unresolved``
because a fact it relies on is not established could still be marked
``[vacuous]``, from that very fact, and whether it was depended on the
solver's search. Such findings are now dropped
(:doc:`book/part-ii/ch16-when-verification-fails`).

**Callers of functions proved in Lean.** With ``--lean-fallback``, a function
proved by Lean, or by Z3 and Lean together (``Proved (z3+lean)``), did not
establish its contract, so the callers Z3 proved were ``Unresolved`` with
reason ``callee.contract``. Its contract now holds for them as a verified
function's does (:doc:`book/part-ii/ch17-backends-modular-calls`).

**Slices passed through a copy.** A function that requires ``valid(p, n)``
accepted an argument only when it was written as a parameter plus an offset,
as in ``first(a + 1, 3)``. Other arguments failed with a counterexample, even
when the program was correct:

- a copy of such a pointer (``const int *q = a + 1; first(q, 3);``);
- a choice between pointers (``c ? a + 1 : b``);
- a pointer stepped in a loop;
- a result whose contract says where it points.

Such an argument is now accepted when its elements lie in one of the caller's
objects (:doc:`language/pointers`).

**Callee frames inside the caller's.** A call could fail its ``frame`` check
although the callee writes only cells the caller may write, in two cases:

- a callee that writes its one object (``modifies(*p)``) passed a cell the
  caller may write, as in ``set(a + 2, 5)`` under ``modifies(a[2])``;
- a pointer copied into an object the caller may write, as in
  ``int *q = a + 2; set(q, 5);`` under ``modifies(*a)``.

The callee's footprint is now compared with the caller's frame cell by cell
(:doc:`language/pointers`).

**An empty extent inside another object.** Two address parameters of which
one has a ``valid`` extent are disjoint over their extents, which allows an
empty extent anywhere; the check of the pair over one object each was made as
well, so ``touch(b, &b->len, 0)``, an empty extent into ``*b``, failed its
``aliasing`` check. Only the extents are compared now (:doc:`language/pointers`).

**A record member named whole in** ``cppverify::modifies``.
``cppverify::modifies(p->left)``, for a member that is a record or an array,
was taken for one cell holding the whole member. A call ``reset(&p->left)``
of a function that may write its object failed its ``frame`` check, and a
call of the function itself could not be verified (``obligation lowering
failed: ... (invalid sort in obligation IR)``). The footprint is now the
bytes of the member (:doc:`language/structs`).

**Lean goals that could not be proved.** In a Lean goal a quantifier took
everything after it into its body, which made a goal with a quantified fact
before its conclusion say more than its obligation: the goal of a call that
must establish ``cv::pre(cv::forall(k, 0, n, k >= 0) && n < 8)`` had no
proof. A signed right shift of a signed right shift lost its parentheses, and
a spec applied under a quantifier, as in
``cv::forall(k, 0, n, total(k) >= 0)``, had its definition stated with ``k``
outside the quantifier: neither project built. ``decide`` could not evaluate
a machine comparison such as ``cppBvSlt``. Quantifiers are now closed before
what follows them, every operator keeps its grouping, a definition under a
quantifier is stated for every value of its variable, and ``decide``
evaluates the machine comparisons at constants
(:doc:`book/part-ii/ch17-backends-modular-calls`).

C++ that compiles now
~~~~~~~~~~~~~~~~~~~~~

**Contracts in templates.** A template whose contract depends on its
parameters did not compile. Its contracts now compile and are instantiated
with it (Templates, below), and a template without contracts no longer stops
the file (:doc:`language/functions-loops`).

**Apple's assertion macros.** On Apple targets ``<AssertMacros.h>`` defines a
``check(assertion)`` macro, which turned every ``cppverify::check(...)`` after
it into ``error: expected unqualified-id``. ``-fverify-contracts`` now defines
``__ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES`` to ``0`` on Apple
targets unless the command line defines it, so the header defines only its
``__Check``, ``__Require``, and ``__Verify`` names (:doc:`language/syntax`).

**Records through pointers.** Through a pointer, 0.1.1 reached only a record's
direct fields (``p->x``). A nested field (``p->inner.y``), a field of an
element (``p[k].x``), and an element of an array member (``r->buf[i]``) were
errors, so a ring buffer, a fixed-capacity stack, or any record that holds its
storage inline could not be verified. Each of them is now a heap cell, at any
depth: code can read and write it, contracts and ``cppverify::modifies`` can
name it, and a reference can bind to it. Each index is checked against its own
array, so ``r->buf[8]``, which has the address of the next field, is still an
error (:doc:`language/structs`).

**Pointers into records.** A pointer into the object a pointer addresses was an
error: a member array passed to a buffer function (``first(r->buf, 8)``), a
pointer walking it (``for (const int *q = r->buf; q != r->buf + 8; ++q)``),
and the address of an element, a field, or a nested record (``&r->buf[i]``,
``&r->head``, ``&r->inner``). The address of an element of a parameter's own
buffer (``&a[2]``) was an error too. These are supported now. A pointer into
a record may address only the array, field, or record it points into:
accesses, steps, pointer differences, and call arguments through it are
checked against that subobject, so ``q[8]`` past ``r->buf`` is an error,
though it lies in ``*r``. One formed in an operand that ``&&``, ``||``, or
``?:`` evaluates only on its own path is checked only there, so ``i < 8 &&
&r->buf[i] == q`` needs nothing of ``i`` when ``i >= 8``
(:doc:`language/structs`).

**Records through references.** A reference to a record (``Counter &c``,
``const Counter &c``), as a parameter or a local, was an error
(``unsupported C++ type in verification: Counter &``), so the free function
form of a method on an object, ``bump(Counter &c)``, could not be verified.
A reference to a record is now a pointer to it that is never null and never
reseated: ``c.n`` and ``c.buf[i]`` are cells of the object, ``&c.n`` and
``c.buf`` point into it, ``cppverify::modifies(c)`` is the whole object, and
a reference can be bound to ``*p``, ``p->left``, ``a[i]``, or another
reference (:doc:`language/structs`).

**Member functions.** Contracts on a member function written in its class
were ignored with a warning, and one defined outside its class was an error
(``member function verification is unsupported``). A member function of a
class without bases or virtual functions is verified now, as a function of
``this``: fields are cells of the object, ``c.bump()`` passes ``&c``, its
clauses may name members declared after them (the complete-class context of
C++26 contracts), and a non-const one without ``cppverify::modifies`` may
write its object. Virtual functions, destructors, and conversion functions
are errors naming the function (:doc:`language/structs`).

**Constructors.** A constructor was an error (``constructors are not
verified yet``), and a class with one was not a supported type, so a local
of it could not be declared. A constructor of a trivially copyable class
without bases is verified now: its object is the caller's storage, every
member uninitialized at entry, its member initializers run in declaration
order with in-class initializers for the members it does not name, and it
must initialize every member by its end. ``Counter c(5);`` passes ``&c`` and
leaves an initialized object; an implicit or defaulted default constructor
runs its members' initializers in place (:doc:`language/structs`).

**Class invariants.** A ``cppverify::type_invariant`` held only for records
passed and returned by value; member functions and constructors ignored it.
On a class now, every public member function assumes it on entry and must
restore it, every constructor must establish it, and it is checked at every
call, internal ones included; an extent of a pointer field in it is assumed
on entry. An object passed by reference or pointer satisfies it on entry and,
when mutable, at exit, where before only a record passed by value did
(:doc:`language/structs`).

**Templates.** The contracts of templates were ignored with a warning, so
no specialization was verified, and a call to one from verified code was an
error. Each specialization a translation unit instantiates is now verified
as a function of its own, named with its arguments (``twice<int>``,
``Box<int>::get``), with its contract instantiated as its body is, loop
contracts, assertions, and ghost code included, and a class template's type
invariants with the class; a diagnostic about it notes where it is
instantiated, and a contracted template, or member of a class template,
that nothing instantiates is reported. ``cv::post(cv::result > 0)`` and ``cv::old(x) > 0``
of a template's type did not compile (``invalid operands to binary
expression ('T' and 'int')``) (:doc:`language/functions-loops`).

**std::min and std::max.** In a contract they ended ``Unresolved:
obligation lowering failed: f (missing spec definition: fn_...)``, as did
any function using a ``constexpr`` helper that could not be lifted. Of two
integers they now mean what the standard says, whatever the library, in
contracts and in code; any other function of the standard library is an
error naming it, a helper that cannot be lifted is named in the verdicts
that rely on it, and a lifted helper's references to ``const`` integers
stand for their values (:doc:`language/functions-loops`).

**Member operators.** For a member ``operator==``, ``a == b`` passed ``a``
for the operator's parameter and ``b`` as an argument beyond it, an error,
and an operator returning ``*this`` by reference (``Money &operator+=``) was
an unsupported type. A member operator now takes its first operand as its
object, and one returning its own object is verified as returning nothing. A
callee with local objects of its own can now also be lent the caller's local
objects (:doc:`language/structs`).

**Records in memory by value.** A record kept in memory, a local object or
one a pointer or reference addresses, could not be passed, returned, or
(through a pointer) copied by value (``aggregate value use of an automatic
object is unsupported``, ``unsupported aggregate field base expression``).
Such a value is now its fields, each read where it is, with the bounds,
validity, and initialization checks of that read (:doc:`language/structs`).

**Extents of pointer fields.** ``cv::valid(s->data, s->len)`` was an error
(``valid marker requires a bare complete-object pointer and an integer element
count``), so a record that describes a buffer by a pointer and a length (a
string view, a span) could not be verified. A pointer field of the object a
pointer or reference parameter addresses now takes an extent as a pointer
parameter does: accesses through it are checked against the extent, a call
checks the extent at its arguments, and the buffer is disjoint from the other
parameters' objects by default (:doc:`language/structs`).

**Local objects passed to callees.** A local record passed to a reference
parameter (``bump(c)``), and the address of any local passed to a pointer
parameter (``reset(&c)``, ``inc(&x)``, ``inc(&c.n)``), were
``construct.unsupported`` or errors (``raw address-of is unsupported until
lexical lifetime and escape effects are modeled``). They are verified now
when the callee keeps no address of the local, which the call checks: it
stores none in memory, returns none, frees none, and passes one only to
callees that keep none. The callee writes only its footprints in the local,
and every field of a record must be initialized, since the callee reads it as
initialized (:doc:`language/structs`).

**Calls in expressions.** A call was supported only as a statement or a whole
initializer, assignment, return value, or argument; ``return inc(x) * 2;``,
``if (try_get(out, ok))``, ``while (next(i) < n)``, and ``sq(a) + sq(b)``
stopped the file with ``executable call is unsupported in this expression
context``. A call of a function whose result is a scalar or a pointer may now
stand anywhere in an expression or condition, and runs where C++ evaluates
it: a ``&&``, ``||``, or ``?:`` operand's call only on its path, a loop
condition's at every test. Where C++ leaves the order of operands open, a call
that may write what another operand reads is an error at the expression,
and an assignment's right operand is evaluated before its target, as C++17
says (:doc:`language/functions-loops`).

**Range-based for loops.** ``for (int v : a)`` stopped its function
(``unsupported statement: CXXForRangeStmt``). A range-based ``for`` loop over
an array (a local array, an array member, a constant table) is now verified,
its variable a copy of each element or a reference to it, and its contract
names the position with the new construct ``cppverify::index``; without a
measure it decreases the elements left (:doc:`language/functions-loops`).

**Lookup tables.** A read of a global or ``static`` array, or of a string
literal, was an error (``the global array 'table' is unsupported``), which
ruled out the tables at the heart of CRC, base64, and UTF-8 code. An element
of a constant table, a ``const`` or ``constexpr`` array with a constant
initializer or a string literal, is now the value its initializer gives it,
and each index must lie in its array (:doc:`language/pointers`).

**assert and calls that do not return.** ``assert(c)`` stopped its function
(``unsupported statement: ParenExpr``), and a call to ``abort`` or ``exit``
was an error (``call to function without a verification contract``).
Reaching a failed ``assert`` or a call that does not return is now a failure
of the new kind ``unreachable``, and after ``assert(c)``, ``c`` holds; with
``NDEBUG`` an ``assert`` is nothing. An uncontracted ``constexpr`` helper's
``assert`` is checked at each call. ``[[assume(e)]]`` and
``__builtin_assume(e)`` are proved, then assumed. A statement that only
computes a value is computed, with its checks (``x + 1;`` was ``unsupported
expression statement``). LLVM's ``alignTo``, ``maxUIntN``, and
``SignExtend64`` verify with their asserts (:doc:`language/functions-loops`).

**Small forms of everyday C++.** Each of these stopped its function:
character literals (``'0'``, ``L'A'``), a ``consteval`` call and an ``if
constexpr`` condition, a template value parameter used as a value, a default
argument, ``static_assert``, a local ``typedef`` or ``using``, a local class
or enumeration, ``__builtin_expect``, ``return Pt{a, b};``, and ``auto [a, b]
= p;``. Each is now what C++ makes it: a literal or a constant its value, a
default argument evaluated at the call, a declaration nothing at run time,
``__builtin_expect(e, c)`` the value of ``e``, an initializer list the fields
in order, and a structured binding a copy whose fields the bindings name
(:doc:`language/integers`, :doc:`language/structs`,
:doc:`language/functions-loops`).

**Expressions that evaluate nothing at run time.** ``noexcept(e)``, a
requires-expression, a concept, a type trait such as ``__is_same(T, U)``,
``offsetof``, and ``__builtin_LINE()`` stopped their function
(``unsupported expression: CXXNoexceptExpr``). Each is now the value Clang
computes for it (:doc:`language/functions-loops`).

**Pointer steps and reused names.** ``++p``, ``p--``, ``p += n``, and
``p -= n`` on a pointer were errors (``pointer increment/decrement is
unsupported``, ``pointer compound assignment is unsupported``), and so was a
local that took the name of a parameter or of another local, even in a later
block, as two ``for (int i = ...)`` loops in one function do (``local variable
shadowing is unsupported``). A pointer step as a statement is now the
assignment it abbreviates, with the checks of that step, and each declaration
is a variable of its own (:doc:`language/pointers`,
:doc:`language/functions-loops`).

**Switch statements and loop forms.** ``switch`` stopped its function with
``unsupported statement: SwitchStmt``, and so did ``break`` and ``continue``
in a ``do`` loop, a condition declaration (``while (int k = next(i))``), a
``for`` loop without a condition, and a comma expression as a statement (the
increment ``i++, j += 2``). All of them are verified now, with C++'s meaning:
a switch runs from the matching label, or from ``default``, to a ``break`` or
its end, falling through labels, with an init statement, a condition
variable, GNU case ranges, and nested loops and switches; a ``break`` in a
``do`` loop's first iteration skips the loop and a ``continue`` goes to its
condition. Specs and lifted ``constexpr`` helpers may switch too. A label
inside another statement of its switch (Duff's device) and ``[[assume]]``
are errors at the statement (:doc:`language/functions-loops`).

Running cpp-verify
~~~~~~~~~~~~~~~~~~

**Counterexamples after a loop.** A failure whose counterexample passed
through a loop looked like any other, though its state there came from the
loop's invariants and no execution need reach it: the first loop most users
write, without an invariant, failed with ``c = 0`` after ``while (c < n)``.
Such a failure now says so in a note, and unrolling each loop then looks for
an execution that fails the same check within ``--confirm-bound`` iterations
(default 10): it gives that execution, or says that no execution fails the
check (when unrolling proves it) or that none fails it within the bound. The
execution it gives passes the failing checks before this one, and a check
that holds in every execution that passes them is noted with an earlier
check that fails. A failure of a function whose loop has no
``cppverify::decreases`` names that loop too
(:doc:`language/functions-loops`).

**Every failure of a function.** A function reported only its first failing
check. ``--max-failures=N`` reports the first ``N`` (``0``: every one), each
with its own counterexample and notes; a check after a failure is reported
only when an execution that passes the earlier failing checks fails it, as
Dafny reports every failing assertion (:doc:`language/tooling`).

**A summary, and what to print.** A run now ends with one line that counts
its verdicts by kind, with the reasons of the unresolved ones and the time it
took (``Summary: 12 verified, 1 failed, 2 unresolved (spec.fuel 1,
solver.timeout 1) in 3.2 s``). ``--quiet`` prints only what needs attention,
``--list-functions`` lists what a run would verify without verifying it,
``--function=PATTERN`` reports only the functions a glob pattern matches,
with the verdicts a whole run gives, and
the ``Verified: spec axiom: f`` line of a spec that needs no check is printed
only with ``--verbose``. ``--help`` shows the default of ``--timeout``
(:doc:`language/tooling`).

**Ctrl-C stops the run.** Ctrl-C printed an LLVM crash report and the run went
on, or crashed. It now stops every solver at once, reports each unfinished
function as ``Interrupted``, and exits with status 130
(:doc:`language/tooling`).

**Options select their backend, and unused options are errors.**
``--lean-out`` and ``--lean-project`` select Lean and ``--unroll`` selects BMC;
an option the run would not use, such as ``--unroll`` with ``--backend=z3``, or
``--timeout`` and the other solver budgets with Lean export, which runs no
solver, is an error that names what it needs, where it was ignored
(:doc:`language/tooling`).

**Compiler errors stop their file, and headers are C++.** An error in a command
line was printed and then ignored, and a ``.h`` input was compiled as C. Now
the file with the error is not verified and ``cpp-verify`` exits with status 1,
and a header is C++ (:doc:`language/tooling`).

**Crash reports go to cpp-verify.** A crash asked for a report on LLVM's issue
tracker. It now names https://github.com/SwayamInSync/cpp-verify/issues/, in
``cpp-verify`` and in the ``clang++`` it is built with (:doc:`language/tooling`).

**Long expressions.** An expression with hundreds of operations used memory
with the cube of its depth, and one with thousands crashed. The cost is now
quadratic (a 250-term sum lowers in about 5 s instead of 120 s), and an
expression nested more than 256 operations deep is reported where it is
(:doc:`language/limitations`).

**Large functions take far less memory.** Each check of a function restated
every assumption before it as a copy, and the check's query, the function's
complete goal, and that goal's query copied them again, so memory grew with
the number of checks times the length of what came before them: verifying the
ULEB128 case study took 14.9 GB, and lowering it 53 s. Terms now share what
they repeat: the case study verifies within 0.9 GB and lowers in 10 s, and
``safe_fib.cpp`` lowers in 7 s within 0.35 GB instead of 16 s and 4.7 GB.
Verdicts, archives, hashes, and IR dumps are unchanged; a Lean export names a
large subterm that one statement repeats once (:doc:`case-studies/llvm-uleb128`).

**Errors point at the code.** An error about a construct the verifier does not
represent named only the function, as in ``error: pick: unsupported statement:
SwitchStmt``. It now gives the file, line, and column, and shows the line with
a caret under the construct, as a compiler error does; its JSON record carries
the range (:doc:`language/tooling`).

**Errors name the construct, once.** The message gave Clang's class name
(``unsupported statement: CXXThrowExpr``), called a lambda ``aggregate
initialization and copying``, and called a string literal used as a pointer
``array-to-pointer decay of automatic storage``; each use of a variable whose
initializer was rejected added ``read of uninitialized local value``, and a
call without a contract was reported twice. The message now says what C++
calls the construct (``throw is unsupported: exceptions are not modeled``,
``lambdas are unsupported``), and each is reported once
(:doc:`language/tooling`).

**An unsupported construct costs its function alone.** One construct the
verifier does not represent, such as a ``switch``, stopped the file: no
function of it was verified. Now that function is ``Unresolved`` with reason
``construct.unsupported``, its first error's JSON record carrying the verdict,
and every other function is verified. A caller that relies on its contract is
``callee.contract``; a function whose contract is not represented leaves a
call of it ``construct.unsupported``; a function that reaches a spec the
verifier does not represent is ``construct.unsupported``. The exit status is 1
as before (:doc:`language/tooling`).

**Z3 errors.** A Z3 call that failed went unnoticed, and a later step could
report something unrelated. The query now ends ``Unresolved`` with reason
``encoding.failed`` and Z3's message (:doc:`language/tooling`).

**Parallel runs.** With more than one job, a function waiting for its own
queries could run another function's long query, delaying its result and
spending its ``--function-timeout``. A waiting function now runs only its own
queries (:doc:`language/tooling`).

**Documentation for each version.** The site showed only ``main``, so a user
of a release read about features their binary did not have. Its root now
documents the latest release, ``/X.Y/`` each release series (``/0.1/`` is
0.1.1), and ``/dev/`` the development version on ``main``. A banner on every
page names its version, and each release's archive and notes link to its own
series.

**Results that depended on load.** The complete query of a function without
spec functions had 500 ms before its obligations were solved one by one. On a
loaded machine, or in a slower build, it could give up on a counterexample
that an idle machine found in that time, and an obligation whose search does
not end then ran to the timeout: a false claim took minutes and ended
``Unresolved`` with ``solver.timeout``. That query now gets a fixed amount of
solver work (6 million Z3 resource units), with the timeout only as a bound
in time, so it stops where it would on an idle machine
(:doc:`language/tooling`).

**cvc5 1.4.** Every query over sets, multisets, and maps failed with cvc5 1.4,
which requires extended arrays for constant arrays; such a query now enables
them itself (:doc:`language/tooling`).

**Lean proofs stay with their goals.** A goal of a Lean project was named by
its function and its position among the function's obligations, and a spec
body by the position of its module in the file. Reordering two
postconditions gave each proof the other's goal, which the kernel rejected,
and a function inserted earlier in the file renamed the spec bodies every
later proof unfolds. A renamed function lost its proofs, and proofs of goals
that were gone stayed among the proof files. A goal is now named by its
function and the hash of its statement, its proof file lives in the
function's directory and records that hash, and every regeneration puts
each proof with the goal of its statement: a renamed function takes its
proofs along with the names they use, a proof whose statement changed or
whose function is gone is kept in ``Stale/`` with a note, and it comes back
when a goal has its statement again. A fallback run leaves the proofs of
what its solver settles alone. ``--lean-prune-stale`` deletes what
``Stale/`` keeps. A project 0.1 generated is moved to the new names with
its proofs (:doc:`book/part-ii/ch17-backends-modular-calls`).

**Lean goals as hypotheses.** A Lean goal was one disjunction, the negation of
every assumption before what it must show, and a proof picked its way to the
conclusion by counting disjuncts (``right; right; right``) with nothing to
say which was the precondition and which a callee's postcondition. Each goal
now also has a readable form, its assumptions as hypotheses named by where
they come from, such as ``h_pre_1``, ``h_call_next_2``, ``h_inv_1``, or
``h_x_1`` for the definition of ``x_1``, and a bridge from that form to the
goal, which the kernel checks with the generated file. A new proof file
starts from the readable form with every name introduced; a proof of the
goal itself still checks (:doc:`book/part-ii/ch17-backends-modular-calls`).

**Lean proofs cppverify_auto finds.** Every goal of a Lean project was a stub,
each ``True`` included, so a project of a few functions needed tens of proofs
before it certified. Each new goal is now first given to ``cppverify_auto``, a
tactic the project carries in ``CppVerify/Auto.lean``: it tries ``grind``; then
memory stores as the functions they define and machine arithmetic as integers,
before ``grind``; then ``decide`` and ``simp_all``, each with a budget of its
own, and it keeps a step only when its proof uses Lean's foundations alone. A
goal it proves gets that proof, and the export counts them, as in
``Exported: lean obligation: next (cppverify_auto proved 3 of 3 goals)``;
certification checks those proofs like any other. Any other goal gets a stub
that says it was tried, and it is tried again only by a later revision of
``cppverify_auto``. Of the goals of the test suite that Z3 proves, it proves
90%. ``--no-lean-auto`` writes stubs only, and with ``--backend=lean``,
``--jobs``, which was an error there, sets how many Lean processes automation
and certification run at once. Certification also builds the
proofs side by side and checks them in one Lean environment: the 33 goals of
one test took 204 s and now take 12 s
(:doc:`book/part-ii/ch17-backends-modular-calls`).

**A Lean module per function.** A Lean project kept every goal of every
function in ``CppVerify/Generated.lean``, which every proof imported, so a
change to one function built every proof again, and certification compiled
every proof on every run. Each function's goals now have a module of their
own, ``CppVerify/Goals/<function>.lean``, the specs they apply are declared
once, in ``CppVerify/Specs.lean``, and a proof imports its function's goals,
``User``, and ``Auto``. A generated file is written only when its text
changes, and certification compiles a proof again only when it or a module
it imports changed: after a change to one of five functions, it compiles
that function's three proofs. ``lake build``, which failed for want of the
library's root module, builds every proof. A ``User.lean`` that 0.1 wrote,
which imports ``CppVerify.Generated``, keeps working
(:doc:`book/part-ii/ch17-backends-modular-calls`).

**Collections in Lean.** A function whose obligations use a ``seq``, ``set``,
``multiset``, or ``map`` was ``Unresolved`` with reason ``logic.unsupported``
under ``--backend=lean`` and ``--lean-fallback``. They are now Lean values of
core types: a sequence is a ``List Int``, a set its membership test
(``Int → Bool``, since a set may be infinite), a multiset its counts, and a
map the value at each key it holds. Each operation is a function of the
generated prelude with the total meaning of ``<cppverify.h>``, and lemmas
state what each means for ``simp``, ``grind``, and proofs by hand.
``cppverify_auto`` revision 2 adds three steps after the others: machine
equalities as integer facts, collection equality element by element, and the
definition instances a goal states, by the bodies they name. Of the 112 goals
over collections in the test suite that Z3 proves, it proves 104, and
revision 1 86; most of the rest need induction over a recursive spec. Of
every goal the suite exports that Z3 proves, it proves 93.3%, where revision 1
proves 90.4%, and none fewer. Stubs that revision 1 wrote are tried again
(:doc:`book/part-ii/ch17-backends-modular-calls`).

**Spec functions as Lean definitions.** Every spec function of a Lean project
was opaque, known to a goal only through the definition instances it states,
so a goal that needed a spec at another argument, or induction over it, could
not be proved. A spec is now a Lean definition when the pinned Lean proves
that it terminates by its ``cppverify::decreases`` measures, with exactly the
spec's value at every argument, and stays opaque otherwise. A proof may unfold
it or argue by induction over its recursion, and ``cppverify_auto`` revision 3
evaluates its applications at known arguments. Revision 3 also reads the
division and remainder of contracts and specs by their definitions, which
proves goals such as ``a / 2 >= 2`` for ``a >= 4``. Lean's verdict on each
spec is kept in the project, so a later export tries nothing
(:doc:`book/part-ii/ch17-backends-modular-calls`).

**Lean projects from archives.** An obligation archive could reach Lean only
as the unchecked scratch-pad, and a bounded archive of BMC not at all.
``--obligation-in`` with ``--lean-project`` now writes a Lean project as a
source run of the same program does, with the same goals, specs, and proof
files, so a proof written for the source certifies the archive's goal;
``--lean-certify`` reports each module whose goals all certify as ``Proved
obligations`` ``[backend=lean]``, since replay checks a module alone. A
bounded module states its bound with its goals, in a project and in the
scratch-pad, and its result is read as BMC reads one: it is ``BoundedSafe``
when every goal but some unwinding goal certifies. Archives record each spec
function's termination measures and the source of each assumption of a goal,
which a project needs to define the spec and to name the goal's hypotheses;
a module keeps the specs its specs' measures apply
(:doc:`book/part-ii/ch17-backends-modular-calls`).

**Counterexamples confirmed in Lean.** A counterexample the solver found was
checked by cpp-verify's own evaluator only. A fallback project now holds the
refutation of each certified failure, the failing goal stated as the project
states it and proved false at the model's values; ``--lean-certify`` checks it
with the kernel, and a failure it shows reads ``(confirmed in Lean)``. A
counterexample Lean cannot decide, as one that applies a ``cppverify::choose``,
stays a failure with a warning, and one Lean decides the other way would be
``Unresolved``, a disagreement, never a failure. Lean decides a quantifier
over a range of at most 4096 integers by trying each one, within the
heartbeats of a step of ``cppverify_auto``. The release gate's Lean row now
decides every case of its matrix: each valid one certified, each invalid one
refuted (:doc:`book/part-ii/ch17-backends-modular-calls`).

**Lean 4.35.0.** Lean projects pin ``leanprover/lean4:v4.35.0``. A project 0.1
generated, pinned to ``v4.32.2``, moves to the new pin the next time cpp-verify
writes it, with a warning; a proof that no longer builds needs updating for that
Lean. Certification ran elan's default toolchain, which need not be the pin,
since elan picks one by the working directory. It now names the pin, and
refuses a ``lake`` outside elan that reports another Lean
(:doc:`language/tooling`).

**clang-format.** A range footprint is written ``p[lo : n]``, not ``p [lo:n]``
(:doc:`language/tooling`).

Data formats
~~~~~~~~~~~~

Archives are ``cppverify.obligation/3``, which adds measures and the
sources of assumptions and reads ``/2`` and ``/1``; JSON diagnostics stay
``cppverify.diagnostic/1``. A module whose specs' measures apply other specs
keeps them, so its module hash changes; per-obligation hashes, and the proof
cache keyed by them, do not. JSON records may carry the status
``proved-obligations`` (archive replay) and the reason ``interrupted``
(Ctrl-C). Lean projects pin ``leanprover/lean4:v4.35.0``, and each proof
file records the hash of its goal's statement (``cppverify-obligation-statement``
version 1, which leaves out the function's identity).

0.1.1
-----

A patch release of 0.1.0, on the same LLVM 23.1.3, with the same language and
data formats. Each fix changes how the verifier searches, or which entries the
proof cache keeps; none changes what a verdict means.

**Fixed: certified failures reported at once.** A false claim could take the
full query timeout, or end ``Unresolved`` with ``solver.timeout`` under load,
although the verifier had already found a certified counterexample for it.
Once a function's complete query is refuted, the individual obligations only
choose which failure is reported, the first in source order; they now get no
more time than the complete query had, and the complete query's
counterexample stands when they do not finish.

**Fixed: small counterexamples after a large one.** When the solver first
proposed a counterexample whose spec values are too large to compute
(``fibo`` at a billion, say), checking it used up the time of the search for a
small counterexample that follows, so a false claim could end ``Unresolved``
with ``spec.fuel`` on a loaded machine. The check's time is now its own. Such
a check still takes up to ``--certify-timeout``, so under heavy load the
result can still be ``spec.fuel``.

**Fixed: results that depended on earlier queries.** The Z3 backend solved
complete queries in one long-lived solver context, which with one job
(``--jobs=1``, as in the test suite) every function of a file shared. Z3 keeps
the state of the queries solved in a context, as far as an interrupted one
got, and that state steers its next search. On a loaded machine a false
claim could therefore end ``Unresolved`` with ``solver.timeout``, a file's
counterexamples could change from run to run, and after one function needed
an induction, every later query of the file only sought a proof. Every query
is now solved in a context of its own. A proof that fitted its time only in
an earlier query's context may now need a larger ``--timeout``.

**Fixed: counterexamples that only fast machines found.** When a model needs
spec values beyond the solver's unfoldings, the verifier tries the least and
greatest values the query allows for their arguments. It tried one end after
the other, and each end restarted from small steps after every overshoot, so
on slow cores the first end could use the whole of this probe's short budget,
and a false claim whose counterexample lay at the other end ended
``Unresolved`` with ``spec.fuel``. The ends now take turns, and each takes at
most about two checks per bit of its argument. This makes such results rarer,
not impossible: the probe keeps a short budget, so that it cannot hold up a
proof, and on a heavily loaded machine (the test suite on a 3-core macOS
runner) it can still run out.

**Fixed: proof cache pruning.** With ``--proof-cache`` and a limit small
enough to evict entries (``--proof-cache-max-entries``,
``--proof-cache-max-mb``), the cache was pruned after each function, which
could remove entries that functions verified at the same time had not looked
up yet. Whether such a function reported a corrupt entry (``cache.corrupt``)
or proved its obligations again then depended on scheduling. The cache is now
pruned once, after the run's last lookup, and a failure to prune is a warning
instead of ``cache-error`` telemetry on a result.

The solver's search depends on its search order, which differs between
platforms, so these showed more often on macOS arm64 (the known issue of
0.1.0). Time budgets are still wall-clock: a claim whose proof or
counterexample needs more time than its budget can end ``Unresolved`` on a
slow or loaded machine, and a larger ``--timeout`` gives it more.

0.1.0
-----

The first public release of cpp-verify: a Clang-based deductive verifier for a
documented subset of C++, with first-class contracts that Clang parses and
type-checks.

**Built on** LLVM 23.1.3. Z3 4.13.4 is built in. cvc5 (tested with 1.1.2) and
Lean 4.32.2 are optional and found on ``PATH``.

**Install.** Archives for Linux x86_64 and macOS arm64 are attached to the
release on GitHub; each holds ``cpp-verify``, ``clang``/``clang++``,
``clangd``, ``clang-format``, and Clang's headers. The macOS binaries are not
notarized; if macOS refuses to open one downloaded with a browser, run
``xattr -dr com.apple.quarantine`` on the unpacked directory. On other systems,
including Windows, build from source with ``setup.sh`` or ``setup.ps1``
(:doc:`index`).

**Language.** Every construct is written qualified, ``cppverify::pre(...)``,
or through an alias, ``cv::pre(...)``. ``-fverify-contracts`` includes
``<cppverify.h>`` implicitly and reserves no word, so every standard header
compiles. Sources in the earlier keyword syntax convert with
``clang/tools/cpp-verify/cppverify-migrate.py`` (:doc:`language/tooling`).

**Verification.** Function and loop contracts, spec and proof functions,
ghost code, quantifiers, ``cppverify::choose``, triggers, mathematical
collections, behaviors, inductive predicates, and automatic induction, over
integers, flat records, abstract buffers, scalar references, and constrained
pointer lifetimes. Backends: Z3 (default), cvc5, a strict Z3 and cvc5
portfolio, a race of both, bounded model checking, and Lean export and kernel
certification. On the solver backends ``Verified`` is a proof, a failure
(``error: verification failed``) is a counterexample checked against the true
definitions, and anything else is ``Unresolved`` with a reason. BMC reports
``BoundedSafe`` when no failure exists within its bound, Lean export
``Exported``, Lean certification ``Certified`` or ``Proved (z3+lean)``, and a
``[[cppverify::trusted]]`` contract ``Trusted``.

**Editors.** clangd from this release gives hover, go to definition, find
references, rename, and completion inside contracts, and clang-format lays
clauses out one per line (:doc:`language/tooling`).

**License.** cpp-verify, like LLVM, is distributed under the Apache License
v2.0 with LLVM Exceptions. Each archive includes ``LICENSE.TXT`` and, for the
built-in Z3, ``LICENSE-Z3.txt`` (MIT).

**Data formats.** Obligation archives ``cppverify.obligation/2`` (reads
``/1``), JSON diagnostics ``cppverify.diagnostic/1``, and semantic hash format
v4.

**Not yet verified.** Member functions, templates, floating point,
exceptions, lambdas, virtual dispatch, ``switch`` and range-``for``, and the
standard library's containers. Contracts on member functions are ignored with
a warning (``-Wcontract-unsupported``). A contracted function that uses one of
the others fails closed: the run stops with an error naming the construct and
reports no verdicts for the file. Contracts are not saved in precompiled
headers.
The full boundary is in :doc:`language/limitations`.

**Known issue.** The solver's time budgets are wall-clock, and Z3 does not
always search the same way on every platform. On macOS arm64, a false claim
that is hard for the solver is sometimes reported ``Unresolved`` (reason
``solver.timeout`` or ``spec.fuel``) where Linux reports its counterexample
within the same budget. Such a result is never a wrong verdict, and a larger
``--timeout`` gives the solver more time to settle it. 0.1.1 removes four
causes of such results; a claim that needs more time than its budget can still
end this way on a slow or loaded machine.
