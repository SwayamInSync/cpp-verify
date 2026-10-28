# Security

## What matters most

For a verifier, the security-relevant bug is a **wrong verdict**: `Verified`
(or `Certified`) for a claim that does not hold, so that code others rely on
passes verification while it is wrong. Every `Failed` result carries a
counterexample the verifier has checked; a counterexample that does not
actually break the claim is a wrong verdict too.

Report one with the **Wrong verdict** issue form. If it lets a false claim
verify in a way that could be used to slip a defect past verification on
purpose, report it privately through GitHub's private vulnerability
reporting for this repository instead, when it is enabled (Security, Report
a vulnerability).

Include:

- the smallest input that shows it, with its contracts;
- the exact command line;
- `cpp-verify --version`, which names the Z3, cvc5, and Lean it used;
- the output with `--diagnostics-format=json`;
- for a query you suspect the solver of, the files `--dump-smt2=DIR` writes.

## Crashes and other bugs

A crash prints a stack trace and asks for a report: use the **Bug** issue
form. Like LLVM's tools, `cpp-verify` and `clang` are not hardened against
malicious input: a crash on a crafted file is a bug, not a vulnerability.

## Supported versions

Fixes go into the next release; a fix to a wrong verdict is also released
on the current release's branch (`release/X.Y`).
