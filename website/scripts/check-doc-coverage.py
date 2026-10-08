#!/usr/bin/env python3
"""Check that the language reference and the book cover every feature.

Each cpp-verify construct (the words of CppVerifyConstructs.def, written
qualified), each ``<cppverify.h>`` collection operation, and each
verification construct below must appear in a C++ example of the language
reference and of the book.
Each ``cpp-verify`` option, backend, and reason code must be described in
both. A feature that lands without documentation then fails the test suite.
"""

import argparse
import pathlib
import re
import sys

CONTEXTUAL = [") by {"]
CONSTRUCTS = ["[[cppverify::trusted]]", "::ghost {", "valid(", "::calc {",
              "::decreases(*)", "::modifies(*", "[0 :", "do {", "new ",
              "delete ", "seq ", "set ", "multiset ", "map "]
COLLECTION_OPERATIONS = [".len()", ".push(", ".subrange(", ".contains(",
                         ".insert(", ".remove(", ".count(", ".unite(",
                         ".subset_of("]
BLOCK = re.compile(r"^(\s*)\.\. code-block::\s*(\S+)\s*$")


def cpp_examples(pages):
    found = []
    for page in pages:
        lines = page.read_text().splitlines()
        for index, line in enumerate(lines):
            match = BLOCK.match(line)
            if not match or match.group(2) != "cpp":
                continue
            indent = len(match.group(1))
            cursor = index + 1
            while cursor < len(lines):
                current = lines[cursor]
                if (current.strip() and
                        len(current) - len(current.lstrip()) <= indent):
                    break
                found.append(current)
                cursor += 1
    return "\n".join(found)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=pathlib.Path,
                        help="the llvm-project checkout")
    root = parser.parse_args().root

    constructs = (root /
                  "clang/include/clang/Basic/CppVerifyConstructs.def").read_text()
    keywords = re.findall(r'^CPPVERIFY_CONSTRUCT\(\w+, "(\w+)"', constructs,
                          re.M)
    main_cpp = (root / "clang/tools/cpp-verify/Main.cpp").read_text()
    options = sorted(set(re.findall(
        r"cl::(?:opt|list)<.*?>\s*\w+\(\s*\"([\w-]+)\"", main_cpp, re.S)))
    backend = (root / "clang/lib/Verify/Backend/VerifyBackend.cpp").read_text()
    reasons = sorted(set(re.findall(r'return "([a-z]+(?:\.[a-z-]+)+)";',
                                    backend)))
    backends = re.findall(r"expected ([\w, ]+), or (\w+)", main_cpp)
    backends = ([name.strip() for name in backends[0][0].split(",")] +
                [backends[0][1]]) if backends else []

    source = root / "website/source"
    reference = sorted((source / "language").glob("*.rst"))
    book = sorted((source / "book").rglob("*.rst"))
    reference_text = "".join(page.read_text() for page in reference)
    book_text = "".join(page.read_text() for page in book)
    reference_code = cpp_examples(reference)
    book_code = cpp_examples(book)

    missing = []

    def need(kind, name, terms, reference_in, book_in):
        for where, text in (("language reference", reference_in),
                            ("book", book_in)):
            if not any(term in text for term in terms):
                missing.append(f"{kind} {name}: no {where} "
                               f"{'example' if kind == 'construct' else 'text'}"
                               f" shows it")

    for keyword in keywords:
        need("construct", "cppverify::" + keyword, ["::" + keyword],
             reference_code, book_code)
    for construct in CONTEXTUAL + CONSTRUCTS + COLLECTION_OPERATIONS:
        need("construct", construct.strip(), [construct], reference_code,
             book_code)
    for option in options:
        need("option", "--" + option, ["--" + option], reference_text,
             book_text)
    for name in backends:
        need("backend", name, ["--backend=" + name], reference_text, book_text)
    for reason in reasons:
        need("reason", reason, [reason], reference_text, book_text)

    for line in missing:
        print(line)
    print(f"{len(keywords) + len(CONTEXTUAL) + len(CONSTRUCTS) + len(COLLECTION_OPERATIONS)}"
          f" constructs, {len(options)} options, {len(backends)} backends, "
          f"{len(reasons)} reason codes checked, {len(missing)} missing")
    return 1 if missing or not (keywords and options and reasons and backends) \
        else 0


if __name__ == "__main__":
    sys.exit(main())
