#!/usr/bin/env python3
"""Check the C++ examples of the website, the book, and the design notes.

Every ``.. code-block:: cpp`` block (a ```` ```cpp ```` fence in Markdown) must
compile with cpp-verify, and when the next code block on the page is a
``text`` block that shows verdicts, verifying the example must give those
verdicts. A comment right before a block changes how it is checked; several
may be stacked (in Markdown, ``<!-- cppverify-example: ... -->``):

    .. cppverify-example: fragment         part of a larger program: not run
    .. cppverify-example: label NAME       remembered for later blocks
    .. cppverify-example: with NAME ...    compiled after the named blocks
    .. cppverify-example: after            compiled after every earlier
                                           block of the page that compiled
    .. cppverify-example: flags ARGS       extra cpp-verify arguments
    .. cppverify-example: fails NAME ...   these functions fail with a
                                           counterexample
    .. cppverify-example: unresolved NAME ...
                                           these stay unresolved

An example whose page shows no verdicts is verified too: every function
must verify, unless a comment says it fails or stays unresolved. Comments
are invisible in the rendered pages.
"""

import argparse
import concurrent.futures
import pathlib
import re
import subprocess
import sys
import tempfile

PRELUDE = ("#include <cstdint>\n#include <cstddef>\n"
           "using namespace cppverify;\nnamespace cv = cppverify;\n")
DIRECTIVE = re.compile(r"^\s*\.\. cppverify-example:\s*(\w+)\s*(.*)$")
MARKDOWN_DIRECTIVE = re.compile(
    r"^\s*<!--\s*cppverify-example:\s*(\w+)\s*(.*?)\s*-->\s*$")
BLOCK = re.compile(r"^(\s*)\.\. code-block::\s*(\S+)\s*$")
FENCE = re.compile(r"^(\s*)```(\S*)\s*$")
VERDICT = re.compile(
    r"^(Verified|Unresolved|BoundedSafe|Lowered|Trusted|Exported|Certified):"
    r" (.+?)(?=\s+\[|\s+\(|$)")
FAILED = re.compile(r"error: (verification failed|spec [\w ]+? failed): "
                    r"(.+?)(?=\s+\[|\s+\(|$)")


class Block:
    def __init__(self, page, line, language, text, directives):
        self.page = page
        self.line = line
        self.language = language
        self.text = text
        self.directives = directives


def directives_before(lines, index, pattern):
    directives = []
    back = index - 1
    while back >= 0 and not lines[back].strip():
        back -= 1
    while back >= 0:
        directive = pattern.match(lines[back])
        if not directive:
            break
        directives.insert(0, (directive.group(1), directive.group(2).split()))
        back -= 1
    return directives


def markdown_blocks(page):
    lines = page.read_text().splitlines()
    found = []
    index = 0
    while index < len(lines):
        match = FENCE.match(lines[index])
        if not match:
            index += 1
            continue
        indent = len(match.group(1))
        cursor = index + 1
        while cursor < len(lines) and not FENCE.match(lines[cursor]):
            cursor += 1
        body = [line[indent:] for line in lines[index + 1:cursor]]
        found.append(Block(page, index + 1, match.group(2) or "text",
                           "\n".join(body).strip("\n") + "\n",
                           directives_before(lines, index,
                                             MARKDOWN_DIRECTIVE)))
        index = cursor + 1
    return found


def blocks(page):
    if page.suffix == ".md":
        return markdown_blocks(page)
    lines = page.read_text().splitlines()
    found = []
    for index, line in enumerate(lines):
        match = BLOCK.match(line)
        if not match:
            continue
        indent = len(match.group(1))
        body = []
        cursor = index + 1
        while cursor < len(lines) and lines[cursor].strip().startswith(":"):
            cursor += 1
        while cursor < len(lines):
            current = lines[cursor]
            if current.strip() and len(current) - len(current.lstrip()) <= indent:
                break
            body.append(current)
            cursor += 1
        width = min((len(l) - len(l.lstrip()) for l in body if l.strip()),
                    default=0)
        text = "\n".join(l[width:] for l in body).strip("\n") + "\n"
        found.append(Block(page, index + 1, match.group(2), text,
                           directives_before(lines, index, DIRECTIVE)))
    return found


def verdicts(text):
    shown = set()
    for line in text.splitlines():
        line = re.sub(r"^\S+\.cpp:\d+:\d+: ", "", line.strip())
        match = VERDICT.match(line)
        if match:
            shown.add((match.group(1), match.group(2).strip()))
            continue
        match = FAILED.search(line)
        if match:
            shown.add(("Failed", match.group(1) + ": " + match.group(2).strip()))
    return shown


def run(cpp_verify, source, arguments, timeout):
    with tempfile.TemporaryDirectory() as directory:
        path = pathlib.Path(directory) / "example.cpp"
        path.write_text(source)
        try:
            done = subprocess.run([cpp_verify, *arguments, str(path), "--"],
                                  capture_output=True, text=True,
                                  timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, "timed out"
        return done.returncode, done.stdout + done.stderr


def name_of(verdict):
    status, name = verdict
    return name.split(": ")[-1].split()[0]


def check(cpp_verify, job):
    block, source, arguments, expected, fails, unresolved = job
    where = f"{block.page}:{block.line}"
    code, output = run(cpp_verify, source, ["--lower-only", *arguments], 300)
    if code is None or code != 0 or "error:" in output:
        return f"{where}: the example does not compile:\n{output.strip()[:1500]}"
    code, output = run(cpp_verify, source, ["--timeout=20000", *arguments], 900)
    if code is None:
        return f"{where}: verifying the example timed out"
    if not expected:
        wrong = []
        for verdict in sorted(verdicts(output)):
            status, name = verdict[0], name_of(verdict)
            if status == "Failed" and name in fails:
                continue
            if status == "Unresolved" and name in unresolved:
                continue
            if status not in ("Verified", "Trusted"):
                wrong.append(f"  {verdict[0]}: {verdict[1]}")
        if wrong:
            return (f"{where}: the example does not verify, and no comment "
                    f"says which functions fail or stay unresolved:\n" +
                    "\n".join(wrong) + f"\nactual output:\n{output.strip()[:2500]}")
        return None
    if code is None:
        return f"{where}: verifying the example timed out"
    missing = expected - verdicts(output)
    if missing:
        shown = "\n".join(f"  {status}: {name}" for status, name in sorted(missing))
        return (f"{where}: the page shows verdicts the verifier does not give:\n"
                f"{shown}\nactual output:\n{output.strip()[:2500]}")
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cpp-verify", required=True)
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("sources", type=pathlib.Path, nargs="+",
                        help="pages, or directories of .rst pages")
    options = parser.parse_args()

    pages = []
    for source in options.sources:
        pages += sorted(source.rglob("*.rst")) if source.is_dir() else [source]
    jobs = []
    for page in pages:
        page_blocks = blocks(page)
        labels = {}
        compiled = []
        for position, block in enumerate(page_blocks):
            if block.language != "cpp":
                continue
            modes = {name: values for name, values in block.directives}
            if "fragment" in modes:
                continue
            context = []
            if "after" in modes:
                context = list(compiled)
            for name in modes.get("with", []):
                if name not in labels:
                    print(f"{page}:{block.line}: unknown example label {name}")
                    return 1
                context.append(labels[name])
            text = "".join(context) + block.text
            for name in modes.get("label", []):
                labels[name] = block.text
            compiled.append(block.text)
            expected = set()
            following = page_blocks[position + 1:position + 2]
            if following and following[0].language == "text":
                expected = verdicts(following[0].text)
            jobs.append((block, PRELUDE + text, modes.get("flags", []),
                         expected, set(modes.get("fails", [])),
                         set(modes.get("unresolved", []))))

    failures = []
    with concurrent.futures.ThreadPoolExecutor(options.jobs) as pool:
        for failure in pool.map(lambda job: check(options.cpp_verify, job),
                                jobs):
            if failure:
                failures.append(failure)
    for failure in failures:
        print(failure, end="\n\n")
    shown = sum(1 for job in jobs if job[3])
    print(f"{len(jobs)} examples checked ({shown} against the verdicts their "
          f"pages show), {len(failures)} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
