#!/usr/bin/env python3
"""Verify book sidebar has Part I / Part II boundaries with nested chapters."""
from __future__ import annotations

import re
import sys
from pathlib import Path

BUILD = Path(__file__).resolve().parents[1] / "build"
BOOK_INDEX = BUILD / "book" / "index.html"


def main() -> int:
    if not BOOK_INDEX.is_file():
        print(f"error: missing {BOOK_INDEX} — run build-docs.sh first", file=sys.stderr)
        return 1

    html = BOOK_INDEX.read_text(encoding="utf-8")
    # Only the left navigation sidebar (not the in-page table of contents).
    marker = '<div class="content">'
    sidebar = html.split(marker, 1)[0] if marker in html else html

    if "Part I — Foundations" not in sidebar or "Part II — CppVerify" not in sidebar:
        print("error: part titles missing from page", file=sys.stderr)
        return 1

    if 'href="part-i/index.html">Part I — Foundations</a>' not in sidebar:
        print("error: Part I link missing", file=sys.stderr)
        return 1

    # Part nodes are l2; chapters under parts are l3
    if not re.search(
        r'toctree-l2 has-children"><a[^>]+part-i/index\.html">Part I',
        sidebar,
    ):
        print("error: Part I is not a toctree-l2 parent", file=sys.stderr)
        return 1

    if not re.search(
        r'toctree-l3"><a[^>]+part-i/ch01-correctness-and-trust\.html">Chapter 1',
        sidebar,
    ):
        print("error: Chapter 1 is not nested under Part (toctree-l3)", file=sys.stderr)
        return 1

    # Flat layout: chapter as l2 immediately in book list without part-i/index parent
    if re.search(
        r"The CppVerify Book</a>.*?<ul>\s*<li class=\"toctree-l2\"><a[^>]+part-i/ch01",
        sidebar,
        re.S,
    ):
        print("error: flat chapter list under book (no Part boundary)", file=sys.stderr)
        return 1

    if "book-sidebar.js" not in html:
        print("error: book-sidebar.js not linked", file=sys.stderr)
        return 1

    print("ok: book sidebar has Part I / Part II (l2) with chapters (l3)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())