"""Prints the generated text of a Lean project: its prelude, its specs, and
each goal module in the order its Generated module imports them, the
functions' source order."""
import pathlib, sys

root = pathlib.Path(sys.argv[1]) / "CppVerify"
parts = [root / "Prelude.lean", root / "Specs.lean"]
for line in (root / "Generated.lean").read_text().splitlines():
    if line.startswith("import CppVerify.Goals."):
        parts.append(root / "Goals" / (line[len("import CppVerify.Goals."):] + ".lean"))
sys.stdout.write("".join(part.read_text() for part in parts))
