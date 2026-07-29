#!/usr/bin/env python3

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys


VALID_FUNCTIONS = {
    "boolean_control",
    "mathematical_specs",
    "spec_boundary",
    "recursive_spec",
    "bitvector_operations",
    "narrowing_conversion",
    "widening_conversion",
    "quantified_valid",
    "heap_read",
    "heap_write",
    "default_nonalias",
    "bounded_read",
    "type_invariant_read",
    "safe_add",
    "complete_loop",
}

INVALID_FUNCTIONS = {
    "boolean_literal_invalid",
    "quantified_invalid",
    "heap_write_invalid",
    "bounded_read_invalid",
    "overflow_add",
    "overflow_subtract",
    "overflow_multiply",
    "overflow_negate",
    "division_by_zero",
    "division_overflow",
}

EXPECTED_STATUS = {
    **{name: "verified" for name in VALID_FUNCTIONS},
    **{name: "failed" for name in INVALID_FUNCTIONS},
}

# cvc5 is allowed to be incomplete on quantified and inductive proofs. These
# cases must remain unresolved, rather than become a false failure or proof.
CONSERVATIVE_CVC5 = {"quantified_valid", "complete_loop"}

REQUIRED_FEATURES = {
    "mathematical-integers",
    "bit-vectors",
    "pointers",
    "heap-arrays",
    "quantifiers",
    "spec-functions",
}

REQUIRED_IR_TOKENS = {
    "ite : bitvector32",
    "/ : int",
    "% : int",
    "& : bitvector32",
    "| : bitvector32",
    "^ : bitvector32",
    "<< : bitvector32",
    ">> : bitvector32",
    "~ : bitvector32",
    "heap_select",
    "heap_store",
    "forall ",
    "exists ",
    "int_to_bv",
    "bv_to_int",
    "bv_resize",
    "no_overflow",
    "spec_call",
}


def fail(message):
    raise AssertionError(message)


def run(command, expected_codes, timeout=180):
    process = subprocess.run(
        [str(argument) for argument in command],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=timeout,
    )
    if process.returncode not in expected_codes:
        fail(
            "command returned {} instead of {}:\n{}\n{}".format(
                process.returncode,
                sorted(expected_codes),
                " ".join(str(argument) for argument in command),
                process.stdout[-8000:],
            )
        )
    return process.stdout


def parse_json_lines(output):
    records = []
    for line_number, line in enumerate(output.splitlines(), 1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            fail("non-JSON diagnostic on line {}: {} ({})".format(
                line_number, line, error
            ))
        if record.get("schema") != "cppverify.diagnostic/1":
            fail("unexpected diagnostic schema: {}".format(record))
        records.append(record)
    if not records:
        fail("backend emitted no structured diagnostics")
    return records


def function_records(records):
    selected = {}
    for record in records:
        name = record.get("function")
        if name not in EXPECTED_STATUS:
            continue
        if name in selected:
            fail("duplicate result for function {}".format(name))
        selected[name] = record
    missing = set(EXPECTED_STATUS) - set(selected)
    if missing:
        fail("missing function results: {}".format(", ".join(sorted(missing))))
    return selected


def check_matrix(records, backend):
    selected = function_records(records)
    for name, expected in EXPECTED_STATUS.items():
        record = selected[name]
        actual = record.get("status")
        if backend in {"cvc5", "portfolio"} and name in CONSERVATIVE_CVC5:
            if actual == "verified":
                continue
            if actual != "unresolved" or record.get("reason") != "solver.unknown":
                fail(
                    "{} returned {} ({}) for conservative case {}".format(
                        backend, actual, record.get("reason"), name
                    )
                )
            continue
        if actual != expected:
            fail(
                "{} returned {} instead of {} for {}".format(
                    backend, actual, expected, name
                )
            )
        if expected == "failed" and record.get("reason") != "counterexample":
            fail("{} lost counterexample classification for {}".format(
                backend, name
            ))
    if backend == "portfolio":
        for record in records:
            if record.get("reason") == "backend.inconsistent-results":
                fail("strict portfolio reported a backend disagreement")
    return selected


def diagnostic_identity(record):
    obligation = record.get("obligation")
    if not obligation:
        fail("failed result has no source obligation: {}".format(record))
    return (
        obligation.get("id"),
        obligation.get("kind"),
        json.dumps(obligation.get("source"), sort_keys=True),
        json.dumps(record.get("source"), sort_keys=True),
    )


def normalized_results(records):
    selected = function_records(records)
    result = []
    for name in sorted(selected):
        record = selected[name]
        obligation = record.get("obligation") or {}
        result.append(
            (
                name,
                record.get("status"),
                record.get("reason"),
                record.get("bound"),
                obligation.get("id"),
                obligation.get("kind"),
                json.dumps(obligation.get("source"), sort_keys=True),
            )
        )
    return result


def backend_command(cpp_verify, backend, source):
    command = [
        cpp_verify,
        "--backend={}".format(backend),
        "--diagnostics-format=json",
        "--jobs=4",
        "--timeout=10000",
        "--check-ub",
    ]
    if backend == "bmc":
        command.append("--unroll=2")
    command.append(source)
    return command


def replay_command(cpp_verify, backend, archive):
    command = [
        cpp_verify,
        "--backend={}".format(backend),
        "--diagnostics-format=json",
        "--jobs=4",
        "--timeout=10000",
        "--obligation-in={}".format(archive),
    ]
    return command


def check_source_matrix(cpp_verify, source):
    records = {}
    selected = {}
    for backend in ("z3", "cvc5", "portfolio", "bmc"):
        output = run(backend_command(cpp_verify, backend, source), {1})
        records[backend] = parse_json_lines(output)
        selected[backend] = check_matrix(records[backend], backend)

    for name in INVALID_FUNCTIONS:
        expected = diagnostic_identity(selected["z3"][name])
        for backend in ("cvc5", "portfolio", "bmc"):
            actual = diagnostic_identity(selected[backend][name])
            if actual != expected:
                fail(
                    "{} changed source obligation identity for {}".format(
                        backend, name
                    )
                )

    for name, record in selected["bmc"].items():
        expected_bound = 1 if name == "complete_loop" else 0
        if record.get("bound") != expected_bound:
            fail(
                "BMC reported bound {} instead of {} for {}".format(
                    record.get("bound"), expected_bound, name
                )
            )

    repeated = parse_json_lines(
        run(backend_command(cpp_verify, "portfolio", source), {1})
    )
    if normalized_results(repeated) != normalized_results(records["portfolio"]):
        fail("parallel portfolio results are not deterministic")
    return records


def check_lowering_matrix(cpp_verify, source):
    dump = run(
        [
            cpp_verify,
            "--backend=z3",
            "--lower-only",
            "--dump-ir=3",
            "--check-ub",
            source,
        ],
        {0},
    )
    observed_features = set()
    for match in re.finditer(r"^\s*features (.+)$", dump, re.MULTILINE):
        observed_features.update(
            feature.strip() for feature in match.group(1).split(",")
        )
    missing_features = REQUIRED_FEATURES - observed_features
    if missing_features:
        fail("Layer 3 omitted features: {}".format(
            ", ".join(sorted(missing_features))
        ))
    missing_tokens = {token for token in REQUIRED_IR_TOKENS if token not in dump}
    if missing_tokens:
        fail("Layer 3 omitted semantic nodes: {}".format(
            ", ".join(sorted(missing_tokens))
        ))

    for backend in ("cvc5", "portfolio", "bmc"):
        command = [
            cpp_verify,
            "--backend={}".format(backend),
            "--lower-only",
            "--check-ub",
        ]
        if backend == "bmc":
            command.append("--unroll=2")
        command.append(source)
        run(command, {0})


def create_archive(cpp_verify, backend, source, archive, extra=()):
    command = [
        cpp_verify,
        "--backend={}".format(backend),
        "--diagnostics-format=json",
        "--check-ub",
        "--obligation-out={}".format(archive),
    ]
    command.extend(extra)
    command.append(source)
    output = run(command, {1})
    if not archive.is_file() or archive.stat().st_size == 0:
        fail("{} did not produce an obligation archive".format(backend))
    return parse_json_lines(output)


def check_archive_matrix(cpp_verify, source, work, source_records):
    canonical = work / "canonical.cpv"
    create_archive(cpp_verify, "z3", source, canonical)
    for backend in ("z3", "cvc5", "portfolio"):
        replayed = parse_json_lines(
            run(replay_command(cpp_verify, backend, canonical), {1})
        )
        selected = check_matrix(replayed, backend)
        for name in INVALID_FUNCTIONS:
            if diagnostic_identity(selected[name]) != diagnostic_identity(
                function_records(source_records[backend])[name]
            ):
                fail(
                    "{} archive replay changed obligation identity for {}".format(
                        backend, name
                    )
                )

    bmc_archive = work / "bmc.cpv"
    create_archive(
        cpp_verify, "bmc", source, bmc_archive, extra=("--unroll=2",)
    )
    replayed_bmc = parse_json_lines(
        run(replay_command(cpp_verify, "bmc", bmc_archive), {1})
    )
    selected_bmc = check_matrix(replayed_bmc, "bmc")
    source_bmc = function_records(source_records["bmc"])
    for name in INVALID_FUNCTIONS:
        if diagnostic_identity(selected_bmc[name]) != diagnostic_identity(
            source_bmc[name]
        ):
            fail("BMC archive replay changed obligation identity for {}".format(
                name
            ))
    return canonical


def goal_names(lean_text):
    names = set(
        re.findall(
            r"^def ((?:cppverify_[A-Za-z0-9_]+_goal)|"
            r"(?:cppEncoded_[0-9a-f]+)) : Prop :=$",
            lean_text,
            re.MULTILINE,
        )
    )
    if not names:
        fail("Lean export contains no named obligation goals")
    return names


def scratch_theorem_names(lean_text):
    names = set(
        re.findall(
            r"^theorem ((?:cppverify_[A-Za-z0-9_]+_"
            r"(?:correct|obligation_[0-9]+))|(?:cppEncoded_[0-9a-f]+))",
            lean_text,
            re.MULTILINE,
        )
    )
    if not names:
        fail("Lean scratch export contains no named theorems")
    return names


def decode_lean_name(name):
    if not name.startswith("cppEncoded_"):
        return name
    return bytes.fromhex(name.removeprefix("cppEncoded_")).decode("utf-8")


def check_lean_identity(cpp_verify, source, canonical, work):
    source_lean = work / "source.lean"
    replay_lean = work / "replay.lean"
    project = work / "lean-project"

    run(
        [
            cpp_verify,
            "--backend=lean",
            "--check-ub",
            "--lean-out={}".format(source_lean),
            source,
        ],
        {0},
    )
    run(
        [
            cpp_verify,
            "--backend=lean",
            "--lean-out={}".format(replay_lean),
            "--obligation-in={}".format(canonical),
        ],
        {0},
    )
    if source_lean.read_bytes() != replay_lean.read_bytes():
        fail("source and archive replay produced different Lean semantics")
    scratch_goals = scratch_theorem_names(source_lean.read_text())

    run(
        [
            cpp_verify,
            "--backend=lean",
            "--check-ub",
            "--lean-project={}".format(project),
            source,
        ],
        {0},
    )
    generated = project / "CppVerify" / "Generated.lean"
    text = generated.read_text()
    if "sorry" in text:
        fail("generated Lean semantics contains an admitted proof")

    goals = goal_names(text)
    decoded_scratch_goals = {decode_lean_name(goal) for goal in scratch_goals}
    if {
        decode_lean_name(goal).removesuffix("_goal") for goal in goals
    } - decoded_scratch_goals:
        fail("Lean project goal identities differ from scratch/archive export")
    proof_files = list((project / "CppVerify" / "Proofs").glob("Goal_*.lean"))
    if len(proof_files) != len(goals):
        fail("Lean project proof-module count does not match generated goals")
    proof_goals = set()
    for proof_file in proof_files:
        match = re.search(
            r"^theorem ((?:cppverify_[A-Za-z0-9_]+_goal)|"
            r"(?:cppEncoded_[0-9a-f]+))_proof :",
            proof_file.read_text(),
            re.MULTILINE,
        )
        if not match:
            fail("malformed Lean proof module {}".format(proof_file.name))
        goal = match.group(1)
        expected_name = "Goal_{}.lean".format(
            hashlib.md5(goal.encode("utf-8")).hexdigest()[:16]
        )
        if proof_file.name != expected_name:
            fail(
                "Lean goal hash mismatch: {} should be {}".format(
                    proof_file.name, expected_name
                )
            )
        proof_goals.add(goal)
    if proof_goals != goals:
        fail("Lean proof modules do not cover the generated theorem identities")

    run(["lake", "--dir={}".format(project), "build", "CppVerify.Generated"], {0})


def warning_messages(records):
    return [
        record.get("message", "")
        for record in records
        if record.get("severity") == "warning"
    ]


def check_recommends_exclusion(cpp_verify, source, work):
    expected_warning = (
        "recommends of spec recommended_identity may be violated at call in "
        "recommendation_violated"
    )
    for backend in ("z3", "cvc5", "portfolio"):
        records = parse_json_lines(
            run(
                [
                    cpp_verify,
                    "--backend={}".format(backend),
                    "--diagnostics-format=json",
                    source,
                ],
                {1},
            )
        )
        if warning_messages(records) != [expected_warning]:
            fail("{} did not emit the precise source recommends warning".format(
                backend
            ))

    bmc_source = parse_json_lines(
        run(
            [
                cpp_verify,
                "--backend=bmc",
                "--unroll=1",
                "--diagnostics-format=json",
                source,
            ],
            {1},
        )
    )
    if warning_messages(bmc_source):
        fail("BMC source verification published advisory proof obligations")

    canonical = work / "recommends.cpv"
    create_archive(cpp_verify, "z3", source, canonical)
    for backend in ("z3", "cvc5", "portfolio"):
        records = parse_json_lines(
            run(replay_command(cpp_verify, backend, canonical), {1})
        )
        if warning_messages(records):
            fail("{} archive replay reconstructed recommends checks".format(
                backend
            ))

    bmc_archive = work / "recommends-bmc.cpv"
    create_archive(
        cpp_verify, "bmc", source, bmc_archive, extra=("--unroll=1",)
    )
    replayed_bmc = parse_json_lines(
        run(replay_command(cpp_verify, "bmc", bmc_archive), {1})
    )
    if warning_messages(replayed_bmc):
        fail("BMC archive replay reconstructed recommends checks")

    lean_replay = work / "recommends-replay.lean"
    run(
        [
            cpp_verify,
            "--backend=lean",
            "--lean-out={}".format(lean_replay),
            "--obligation-in={}".format(canonical),
        ],
        {0},
    )
    if re.search(
        r"^/- function: [^\n]*\.recommends", lean_replay.read_text(), re.MULTILINE
    ):
        fail("Lean archive replay included advisory recommends obligations")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cpp-verify", required=True, type=pathlib.Path)
    parser.add_argument("--source", required=True, type=pathlib.Path)
    parser.add_argument("--recommends", required=True, type=pathlib.Path)
    parser.add_argument("--work-dir", required=True, type=pathlib.Path)
    arguments = parser.parse_args()

    for path in (arguments.cpp_verify, arguments.source, arguments.recommends):
        if not path.exists():
            fail("required path does not exist: {}".format(path))
    arguments.work_dir.mkdir(parents=True, exist_ok=False)

    check_lowering_matrix(arguments.cpp_verify, arguments.source)
    print("PASS: canonical feature and operator matrix")

    source_records = check_source_matrix(arguments.cpp_verify, arguments.source)
    print("PASS: automated verdict and conservative-unknown matrix")
    print("PASS: source diagnostic identity and parallel determinism")

    canonical = check_archive_matrix(
        arguments.cpp_verify, arguments.source, arguments.work_dir, source_records
    )
    print("PASS: canonical and incremental-BMC archive replay")

    check_lean_identity(
        arguments.cpp_verify, arguments.source, canonical, arguments.work_dir
    )
    print("PASS: Lean theorem, hash, replay, and kernel-export identity")

    check_recommends_exclusion(
        arguments.cpp_verify, arguments.recommends, arguments.work_dir
    )
    print("PASS: recommends exclusion from BMC and Lean replay artifacts")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, subprocess.SubprocessError) as error:
        print("FAIL: {}".format(error), file=sys.stderr)
        sys.exit(1)
