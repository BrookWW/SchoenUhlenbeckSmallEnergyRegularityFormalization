"""Shared utilities for inspecting the compiled Lean declarations."""

from pathlib import Path
import json
import re
import subprocess


PROJECT = Path(__file__).resolve().parent.parent
MANIFEST = PROJECT / "verification" / "theorem-types.json"
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def load_theorems():
    """Read the complete, nonempty list of stored kernel-type fingerprints."""
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1:
        raise ValueError("Unsupported theorem manifest schema.")
    if data.get("encoding") != "lean-kernel-expression-json-v1":
        raise ValueError("Unsupported kernel-type encoding.")
    records = data.get("theorems")
    if not isinstance(records, list) or not records:
        raise ValueError("The theorem manifest must contain a nonempty list.")
    names = set()
    for record in records:
        if not isinstance(record, dict) or set(record) != {"module", "theorem", "type_sha256"}:
            raise ValueError("Malformed theorem manifest record.")
        for key in ("module", "theorem"):
            if not isinstance(record[key], str) or not NAME.fullmatch(record[key]):
                raise ValueError(f"Invalid Lean {key}: {record[key]!r}")
            if not record[key].startswith(("HarmonicMaps.", "HolderToCK.")):
                raise ValueError(f"Unexpected Lean {key}: {record[key]}")
        fingerprint = record["type_sha256"]
        if not isinstance(fingerprint, str) or not re.fullmatch(r"[0-9a-f]{64}", fingerprint):
            raise ValueError("Malformed kernel-type fingerprint.")
        if record["theorem"] in names:
            raise ValueError(f"Duplicate theorem: {record['theorem']}")
        names.add(record["theorem"])
        source = PROJECT / (record["module"].replace(".", "/") + ".lean")
        if not source.is_file():
            raise ValueError(f"Missing source module: {record['module']}")
        declarations = strip_comments_and_strings(source.read_text(encoding="utf-8"))
        short_name = record["theorem"].partition(".")[2]
        if not re.search(r"\btheorem\s+" + re.escape(short_name) + r"\b", declarations):
            raise ValueError(f"Missing theorem declaration: {record['theorem']}")
    return records


def lean_output(code):
    """Inspect existing build products; never rebuild a dependency implicitly."""
    completed = subprocess.run(
        ["lake", "--no-build", "env", "lean", "--stdin"],
        input=code, text=True, capture_output=True, cwd=PROJECT, check=False,
    )
    if completed.returncode:
        details = (completed.stdout + completed.stderr).strip()
        raise RuntimeError(f"Lean inspection failed (exit {completed.returncode}):\n{details}")
    return completed.stdout


def parse_records(output, prefix, expected):
    """Reject missing, duplicate, malformed, or unexpected inspection records."""
    records = {}
    for line in output.splitlines():
        if not line.startswith(prefix + " "):
            continue
        pieces = line.split(" ", 2)
        if len(pieces) != 3:
            raise ValueError(f"Malformed {prefix} record.")
        _, name, payload = pieces
        if name not in expected or name in records:
            raise ValueError(f"Unexpected or duplicate {prefix} record: {name}")
        json.loads(payload)
        records[name] = payload
    if set(records) != set(expected):
        missing = ", ".join(sorted(set(expected) - set(records)))
        raise ValueError(f"Missing {prefix} records: {missing}")
    return records


def strip_comments_and_strings(source):
    """Mask nested Lean comments and strings while retaining line positions."""
    output = list(source)
    index = 0
    while index < len(source):
        start = index
        if source.startswith("--", index):
            end = source.find("\n", index)
            index = len(source) if end < 0 else end
        elif source.startswith("/-", index):
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError("Unterminated Lean block comment.")
        elif source[index] == '"':
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise ValueError("Unterminated Lean string.")
        else:
            index += 1
            continue
        for position in range(start, min(index, len(source))):
            if output[position] != "\n":
                output[position] = " "
    return "".join(output)


def check_frozen_coverage(records):
    """Require a manifest entry for every theorem in the public Frozen modules."""
    actual = set()
    files = sorted(path for namespace in ("HarmonicMaps", "HolderToCK")
                   for path in (PROJECT / namespace / "Frozen").glob("*.lean"))
    if not files:
        raise ValueError("No public theorem modules found.")
    for path in files:
        source = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        module = path.relative_to(PROJECT).with_suffix("").as_posix().replace("/", ".")
        namespace = path.relative_to(PROJECT).parts[0]
        for name in re.findall(r"\btheorem\s+([A-Za-z_][A-Za-z0-9_']*)\b", source):
            actual.add((module, namespace + "." + name))
    expected = {
        (record["module"], record["theorem"])
        for record in records if ".Frozen." in record["module"]
    }
    if actual != expected:
        raise ValueError("Frozen theorem declarations and the manifest do not agree.")
