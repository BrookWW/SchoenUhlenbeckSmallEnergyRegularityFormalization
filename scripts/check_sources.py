#!/usr/bin/env python3
"""Validate the public source footprint, module layout and declared dependencies."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

from verification_common import PROJECT


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_header(source):
    """Find the first command, retaining Lean doc comments as commands."""
    index = 0
    while index < len(source):
        if source[index].isspace() or source[index] == "\ufeff":
            index += 1
        elif source.startswith("--", index):
            end = source.find("\n", index)
            index = len(source) if end < 0 else end + 1
        elif source.startswith("/-", index) and not source.startswith(("/--", "/-!"), index):
            index += 2
            depth = 1
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
                return False
        else:
            return re.match(r"module(?![\w'.!?])", source[index:]) is not None
    return False


def main():
    manifest = json.loads((PROJECT / "verification/sources.json").read_text())
    if manifest.get("schema_version") != 1:
        raise ValueError("Unsupported source manifest schema")
    for entry in manifest["manuscripts"] + manifest["semantic_definition_sources"]:
        path = PROJECT / entry["path"]
        if path.is_symlink() or not path.is_file() or digest(path) != entry["sha256"]:
            raise ValueError("Mathematical source fingerprint changed: " + entry["path"])
    actual_upgrade = {"HolderToCK.lean"} | {
        p.relative_to(PROJECT).as_posix() for p in (PROJECT / "HolderToCK").rglob("*.lean")}
    if actual_upgrade != set(manifest["upgrade_source_files"]):
        raise ValueError("Upgrade mathematical source inventory changed")
    for name, expected in manifest["upgrade_source_files"].items():
        path = PROJECT / name
        if path.is_symlink() or digest(path) != expected:
            raise ValueError("Upgrade mathematical source changed: " + name)
    paths = [PROJECT / "HarmonicMaps.lean", PROJECT / "HolderToCK.lean"]
    paths += [p for root in ("HarmonicMaps", "HolderToCK")
              for p in sorted((PROJECT / root).rglob("*.lean"))]
    for path in paths:
        source = path.read_text()
        if path.is_symlink() or not module_header(source):
            raise ValueError("Invalid module header or source symlink: " + str(path.relative_to(PROJECT)))
        if len(source.splitlines()) > 10_000:
            raise ValueError("Oversized Lean module: " + str(path.relative_to(PROJECT)))
        if re.search(r"(?:/Users/|/home/|/private/|/tmp/|(?:blueprint|review|registry)/)", source):
            raise ValueError("Non-public path in mathematics: " + str(path.relative_to(PROJECT)))
    for entry in manifest["build_configuration"]:
        path = PROJECT / entry["path"]
        if path.is_symlink() or not path.is_file() or digest(path) != entry["sha256"]:
            raise ValueError("Build configuration changed: " + entry["path"])
    if (PROJECT / ".lake/package-overrides.json").exists():
        raise ValueError("Undeclared package override")
    lake = json.loads((PROJECT / "lake-manifest.json").read_text())
    for dependency in lake["packages"]:
        if dependency["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", dependency["rev"]):
            raise ValueError("Unpinned dependency: " + dependency["name"])
        package = PROJECT / lake["packagesDir"] / dependency["name"]
        actual = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(package), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
        if actual != dependency["rev"] or dirty:
            raise ValueError("Dependency source drift: " + dependency["name"])
    if "harmonicMaps" in {d["name"] for d in lake["packages"]}:
        raise ValueError("Repository depends on itself")
    print(f"SOURCE FOOTPRINT PASS: {len(paths)} modules, {len(actual_upgrade)} upgrade modules")
    print("MANUSCRIPT AND SEMANTIC-DEFINITION FINGERPRINTS PASS")
    print("PINNED DEPENDENCY AND MODULE CHECK PASS")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
