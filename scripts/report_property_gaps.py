#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "test" / "property_manifest.json"
EXCLUSIONS = ROOT / "test" / "property_exclusions.json"
TEST_DIR = ROOT / "test"

PROPERTY_WITH_NUM_RE = re.compile(
    r"Property\s+\d+[A-Za-z]*\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
PROPERTY_SIMPLE_RE = re.compile(
    r"Property\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
FILE_RE = re.compile(r"^Property(.+)\.t\.sol$")


def load_json(path: Path) -> dict[str, list[str]]:
    if not path.exists():
        raise SystemExit(f"Missing file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def extract_property_names(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    names: list[str] = []
    for line in text.splitlines():
        match = PROPERTY_WITH_NUM_RE.search(line)
        if match:
            names.append(match.group(1))
            continue
        match = PROPERTY_SIMPLE_RE.search(line)
        if match:
            names.append(match.group(1))
    return names


def collect_covered() -> dict[str, set[str]]:
    covered: dict[str, set[str]] = {}
    for path in sorted(TEST_DIR.glob("Property*.t.sol")):
        match = FILE_RE.match(path.name)
        if not match:
            continue
        contract = match.group(1)
        covered.setdefault(contract, set()).update(extract_property_names(path))
    return covered


def snake_to_camel(name: str) -> str:
    parts = [p for p in name.replace("'", "").split("_") if p]
    return "".join(part[:1].upper() + part[1:] for part in parts)


def main() -> None:
    parser = argparse.ArgumentParser(description="Report proof->test property gaps.")
    parser.add_argument("--stubs", action="store_true", help="Emit stub test templates.")
    args = parser.parse_args()

    manifest = {k: set(v) for k, v in load_json(MANIFEST).items()}
    exclusions = {}
    if EXCLUSIONS.exists():
        exclusions = {k: set(v) for k, v in load_json(EXCLUSIONS).items()}

    covered = collect_covered()

    missing_total = 0
    for contract, names in sorted(manifest.items()):
        covered_names = covered.get(contract, set())
        excluded_names = exclusions.get(contract, set())
        missing = sorted(names - covered_names - excluded_names)
        if not missing:
            continue
        missing_total += len(missing)
        print(f"\n{contract}: {len(missing)} missing")
        for name in missing:
            print(f"  - {name}")
        if args.stubs:
            print("\n  // Stub templates")
            for name in missing:
                func_name = f"testProperty_{snake_to_camel(name)}"
                print("  /// Property: " + name)
                print(f"  function {func_name}() public {{")
                print("      // TODO: implement via proof->test extraction")
                print("      revert(\"TODO\");")
                print("  }")

    if missing_total == 0:
        print("All properties covered (respecting exclusions).")


if __name__ == "__main__":
    main()
