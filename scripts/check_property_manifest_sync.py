#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
PROOFS_DIR = ROOT / "DumbContracts" / "Proofs"
MANIFEST_PATH = ROOT / "test" / "property_manifest.json"

THEOREM_RE = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z0-9_']+)")


def collect_theorems(path: Path) -> list[str]:
    names: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return names
    for line in text.splitlines():
        match = THEOREM_RE.match(line)
        if match:
            names.append(match.group(2))
    return names


def extract_manifest() -> dict[str, list[str]]:
    if not PROOFS_DIR.exists():
        raise SystemExit(f"Missing proofs dir: {PROOFS_DIR}")
    manifest: dict[str, list[str]] = {}
    for contract_dir in sorted(PROOFS_DIR.iterdir()):
        if not contract_dir.is_dir():
            continue
        contract = contract_dir.name
        theorems: list[str] = []
        for lean in sorted(contract_dir.rglob("*.lean")):
            theorems.extend(collect_theorems(lean))
        if theorems:
            manifest[contract] = sorted(dict.fromkeys(theorems))
    return manifest


def load_manifest() -> dict[str, list[str]]:
    if not MANIFEST_PATH.exists():
        raise SystemExit(f"Missing property manifest: {MANIFEST_PATH}")
    data = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    return {k: list(v) for k, v in data.items()}


def main() -> None:
    expected = extract_manifest()
    actual = load_manifest()

    problems: list[str] = []
    all_contracts = sorted(set(expected.keys()) | set(actual.keys()))
    for contract in all_contracts:
        exp = expected.get(contract, [])
        act = actual.get(contract, [])
        if not exp and act:
            problems.append(f"{contract}: manifest has entries but proofs missing")
            continue
        if exp and not act:
            problems.append(f"{contract}: missing manifest entries (run extract_property_manifest.py)")
            continue
        exp_set = set(exp)
        act_set = set(act)
        missing = sorted(exp_set - act_set)
        extra = sorted(act_set - exp_set)
        if missing:
            problems.append(f"{contract}: missing {len(missing)} theorem(s) in manifest")
        if extra:
            problems.append(f"{contract}: {len(extra)} extra theorem(s) in manifest")

    if problems:
        print("Property manifest is out of sync with proofs:", file=sys.stderr)
        for problem in problems:
            print(f"  - {problem}", file=sys.stderr)
        print("", file=sys.stderr)
        print("Run: python3 scripts/extract_property_manifest.py", file=sys.stderr)
        raise SystemExit(1)

    print("Property manifest sync check passed.")


if __name__ == "__main__":
    main()
