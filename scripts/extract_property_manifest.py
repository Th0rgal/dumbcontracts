#!/usr/bin/env python3
import json
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOFS_DIR = ROOT / "DumbContracts" / "Proofs"
OUTPUT = ROOT / "test" / "property_manifest.json"

THEOREM_RE = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z0-9_']+)")


def collect_theorems(path: Path) -> list[str]:
    names = []
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return names
    for line in text.splitlines():
        m = THEOREM_RE.match(line)
        if m:
            names.append(m.group(2))
    return names


def main() -> None:
    manifest = {}
    if not PROOFS_DIR.exists():
        raise SystemExit(f"Missing proofs dir: {PROOFS_DIR}")
    for contract_dir in sorted(PROOFS_DIR.iterdir()):
        if not contract_dir.is_dir():
            continue
        contract = contract_dir.name
        theorems = []
        for lean in sorted(contract_dir.rglob("*.lean")):
            theorems.extend(collect_theorems(lean))
        if theorems:
            # stable ordering + unique
            manifest[contract] = sorted(dict.fromkeys(theorems))
    OUTPUT.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
