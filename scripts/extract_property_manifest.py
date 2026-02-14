#!/usr/bin/env python3
"""Extract theorem names from Lean proof files to generate property manifest."""

import json
from pathlib import Path

from property_utils import PROOFS_DIR, collect_theorems

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "test" / "property_manifest.json"


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
