#!/usr/bin/env python3
"""Check that property_manifest.json is in sync with actual Lean proofs."""

from __future__ import annotations

from property_utils import extract_manifest_from_proofs, load_manifest, report_errors


def main() -> None:
    expected = extract_manifest_from_proofs()
    actual = {k: sorted(v) for k, v in load_manifest().items()}

    problems: list[str] = []
    for contract in sorted(set(expected.keys()) | set(actual.keys())):
        exp = expected.get(contract, [])
        act = actual.get(contract, [])
        if not exp and act:
            problems.append(f"{contract}: manifest has entries but proofs missing")
            continue
        if exp and not act:
            problems.append(f"{contract}: missing manifest entries (run extract_property_manifest.py)")
            continue
        missing = sorted(set(exp) - set(act))
        extra = sorted(set(act) - set(exp))
        if missing:
            problems.append(f"{contract}: missing {len(missing)} theorem(s) in manifest: {', '.join(missing)}")
        if extra:
            problems.append(f"{contract}: {len(extra)} extra theorem(s) in manifest: {', '.join(extra)}")

    report_errors(problems, "Property manifest out of sync (run extract_property_manifest.py)")
    print("Property manifest sync check passed.")


if __name__ == "__main__":
    main()
