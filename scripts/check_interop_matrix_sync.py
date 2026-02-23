#!/usr/bin/env python3
"""Check Solidity interop support matrix sync across ROADMAP and status docs.

Validates that the matrix rows and status columns in:
- docs/ROADMAP.md ("Solidity Interop Profile (Issue #586)")
- docs/VERIFICATION_STATUS.md ("Solidity Interop Support Matrix (Issue #586)")

stay synchronized for migration-critical status reporting.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT

ROADMAP = ROOT / "docs" / "ROADMAP.md"
VERIFICATION_STATUS = ROOT / "docs" / "VERIFICATION_STATUS.md"

STATUS_COLUMNS = [
    "Spec support",
    "Codegen support",
    "Proof status",
    "Test status",
    "Current status",
]


def _normalize_feature(name: str) -> str:
    """Normalize a feature label to compare semantically-equivalent row names."""
    normalized = name.strip().lower()
    normalized = normalized.replace("`", "")
    normalized = normalized.replace("(", " ").replace(")", " ")
    normalized = normalized.replace("/", " ")
    normalized = normalized.replace("+", " plus ")
    normalized = re.sub(r"[^a-z0-9\s-]", " ", normalized)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    replacements = {
        "full event abi parity indexed dynamic plus tuple hashing": "event abi parity indexed dynamic tuple payloads",
        "event abi parity for indexed dynamic tuple payloads": "event abi parity indexed dynamic tuple payloads",
        "low-level calls call staticcall delegatecall plus returndata handling": "low-level calls call staticcall delegatecall returndata",
        "low-level calls call staticcall delegatecall with returndata": "low-level calls call staticcall delegatecall returndata",
        "storage layout controls packed fields plus explicit slot mapping": "storage layout controls packed explicit slots",
        "storage layout controls packing plus explicit slots": "storage layout controls packed explicit slots",
    }
    return replacements.get(normalized, normalized)


def _extract_table_rows(doc: Path, heading_pattern: str) -> list[list[str]]:
    text = doc.read_text(encoding="utf-8")
    heading = re.search(heading_pattern, text, flags=re.MULTILINE)
    if not heading:
        raise ValueError(f"{doc}: missing heading matching /{heading_pattern}/")

    after = text[heading.end() :].splitlines()
    rows: list[list[str]] = []
    in_table = False
    for line in after:
        stripped = line.strip()
        if not in_table:
            if stripped.startswith("|"):
                in_table = True
            else:
                continue
        if not stripped.startswith("|"):
            break
        if re.match(r"^\|[-\s|:]+\|$", stripped):
            continue
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        rows.append(cells)

    if len(rows) < 2:
        raise ValueError(f"{doc}: failed to parse interop matrix rows")
    return rows


def _parse_roadmap_rows() -> dict[str, list[str]]:
    rows = _extract_table_rows(ROADMAP, r"^### Solidity Interop Profile \(Issue #586\)\s*$")
    header, body = rows[0], rows[1:]
    expected_header = ["Priority", "Feature", *STATUS_COLUMNS]
    if header != expected_header:
        raise ValueError(
            f"{ROADMAP}: unexpected matrix header {header!r}; expected {expected_header!r}"
        )
    parsed: dict[str, list[str]] = {}
    for row in body:
        if len(row) != len(expected_header):
            raise ValueError(f"{ROADMAP}: malformed matrix row: {row!r}")
        feature = _normalize_feature(row[1])
        parsed[feature] = row[2:]
    return parsed


def _parse_verification_rows() -> dict[str, list[str]]:
    rows = _extract_table_rows(
        VERIFICATION_STATUS, r"^## Solidity Interop Support Matrix \(Issue #586\)\s*$"
    )
    header, body = rows[0], rows[1:]
    expected_header = ["Feature", *STATUS_COLUMNS]
    if header != expected_header:
        raise ValueError(
            f"{VERIFICATION_STATUS}: unexpected matrix header {header!r}; expected {expected_header!r}"
        )
    parsed: dict[str, list[str]] = {}
    for row in body:
        if len(row) != len(expected_header):
            raise ValueError(f"{VERIFICATION_STATUS}: malformed matrix row: {row!r}")
        feature = _normalize_feature(row[0])
        parsed[feature] = row[1:]
    return parsed


def main() -> None:
    roadmap = _parse_roadmap_rows()
    verification = _parse_verification_rows()

    errors: list[str] = []

    roadmap_features = set(roadmap.keys())
    verification_features = set(verification.keys())

    only_roadmap = sorted(roadmap_features - verification_features)
    only_verification = sorted(verification_features - roadmap_features)

    if only_roadmap:
        errors.append(
            "ROADMAP has interop rows missing in VERIFICATION_STATUS: "
            + ", ".join(repr(f) for f in only_roadmap)
        )
    if only_verification:
        errors.append(
            "VERIFICATION_STATUS has interop rows missing in ROADMAP: "
            + ", ".join(repr(f) for f in only_verification)
        )

    shared = sorted(roadmap_features & verification_features)
    for feature in shared:
        lhs = roadmap[feature]
        rhs = verification[feature]
        if lhs != rhs:
            deltas = []
            for idx, col in enumerate(STATUS_COLUMNS):
                if lhs[idx] != rhs[idx]:
                    deltas.append(f"{col}: roadmap={lhs[idx]!r}, verification_status={rhs[idx]!r}")
            errors.append(f"Interop matrix drift for {feature!r}: " + "; ".join(deltas))

    if errors:
        print("Interop matrix sync check failed:", file=sys.stderr)
        for e in errors:
            print(f"- {e}", file=sys.stderr)
        print(
            "\nKeep docs/ROADMAP.md and docs/VERIFICATION_STATUS.md interop matrices synchronized.",
            file=sys.stderr,
        )
        raise SystemExit(1)

    print(
        f"Interop matrix is synchronized across docs ({len(shared)} feature rows checked)."
    )


if __name__ == "__main__":
    main()
