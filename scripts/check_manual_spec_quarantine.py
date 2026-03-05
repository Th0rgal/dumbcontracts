#!/usr/bin/env python3
"""Fail closed if canonical compiler paths reference quarantined manual artifacts.

Issue #999 keeps legacy/manual artifacts available for compatibility and proof
migration, but canonical compile/lowering/gas/CLI paths must not depend on
manual `*Spec` artifacts or legacy hand-written `Contracts.<Name>.Contract` contracts
(except explicit compatibility allowlist entries).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, scrub_lean_code

CANONICAL_FILES = [
    ROOT / "Compiler" / "CompileDriver.lean",
    ROOT / "Compiler" / "Gas" / "Report.lean",
    ROOT / "Compiler" / "Lowering" / "FromEDSL.lean",
    ROOT / "Compiler" / "Main.lean",
    ROOT / "Compiler" / "MainTest.lean",
]

ALLOWED_QUALIFIED_SPEC_REFERENCES = {
    "Compiler.Specs.cryptoHashSpec",
    "Specs.cryptoHashSpec",
}

QUALIFIED_SPEC_RE = re.compile(
    r"\b(?P<qual>(?:Compiler\.)?Specs\.(?P<name>[A-Za-z_][A-Za-z0-9_']*Spec))\b"
)

LEGACY_EXAMPLE_MODULES = {
    "Counter",
    "SimpleStorage",
    "SafeCounter",
    "Owned",
    "OwnedCounter",
    "Ledger",
    "SimpleToken",
}

LEGACY_IMPORT_RE = re.compile(
    r"\bimport\s+Contracts\.(?P<name>[A-Za-z_][A-Za-z0-9_]*)\.Contract\b"
)
LEGACY_QUALIFIED_RE = re.compile(
    r"\bContracts\.(?P<name>[A-Za-z_][A-Za-z0-9_]*)\."
)


def find_disallowed_references(content: str) -> list[str]:
    disallowed: list[str] = []
    for match in QUALIFIED_SPEC_RE.finditer(content):
        qualified = match.group("qual")
        if qualified in ALLOWED_QUALIFIED_SPEC_REFERENCES:
            continue
        disallowed.append(qualified)
    for match in LEGACY_IMPORT_RE.finditer(content):
        name = match.group("name")
        if name in LEGACY_EXAMPLE_MODULES:
            disallowed.append(f"import Contracts.{name}.Contract")
    for match in LEGACY_QUALIFIED_RE.finditer(content):
        name = match.group("name")
        if name in LEGACY_EXAMPLE_MODULES:
            disallowed.append(f"Contracts.{name}.*")
    return disallowed


def main() -> int:
    errors: list[str] = []
    for path in CANONICAL_FILES:
        if not path.exists():
            errors.append(f"Missing canonical file: {path.relative_to(ROOT)}")
            continue
        scrubbed = scrub_lean_code(path.read_text(encoding="utf-8"))
        bad = sorted(set(find_disallowed_references(scrubbed)))
        if bad:
            rel = path.relative_to(ROOT)
            errors.append(
                f"{rel}: found quarantined manual spec reference(s): {', '.join(bad)}"
            )

    if errors:
        print("Manual-spec quarantine check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        print(
            "\nCanonical compiler paths must not reference manual Compiler.Specs.*Spec symbols "
            "or legacy Contracts.<Name>.Contract modules. Route canonical flows through generated "
            "EDSL contracts and Specs.allSpecs.",
            file=sys.stderr,
        )
        return 1

    print(
        "Manual-artifact quarantine check passed "
        f"({len(CANONICAL_FILES)} canonical files; only allowlisted compatibility specs used)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
