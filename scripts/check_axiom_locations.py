#!/usr/bin/env python3
"""Check that AXIOMS.md stays in sync with Lean axiom declarations.

Parses AXIOMS.md for location patterns like `File.lean:NN` and verifies each
axiom actually appears at the claimed line number in the source file.
Also verifies:
- every Lean kernel axiom is listed in AXIOMS.md
- AXIOMS.md has no stale/extra axiom entries
- AXIOMS.md trust summary active axiom count matches source

Usage:
    python3 scripts/check_axiom_locations.py
"""

from __future__ import annotations

import re
from pathlib import Path

from property_utils import ROOT, die, report_errors, scrub_lean_code

AXIOM_DECL_RE = re.compile(r"^(?:private |protected )?axiom\s+([A-Za-z_][A-Za-z0-9_']*)\b")


def parse_axiom_entries(axioms_md_text: str) -> list[tuple[str, str, int]]:
    """Extract (axiom_name, relative_path, claimed_line) entries from AXIOMS.md."""
    blocks = re.findall(
        r"### \d+\.\s+`([^`]+)`(?:[^\n]*)\n\n"
        r"\*\*Location\*\*:\s*`([^:]+):(\d+)`",
        axioms_md_text,
    )
    return [(name, rel_path, int(line)) for name, rel_path, line in blocks]


def parse_active_axiom_count(axioms_md_text: str) -> int | None:
    """Extract trust-summary active axiom count from AXIOMS.md, if present."""
    match = re.search(r"^- Active axioms:\s*(\d+)\s*$", axioms_md_text, flags=re.MULTILINE)
    if match is None:
        return None
    return int(match.group(1))


def discover_repo_axioms() -> dict[str, tuple[str, int]]:
    """Return all Lean axiom declarations as {name: (relative_path, line)}."""
    discovered: dict[str, tuple[str, int]] = {}
    for subdir in ("Compiler", "Verity"):
        base_dir = ROOT / subdir
        if not base_dir.exists():
            continue
        for lean_file in sorted(base_dir.rglob("*.lean")):
            text = scrub_lean_code(lean_file.read_text(encoding="utf-8"))
            rel_path = str(lean_file.relative_to(ROOT))
            for i, line in enumerate(text.splitlines(), 1):
                match = AXIOM_DECL_RE.match(line)
                if match is None:
                    continue
                name = match.group(1)
                if name in discovered:
                    old_path, old_line = discovered[name]
                    die(
                        f"Duplicate axiom name {name!r}: "
                        f"{old_path}:{old_line} and {rel_path}:{i}"
                    )
                discovered[name] = (rel_path, i)
    return discovered


def main() -> None:
    axioms_md = ROOT / "AXIOMS.md"
    if not axioms_md.exists():
        die("AXIOMS.md not found")

    text = axioms_md.read_text(encoding="utf-8")

    axiom_blocks = parse_axiom_entries(text)

    if not axiom_blocks:
        die("No axiom location entries found in AXIOMS.md")

    discovered_axioms = discover_repo_axioms()
    documented_names = {name for name, _, _ in axiom_blocks}
    discovered_names = set(discovered_axioms)

    errors: list[str] = []
    checked = 0

    for axiom_name, rel_path, claimed_line in axiom_blocks:
        source_file = ROOT / rel_path

        if not source_file.exists():
            errors.append(f"{axiom_name}: file {rel_path} not found")
            continue

        lines = source_file.read_text(encoding="utf-8").splitlines()

        # Find actual line number for this axiom
        actual_line = None
        for i, line in enumerate(lines, 1):
            if re.match(rf"^(private |protected )?axiom\s+{re.escape(axiom_name)}\b", line):
                actual_line = i
                break

        if actual_line is None:
            errors.append(
                f"{axiom_name}: not found in {rel_path} "
                f"(AXIOMS.md claims line {claimed_line})"
            )
        elif actual_line != claimed_line:
            errors.append(
                f"{axiom_name}: AXIOMS.md says line {claimed_line} "
                f"but actually at line {actual_line} in {rel_path}"
            )
        else:
            print(f"  OK {axiom_name} at {rel_path}:{actual_line}")
            checked += 1

    missing_from_docs = sorted(discovered_names - documented_names)
    for axiom_name in missing_from_docs:
        rel_path, line = discovered_axioms[axiom_name]
        errors.append(
            f"{axiom_name}: declared in {rel_path}:{line} but missing from AXIOMS.md"
        )

    stale_doc_entries = sorted(documented_names - discovered_names)
    for axiom_name in stale_doc_entries:
        errors.append(f"{axiom_name}: listed in AXIOMS.md but no Lean axiom declaration exists")

    active_count = parse_active_axiom_count(text)
    if active_count is None:
        errors.append("AXIOMS.md: missing '- Active axioms: N' trust summary line")
    elif active_count != len(discovered_axioms):
        errors.append(
            f"AXIOMS.md trust summary says Active axioms: {active_count}, "
            f"but source has {len(discovered_axioms)}"
        )

    report_errors(errors, "Axiom location check failed")
    print(
        f"\nOK: {checked} documented axiom locations are accurate; "
        f"registry is complete and synchronized with {len(discovered_axioms)} source axioms"
    )


if __name__ == "__main__":
    main()
