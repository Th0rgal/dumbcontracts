#!/usr/bin/env python3
"""Parse and validate the output of `lake env lean PrintAxioms.lean`.

For each `#print axioms X` statement, Lean outputs one of:
  - "'X' depends on axioms: [axiom1, axiom2, ...]"
  - "'X' does not depend on any axioms"

This script:
  1. Parses the output into a per-theorem axiom dependency map.
  2. Validates that the only non-Lean-builtin axiom is `keccak256_first_4_bytes`.
  3. Produces a human-readable summary report.
  4. Exits non-zero if unexpected axioms are found.

Usage:
    lake env lean PrintAxioms.lean 2>&1 | python3 scripts/check_axiom_report.py
    python3 scripts/check_axiom_report.py --log axiom-output.log
"""

import re
import sys
from pathlib import Path

# Lean kernel axioms that are always present and expected.
# sorryAx is intentionally excluded: it indicates an incomplete proof and must
# surface as forbidden/unexpected rather than being silently classified as builtin.
LEAN_BUILTIN_AXIOMS = frozenset([
    "propext",
    "Quot.sound",
    "Classical.choice",
])

# Axioms documented in AXIOMS.md as acceptable
DOCUMENTED_AXIOMS = frozenset([
    "keccak256_first_4_bytes",
])

FORBIDDEN_AXIOMS = frozenset([
    "sorryAx",  # Indicates a sorry-based proof
])


def parse_axiom_output(text: str) -> dict[str, list[str]]:
    """Parse Lean #print axioms output into {theorem_name: [axioms]}."""
    results: dict[str, list[str]] = {}

    for line in text.splitlines():
        line = line.strip()

        # Match: 'Foo.bar' depends on axioms: [ax1, ax2]
        m = re.match(r"'(.+)' depends on axioms: \[(.+)\]", line)
        if m:
            name = m.group(1)
            axioms = [a.strip() for a in m.group(2).split(",")]
            results[name] = axioms
            continue

        # Match: 'Foo.bar' does not depend on any axioms
        m = re.match(r"'(.+)' does not depend on any axioms", line)
        if m:
            results[m.group(1)] = []
            continue

    return results


def classify_axioms(
    axiom_map: dict[str, list[str]],
) -> tuple[set[str], set[str], set[str], dict[str, list[str]]]:
    """Classify axioms into builtin, documented, forbidden, and unexpected."""
    all_axioms: set[str] = set()
    for axioms in axiom_map.values():
        all_axioms.update(axioms)

    builtin = all_axioms & LEAN_BUILTIN_AXIOMS
    documented = all_axioms & DOCUMENTED_AXIOMS
    forbidden = all_axioms & FORBIDDEN_AXIOMS
    unexpected = all_axioms - LEAN_BUILTIN_AXIOMS - DOCUMENTED_AXIOMS

    # Map unexpected axioms to the theorems that use them
    unexpected_usage: dict[str, list[str]] = {}
    for ax in unexpected:
        users = [thm for thm, axioms in axiom_map.items() if ax in axioms]
        unexpected_usage[ax] = users

    return builtin, documented, forbidden, unexpected_usage


def generate_report(
    axiom_map: dict[str, list[str]],
    builtin: set[str],
    documented: set[str],
    forbidden: set[str],
    unexpected_usage: dict[str, list[str]],
) -> str:
    """Generate a human-readable axiom report."""
    lines = ["# Axiom Dependency Report", ""]

    total = len(axiom_map)
    axiom_free = sum(1 for v in axiom_map.values() if not v)
    builtin_only = sum(
        1
        for v in axiom_map.values()
        if v and all(a in LEAN_BUILTIN_AXIOMS for a in v)
    )
    uses_documented = sum(
        1
        for v in axiom_map.values()
        if any(a in DOCUMENTED_AXIOMS for a in v)
    )

    lines.append(f"Total theorems checked: {total}")
    lines.append(f"Axiom-free (pure logic): {axiom_free}")
    lines.append(f"Uses only Lean builtins (propext, Quot.sound, Classical.choice): {builtin_only}")
    lines.append(f"Uses documented project axioms: {uses_documented}")
    lines.append("")

    lines.append("## Lean Builtin Axioms Used")
    for ax in sorted(builtin - FORBIDDEN_AXIOMS):
        lines.append(f"  - {ax}")
    lines.append("")

    lines.append("## Documented Project Axioms")
    for ax in sorted(documented):
        users = [thm for thm, axioms in axiom_map.items() if ax in axioms]
        lines.append(f"  - {ax} (used by {len(users)} theorems)")
    lines.append("")

    if forbidden:
        lines.append("## FORBIDDEN AXIOMS DETECTED")
        for ax in sorted(forbidden):
            users = [thm for thm, axioms in axiom_map.items() if ax in axioms]
            lines.append(f"  - {ax} (used by {len(users)} theorems)")
            for u in users[:10]:
                lines.append(f"      {u}")
        lines.append("")

    if unexpected_usage:
        lines.append("## UNEXPECTED AXIOMS DETECTED")
        for ax, users in sorted(unexpected_usage.items()):
            lines.append(f"  - {ax} (used by {len(users)} theorems)")
            for u in users[:10]:
                lines.append(f"      {u}")
        lines.append("")

    if not forbidden and not unexpected_usage:
        lines.append("## Result: PASS")
        lines.append("All theorems depend only on Lean builtins and documented project axioms.")
    else:
        lines.append("## Result: FAIL")
        lines.append("Unexpected or forbidden axioms detected.")

    return "\n".join(lines) + "\n"


def main() -> None:
    # Read from file or stdin
    if "--log" in sys.argv:
        idx = sys.argv.index("--log")
        if idx + 1 >= len(sys.argv):
            print("ERROR: --log requires a file path argument", file=sys.stderr)
            sys.exit(1)
        log_path = Path(sys.argv[idx + 1])
        text = log_path.read_text()
    else:
        text = sys.stdin.read()

    axiom_map = parse_axiom_output(text)

    if not axiom_map:
        print("WARNING: No #print axioms output found. Is the input empty?", file=sys.stderr)
        print("Parsed 0 theorems from input.", file=sys.stderr)
        sys.exit(1)

    builtin, documented, forbidden, unexpected_usage = classify_axioms(axiom_map)
    report = generate_report(axiom_map, builtin, documented, forbidden, unexpected_usage)

    print(report)

    # Write report to file if OUTPUT_FILE env var is set
    import os
    output_file = os.environ.get("AXIOM_REPORT_FILE")
    if output_file:
        Path(output_file).write_text(report)
        print(f"Report written to {output_file}", file=sys.stderr)

    if forbidden or unexpected_usage:
        sys.exit(1)


if __name__ == "__main__":
    main()
