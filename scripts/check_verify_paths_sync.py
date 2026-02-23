#!/usr/bin/env python3
"""Ensure verify.yml path filters stay consistent.

Guards against drift between:
- `on.push.paths`
- `on.pull_request.paths`
- `jobs.changes.steps[*].with.filters.code` (dorny/paths-filter)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"


def normalize_path(raw: str) -> str:
    value = raw.strip()
    if value.startswith("- "):
        value = value[2:].strip()
    if (value.startswith("'") and value.endswith("'")) or (
        value.startswith('"') and value.endswith('"')
    ):
        value = value[1:-1]
    return value


def extract_list_block(text: str, pattern: str, label: str) -> list[str]:
    match = re.search(pattern, text, re.MULTILINE)
    if not match:
        raise ValueError(f"Could not locate {label} in {VERIFY_YML}")
    block = match.group("block")
    entries = [normalize_path(line) for line in block.splitlines() if line.strip()]
    if not entries:
        raise ValueError(f"{label} is empty in {VERIFY_YML}")
    return entries


def duplicates(values: list[str]) -> list[str]:
    seen: set[str] = set()
    dups: list[str] = []
    for value in values:
        if value in seen and value not in dups:
            dups.append(value)
        seen.add(value)
    return dups


def compare_lists(reference_name: str, reference: list[str], other_name: str, other: list[str]) -> list[str]:
    errors: list[str] = []
    if reference == other:
        return errors

    ref_set = set(reference)
    other_set = set(other)
    missing = sorted(ref_set - other_set)
    extra = sorted(other_set - ref_set)

    if missing:
        errors.append(f"{other_name} is missing {len(missing)} path(s) present in {reference_name}:")
        errors.extend([f"  - {m}" for m in missing])
    if extra:
        errors.append(f"{other_name} has {len(extra)} extra path(s) not present in {reference_name}:")
        errors.extend([f"  - {e}" for e in extra])

    if not missing and not extra:
        errors.append(
            f"{other_name} has the same entries as {reference_name} but in a different order. "
            "Keep order aligned to reduce review noise."
        )
    return errors


def ensure_subset(parent_name: str, parent: list[str], subset_name: str, subset: list[str]) -> list[str]:
    errors: list[str] = []
    parent_set = set(parent)
    extra = sorted(set(subset) - parent_set)
    if extra:
        errors.append(f"{subset_name} contains {len(extra)} path(s) not present in {parent_name}:")
        errors.extend([f"  - {e}" for e in extra])
    return errors


def main() -> int:
    text = VERIFY_YML.read_text(encoding="utf-8")

    push_paths = extract_list_block(
        text,
        r"^  push:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.push.paths",
    )
    pr_paths = extract_list_block(
        text,
        r"^  pull_request:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.pull_request.paths",
    )
    filter_paths = extract_list_block(
        text,
        r"^          filters: \|\n(?:^            .*\n)*?^            code:\n(?P<block>(?:^              - .*\n)+)",
        "changes.filter.code",
    )

    errors: list[str] = []

    for label, values in [
        ("on.push.paths", push_paths),
        ("on.pull_request.paths", pr_paths),
        ("changes.filter.code", filter_paths),
    ]:
        dup = duplicates(values)
        if dup:
            errors.append(f"{label} contains duplicate path entries:")
            errors.extend([f"  - {d}" for d in dup])

    errors.extend(compare_lists("on.push.paths", push_paths, "on.pull_request.paths", pr_paths))
    errors.extend(ensure_subset("on.push.paths", push_paths, "changes.filter.code", filter_paths))

    if errors:
        print("verify.yml path-filter inconsistency detected:", file=sys.stderr)
        for line in errors:
            print(line, file=sys.stderr)
        print(
            "\nUpdate .github/workflows/verify.yml so push/pull_request lists match and "
            "changes.filter.code remains a valid subset.",
            file=sys.stderr,
        )
        return 1

    print(
        "verify.yml path filters are consistent "
        f"({len(push_paths)} push/pull_request entries; {len(filter_paths)} changes.filter.code entries)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
