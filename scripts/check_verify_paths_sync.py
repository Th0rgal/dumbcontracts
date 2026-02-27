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

from workflow_jobs import compare_lists, extract_job_body

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
CHECK_ONLY_PATHS = [
    "docs/**",
    "docs-site/**",
    "AXIOMS.md",
    "README.md",
    "TRUST_ASSUMPTIONS.md",
]


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


def extract_changes_filter_paths(text: str) -> list[str]:
    changes_body = extract_job_body(text, "changes", VERIFY_YML)
    return extract_list_block(
        changes_body,
        r"^\s*filters:\s*\|\n(?:^\s+.*\n)*?^\s*code:\n(?P<block>(?:^\s*-\s+.*\n)+)",
        "changes.filter.code",
    )


def duplicates(values: list[str]) -> list[str]:
    seen: set[str] = set()
    dups: list[str] = []
    for value in values:
        if value in seen and value not in dups:
            dups.append(value)
        seen.add(value)
    return dups


def ensure_subset(parent_name: str, parent: list[str], subset_name: str, subset: list[str]) -> list[str]:
    errors: list[str] = []
    parent_set = set(parent)
    extra = sorted(set(subset) - parent_set)
    if extra:
        errors.append(f"{subset_name} contains {len(extra)} path(s) not present in {parent_name}:")
        errors.extend([f"  - {e}" for e in extra])
    return errors


def expected_code_filter_paths(trigger_paths: list[str]) -> list[str]:
    excluded = set(CHECK_ONLY_PATHS)
    return [path for path in trigger_paths if path not in excluded]


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
    filter_paths = extract_changes_filter_paths(text)

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

    missing_exclusions = [path for path in CHECK_ONLY_PATHS if path not in push_paths]
    if missing_exclusions:
        errors.append("CHECK_ONLY_PATHS contains entries not present in on.push.paths:")
        errors.extend([f"  - {m}" for m in missing_exclusions])

    expected_filter_paths = expected_code_filter_paths(push_paths)
    errors.extend(
        compare_lists(
            "on.push.paths minus CHECK_ONLY_PATHS",
            expected_filter_paths,
            "changes.filter.code",
            filter_paths,
        )
    )

    if errors:
        print("verify.yml path-filter inconsistency detected:", file=sys.stderr)
        for line in errors:
            print(line, file=sys.stderr)
        print(
            "\nUpdate .github/workflows/verify.yml so push/pull_request lists match, "
            "then keep changes.filter.code equal to on.push.paths minus CHECK_ONLY_PATHS.",
            file=sys.stderr,
        )
        return 1

    print(
        "verify.yml path filters are consistent "
        f"({len(push_paths)} push/pull_request entries; {len(filter_paths)} changes.filter.code entries; "
        f"{len(CHECK_ONLY_PATHS)} check-only exclusions)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
