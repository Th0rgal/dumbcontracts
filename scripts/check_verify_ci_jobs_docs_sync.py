#!/usr/bin/env python3
"""Ensure verify.yml job list matches scripts/README.md CI Integration summary."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SCRIPTS_README = ROOT / "scripts" / "README.md"


def _extract_workflow_jobs(text: str) -> list[str]:
    lines = text.splitlines()
    jobs_idx = next((i for i, line in enumerate(lines) if line == "jobs:"), None)
    if jobs_idx is None:
        raise ValueError(f"Could not locate jobs section in {VERIFY_YML}")

    jobs: list[str] = []
    for line in lines[jobs_idx + 1 :]:
        if not line:
            continue
        if not line.startswith(" "):
            break
        m = re.match(r"^  ([A-Za-z0-9_-]+):\s*$", line)
        if m:
            jobs.append(m.group(1))
    if not jobs:
        raise ValueError(f"No top-level jobs found in {VERIFY_YML}")
    return jobs


def _extract_readme_ci_jobs(text: str) -> list[str]:
    section = re.search(
        r"^## CI Integration\n(?P<body>.*?)(?:^## |\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    if not section:
        raise ValueError(f"Could not locate '## CI Integration' section in {SCRIPTS_README}")

    jobs: list[str] = []
    for line in section.group("body").splitlines():
        m = re.match(r"^\*\*`([^`]+)`(?: job)?\*\*", line)
        if m:
            jobs.append(m.group(1))
    if not jobs:
        raise ValueError(f"No CI job summary entries found in {SCRIPTS_README}")
    return jobs


def _compare(expected: list[str], actual: list[str]) -> list[str]:
    if expected == actual:
        return []

    errors: list[str] = []
    expected_set = set(expected)
    actual_set = set(actual)

    missing = [job for job in expected if job not in actual_set]
    extra = [job for job in actual if job not in expected_set]

    if missing:
        errors.append("README CI Integration is missing workflow jobs:")
        errors.extend([f"  - {job}" for job in missing])
    if extra:
        errors.append("README CI Integration has jobs not present in workflow:")
        errors.extend([f"  - {job}" for job in extra])
    if not missing and not extra:
        errors.append(
            "README CI Integration contains the same jobs but in a different order. "
            "Keep order aligned with workflow for quick cross-referencing."
        )
    return errors


def main() -> int:
    workflow_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    workflow_jobs = _extract_workflow_jobs(workflow_text)
    readme_jobs = _extract_readme_ci_jobs(readme_text)

    errors = _compare(workflow_jobs, readme_jobs)
    if errors:
        print("verify CI job/docs sync check failed:", file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        print(
            "\nUpdate scripts/README.md '## CI Integration' job summary to match "
            ".github/workflows/verify.yml job order.",
            file=sys.stderr,
        )
        return 1

    print(f"verify CI job/docs list is synchronized ({len(workflow_jobs)} jobs).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
