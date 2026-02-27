#!/usr/bin/env python3
"""Ensure verify.yml job list matches scripts/README.md CI Integration summary."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from workflow_jobs import compare_lists, extract_top_level_jobs

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SCRIPTS_README = ROOT / "scripts" / "README.md"


def _extract_workflow_jobs(text: str) -> list[str]:
    return extract_top_level_jobs(text, VERIFY_YML)


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


def main() -> int:
    workflow_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    workflow_jobs = _extract_workflow_jobs(workflow_text)
    readme_jobs = _extract_readme_ci_jobs(readme_text)

    errors = compare_lists("workflow", workflow_jobs, "README CI Integration", readme_jobs)
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
