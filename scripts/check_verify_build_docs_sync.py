#!/usr/bin/env python3
"""Ensure verify.yml build/build-compiler job script lists match scripts/README.md docs."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from workflow_jobs import (
    compare_lists,
    extract_job_body,
    extract_python_script_commands,
    extract_run_commands_from_job_body,
)

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SCRIPTS_README = ROOT / "scripts" / "README.md"

# Each entry: (workflow job name, README heading pattern, label for messages)
_JOBS = [
    ("build", r"^\*\*`build` job\*\*", "build"),
    ("build-compiler", r"^\*\*`build-compiler` job\*\*", "build-compiler"),
]


def _normalize_spaces(text: str) -> str:
    return " ".join(text.split())


def _extract_workflow_job_commands(text: str, job_name: str) -> list[str]:
    job_body = extract_job_body(text, job_name, VERIFY_YML)
    run_commands = extract_run_commands_from_job_body(
        job_body, source=VERIFY_YML, context=job_name
    )
    commands = extract_python_script_commands(
        run_commands, source=VERIFY_YML, include_args=False
    )
    if not commands:
        raise ValueError(f"No python3 scripts/* run commands found in {job_name} job in {VERIFY_YML}")
    return commands


def _extract_readme_job_commands(text: str, heading_pattern: str, label: str) -> list[str]:
    section = re.search(
        heading_pattern + r".*?\n(?P<body>(?:^\d+\.\s.*\n)+)",
        text,
        flags=re.MULTILINE,
    )
    if not section:
        raise ValueError(f"Could not locate '**`{label}` job**' numbered list in {SCRIPTS_README}")

    commands: list[str] = []
    for line in section.group("body").splitlines():
        code_spans = re.findall(r"`([^`]+)`", line)
        script_spans = [span for span in code_spans if ".py" in span]
        for cmd in script_spans:
            if cmd.startswith("python3 "):
                cmd = cmd[len("python3 ") :].strip()
            if cmd.startswith("scripts/"):
                cmd = cmd[len("scripts/") :]
            commands.append(_normalize_spaces(cmd).split()[0])

    if not commands:
        raise ValueError(f"No documented {label} script commands found in {SCRIPTS_README}")
    return commands


def main() -> int:
    workflow_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    all_errors: list[str] = []
    total_commands = 0

    for job_name, heading_pattern, label in _JOBS:
        workflow_commands = _extract_workflow_job_commands(workflow_text, job_name)
        readme_commands = _extract_readme_job_commands(readme_text, heading_pattern, label)

        errors = compare_lists(
            f"workflow {label} job", workflow_commands,
            f"README {label} list", readme_commands,
        )
        all_errors.extend(errors)
        total_commands += len(workflow_commands)

    if all_errors:
        print("verify build/docs sync check failed:", file=sys.stderr)
        for error in all_errors:
            print(error, file=sys.stderr)
        print(
            "\nUpdate scripts/README.md '**`build` job**' and '**`build-compiler` job**' "
            "command lists to match .github/workflows/verify.yml.",
            file=sys.stderr,
        )
        return 1

    print(
        "verify build/docs command list is synchronized "
        f"({total_commands} script commands across {len(_JOBS)} jobs)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
