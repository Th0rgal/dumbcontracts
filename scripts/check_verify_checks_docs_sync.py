#!/usr/bin/env python3
"""Ensure verify.yml checks-job script list matches scripts/README.md docs."""

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


def _extract_workflow_checks_commands(text: str) -> list[str]:
    job_body = extract_job_body(text, "checks", VERIFY_YML)
    run_commands = extract_run_commands_from_job_body(
        job_body, source=VERIFY_YML, context="checks"
    )
    commands = extract_python_script_commands(run_commands, source=VERIFY_YML)

    if not commands:
        raise ValueError(f"No python3 scripts/* run commands found in checks job in {VERIFY_YML}")
    return commands


def _extract_readme_checks_commands(text: str) -> list[str]:
    section = re.search(
        r"^\*\*`checks` job\*\*.*?\n(?P<body>(?:^\d+\.\s.*\n)+)",
        text,
        flags=re.MULTILINE,
    )
    if not section:
        raise ValueError(f"Could not locate '**`checks` job**' numbered list in {SCRIPTS_README}")

    commands: list[str] = []
    for line in section.group("body").splitlines():
        cmd = re.search(r"\(`([^`]+)`\)", line)
        if not cmd:
            raise ValueError(f"Could not parse command from README checks line: {line!r}")
        commands.append(cmd.group(1).strip())
    if not commands:
        raise ValueError(f"No documented checks commands found in {SCRIPTS_README}")
    return commands


def main() -> int:
    workflow_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    workflow_commands = _extract_workflow_checks_commands(workflow_text)
    readme_commands = _extract_readme_checks_commands(readme_text)

    errors = compare_lists("workflow checks job", workflow_commands, "README checks list", readme_commands)
    if errors:
        print("verify checks/docs sync check failed:", file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        print(
            "\nUpdate scripts/README.md '**`checks` job**' command list to match "
            ".github/workflows/verify.yml checks job.",
            file=sys.stderr,
        )
        return 1

    print(
        "verify checks/docs command list is synchronized "
        f"({len(workflow_commands)} commands)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
