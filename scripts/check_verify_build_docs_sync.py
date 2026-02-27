#!/usr/bin/env python3
"""Ensure verify.yml build-job script list matches scripts/README.md docs."""

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


def _normalize_spaces(text: str) -> str:
    return " ".join(text.split())


def _extract_workflow_build_commands(text: str) -> list[str]:
    job_body = extract_job_body(text, "build", VERIFY_YML)
    run_commands = extract_run_commands_from_job_body(
        job_body, source=VERIFY_YML, context="build"
    )
    commands = extract_python_script_commands(
        run_commands, source=VERIFY_YML, include_args=False
    )
    if not commands:
        raise ValueError(f"No python3 scripts/* run commands found in build job in {VERIFY_YML}")
    return commands


def _extract_readme_build_commands(text: str) -> list[str]:
    section = re.search(
        r"^\*\*`build` job\*\*.*?\n(?P<body>(?:^\d+\.\s.*\n)+)",
        text,
        flags=re.MULTILINE,
    )
    if not section:
        raise ValueError(f"Could not locate '**`build` job**' numbered list in {SCRIPTS_README}")

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
        raise ValueError(f"No documented build script commands found in {SCRIPTS_README}")
    return commands


def main() -> int:
    workflow_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    workflow_commands = _extract_workflow_build_commands(workflow_text)
    readme_commands = _extract_readme_build_commands(readme_text)

    errors = compare_lists("workflow build job", workflow_commands, "README build list", readme_commands)
    if errors:
        print("verify build/docs sync check failed:", file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        print(
            "\nUpdate scripts/README.md '**`build` job**' command list to match "
            ".github/workflows/verify.yml build job.",
            file=sys.stderr,
        )
        return 1

    print(
        "verify build/docs command list is synchronized "
        f"({len(workflow_commands)} script commands)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
