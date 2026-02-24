#!/usr/bin/env python3
"""Ensure verify.yml checks-job script list matches scripts/README.md docs."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from workflow_jobs import extract_job_body

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SCRIPTS_README = ROOT / "scripts" / "README.md"


def _normalize_workflow_cmd(raw: str) -> str:
    text = " ".join(raw.strip().split())
    if not text.startswith("python3 "):
        raise ValueError(f"Expected python3 scripts command, got: {raw!r}")
    text = text[len("python3 ") :].strip()
    if not text.startswith("scripts/"):
        raise ValueError(f"Expected scripts/ path command, got: {raw!r}")
    return text[len("scripts/") :]


def _extract_workflow_checks_commands(text: str) -> list[str]:
    job_body = extract_job_body(text, "checks", VERIFY_YML)
    lines = job_body.splitlines()
    steps_idx = next((i for i, line in enumerate(lines) if line == "    steps:"), None)
    if steps_idx is None:
        raise ValueError(f"Could not locate checks.steps in {VERIFY_YML}")

    steps_indent = len(lines[steps_idx]) - len(lines[steps_idx].lstrip(" "))
    steps: list[str] = []
    for line in lines[steps_idx + 1 :]:
        if line.strip():
            indent = len(line) - len(line.lstrip(" "))
            if indent <= steps_indent:
                break
        steps.append(line)

    commands: list[str] = []
    i = 0
    while i < len(steps):
        line = steps[i]
        m = re.match(r"^(\s*)run:\s*(.*?)\s*$", line)
        if not m:
            i += 1
            continue

        indent = len(m.group(1))
        payload = m.group(2)
        block_lines: list[str] = []
        if payload.startswith("|") or payload.startswith(">"):
            i += 1
            while i < len(steps):
                nxt = steps[i]
                if not nxt.strip():
                    block_lines.append("")
                    i += 1
                    continue
                if len(nxt) - len(nxt.lstrip(" ")) <= indent:
                    break
                block_lines.append(nxt[indent + 2 :])
                i += 1
        else:
            block_lines.append(payload)
            i += 1

        commands.extend(_extract_python_script_commands(block_lines))

    if not commands:
        raise ValueError(f"No python3 scripts/* run commands found in checks job in {VERIFY_YML}")
    return commands


def _extract_python_script_commands(block_lines: list[str]) -> list[str]:
    commands: list[str] = []
    i = 0
    while i < len(block_lines):
        stripped = block_lines[i].strip()
        if not stripped or stripped.startswith("#"):
            i += 1
            continue

        if not stripped.startswith("python3 scripts/"):
            i += 1
            continue

        cmd = stripped
        if "#" in cmd:
            cmd = cmd.split("#", 1)[0].rstrip()
        while cmd.endswith("\\"):
            cmd = cmd[:-1].rstrip()
            i += 1
            if i >= len(block_lines):
                raise ValueError(
                    "Trailing line-continuation in python3 scripts command in "
                    f"{VERIFY_YML}: {stripped!r}"
                )
            continuation = block_lines[i].strip()
            if continuation:
                if "#" in continuation:
                    continuation = continuation.split("#", 1)[0].rstrip()
                if continuation:
                    cmd += " " + continuation

        commands.append(_normalize_workflow_cmd(cmd))
        i += 1
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


def _compare(expected: list[str], actual: list[str]) -> list[str]:
    if expected == actual:
        return []

    errors: list[str] = []
    expected_set = set(expected)
    actual_set = set(actual)

    missing = [cmd for cmd in expected if cmd not in actual_set]
    extra = [cmd for cmd in actual if cmd not in expected_set]

    if missing:
        errors.append("README checks list is missing workflow commands:")
        errors.extend([f"  - {m}" for m in missing])
    if extra:
        errors.append("README checks list has commands not present in workflow checks job:")
        errors.extend([f"  - {e}" for e in extra])
    if not missing and not extra:
        errors.append(
            "README checks list contains the same commands but in a different order. "
            "Keep exact order aligned with workflow for auditability."
        )
    return errors


def main() -> int:
    workflow_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    workflow_commands = _extract_workflow_checks_commands(workflow_text)
    readme_commands = _extract_readme_checks_commands(readme_text)

    errors = _compare(workflow_commands, readme_commands)
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
