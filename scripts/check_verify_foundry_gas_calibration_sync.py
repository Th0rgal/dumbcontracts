#!/usr/bin/env python3
"""Ensure foundry-gas-calibration workflow settings stay synchronized with docs."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from workflow_jobs import extract_job_body

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SCRIPTS_README = ROOT / "scripts" / "README.md"


def _extract_foundry_gas_calibration_job(text: str) -> str:
    return extract_job_body(text, "foundry-gas-calibration", VERIFY_YML)


def _normalize_scalar(raw: str) -> str:
    value = raw.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in {'"', "'"}:
        return value[1:-1]
    value = re.sub(r"\s+#.*$", "", value).strip()
    return value


def _leading_spaces(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _extract_named_step_body(job_body: str, step_name: str) -> str:
    lines = job_body.splitlines()
    for i, line in enumerate(lines):
        m = re.match(r"^(?P<indent>\s*)-\s+name:\s*(?P<name>.+?)\s*$", line)
        if not m:
            continue
        if _normalize_scalar(m.group("name")) != step_name:
            continue

        indent = m.group("indent")
        body_lines: list[str] = []
        for j in range(i + 1, len(lines)):
            if re.match(rf"^{re.escape(indent)}-\s+", lines[j]):
                break
            body_lines.append(lines[j])
        return "\n".join(body_lines) + ("\n" if body_lines else "")

    raise ValueError(
        f"Could not locate '{step_name}' step in foundry-gas-calibration job in {VERIFY_YML}"
    )


def _extract_mapping_value(step_body: str, block_name: str, key: str, context: str) -> str:
    lines = step_body.splitlines()
    for i, line in enumerate(lines):
        m = re.match(rf"^(?P<indent>\s*){re.escape(block_name)}:\s*$", line)
        if not m:
            continue

        block_indent = _leading_spaces(line)
        for j in range(i + 1, len(lines)):
            inner = lines[j]
            if _leading_spaces(inner) <= block_indent:
                break
            k = re.match(rf"^\s*{re.escape(key)}:\s*(.+?)\s*$", inner)
            if k:
                return _normalize_scalar(k.group(1))

        raise ValueError(f"Could not locate {key} in {block_name} block for {context} in {VERIFY_YML}")

    raise ValueError(f"Could not locate {block_name} block for {context} in {VERIFY_YML}")


def _extract_foundry_profile(job_body: str) -> str:
    step_body = _extract_named_step_body(job_body, "Check static-vs-foundry gas calibration")
    return _extract_mapping_value(step_body, "env", "FOUNDRY_PROFILE", "calibration step")


def _extract_static_report_artifact(job_body: str) -> str:
    step_body = _extract_named_step_body(job_body, "Download static gas report")
    uses_m = re.search(r"^\s*uses:\s*(.+?)\s*$", step_body, flags=re.MULTILINE)
    if not uses_m:
        raise ValueError(
            "Could not locate uses key in Download static gas report step in "
            f"{VERIFY_YML}"
        )
    uses_value = _normalize_scalar(uses_m.group(1))
    if not uses_value.startswith("actions/download-artifact@"):
        raise ValueError(
            "Download static gas report step must use actions/download-artifact@<ref> in "
            f"{VERIFY_YML}"
        )
    return _extract_mapping_value(step_body, "with", "name", "download static gas report step")


def _extract_run_text(step_body: str, context: str) -> str:
    lines = step_body.splitlines()
    for i, line in enumerate(lines):
        m = re.match(r"^(?P<indent>\s*)run:\s*(?P<value>.*)\s*$", line)
        if not m:
            continue
        value = m.group("value").strip()
        if value and not value.startswith("|") and not value.startswith(">"):
            return value

        run_indent = _leading_spaces(line)
        block_lines: list[str] = []
        for j in range(i + 1, len(lines)):
            inner = lines[j]
            if _leading_spaces(inner) <= run_indent:
                break
            block_lines.append(inner.strip())
        if not block_lines:
            raise ValueError(f"Run block is empty for {context} in {VERIFY_YML}")
        return "\n".join(block_lines)

    raise ValueError(f"Could not locate run command for {context} in {VERIFY_YML}")


def _extract_calibration_command(job_body: str) -> str:
    step_body = _extract_named_step_body(job_body, "Check static-vs-foundry gas calibration")
    run_text = _extract_run_text(step_body, "calibration step")
    m = re.search(
        r"(python3\s+scripts/check_gas_calibration\.py\s+--static-report\s+\S+)",
        run_text,
    )
    if not m:
        raise ValueError(
            "Could not locate check_gas_calibration command in "
            f"foundry-gas-calibration calibration step in {VERIFY_YML}"
        )
    return re.sub(r"\s+", " ", m.group(1).strip())


def _extract_readme_summary_line(text: str) -> str:
    m = re.search(r"^\*\*`foundry-gas-calibration`\*\*.*$", text, flags=re.MULTILINE)
    if not m:
        raise ValueError(
            "Could not locate foundry-gas-calibration CI summary line in "
            f"{SCRIPTS_README}"
        )
    return m.group(0)


def main() -> int:
    verify_text = VERIFY_YML.read_text(encoding="utf-8")
    readme_text = SCRIPTS_README.read_text(encoding="utf-8")

    job_body = _extract_foundry_gas_calibration_job(verify_text)
    foundry_profile = _extract_foundry_profile(job_body)
    artifact_name = _extract_static_report_artifact(job_body)
    command = _extract_calibration_command(job_body)
    readme_line = _extract_readme_summary_line(readme_text)

    errors: list[str] = []
    if foundry_profile != "difftest":
        errors.append(
            "verify.yml foundry-gas-calibration must keep FOUNDRY_PROFILE=difftest."
        )
    if artifact_name != "static-gas-report":
        errors.append(
            "verify.yml foundry-gas-calibration must download static-gas-report artifact."
        )
    if "check_gas_calibration.py" not in command:
        errors.append(
            "verify.yml foundry-gas-calibration must run scripts/check_gas_calibration.py."
        )
    if "--static-report gas-report-static.tsv" not in command:
        errors.append(
            "verify.yml foundry-gas-calibration must pass --static-report gas-report-static.tsv."
        )
    if "check_gas_calibration.py" not in readme_line:
        errors.append(
            "scripts/README.md foundry-gas-calibration summary must mention check_gas_calibration.py."
        )
    if "static report" not in readme_line.lower():
        errors.append(
            "scripts/README.md foundry-gas-calibration summary must mention static report input."
        )
    if "Foundry gas report" not in readme_line:
        errors.append(
            "scripts/README.md foundry-gas-calibration summary must mention Foundry gas report input."
        )

    if errors:
        print("verify foundry-gas-calibration sync check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        print(f"  verify.yml FOUNDRY_PROFILE: {foundry_profile}", file=sys.stderr)
        print(f"  verify.yml artifact name:   {artifact_name}", file=sys.stderr)
        print(f"  verify.yml command:         {command}", file=sys.stderr)
        print(f"  README summary line:        {readme_line}", file=sys.stderr)
        return 1

    print(
        "verify foundry-gas-calibration settings are synchronized across workflow/docs "
        "(profile difftest, static-gas-report, check_gas_calibration.py)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
