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


def _extract_foundry_profile(job_body: str) -> str:
    m = re.search(r'^\s*FOUNDRY_PROFILE:\s*(?:"([^"]+)"|(\S+))\s*$', job_body, re.MULTILINE)
    if not m:
        raise ValueError(
            f"Could not locate FOUNDRY_PROFILE in foundry-gas-calibration job in {VERIFY_YML}"
        )
    return m.group(1) or m.group(2)


def _extract_static_report_artifact(job_body: str) -> str:
    m = re.search(
        r"^\s*with:\s*\n\s*name:\s*(\S+)\s*$",
        job_body,
        flags=re.MULTILINE,
    )
    if not m:
        raise ValueError(
            "Could not locate download-artifact name in foundry-gas-calibration "
            f"job in {VERIFY_YML}"
        )
    return m.group(1)


def _extract_calibration_command(job_body: str) -> str:
    m = re.search(
        r"^\s*run:\s*(python3\s+scripts/check_gas_calibration\.py\s+--static-report\s+\S+)\s*$",
        job_body,
        flags=re.MULTILINE,
    )
    if not m:
        raise ValueError(
            "Could not locate check_gas_calibration command in "
            f"foundry-gas-calibration job in {VERIFY_YML}"
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
