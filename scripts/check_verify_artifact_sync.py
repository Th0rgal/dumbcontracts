#!/usr/bin/env python3
"""Ensure verify.yml artifact uploads/downloads stay synchronized."""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

from workflow_jobs import extract_job_body, extract_top_level_jobs

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"


def _extract_job_block(text: str, job_name: str) -> str:
    return extract_job_body(text, job_name, VERIFY_YML)


def _extract_upload_names(build_body: str) -> list[str]:
    return re.findall(
        r"actions/upload-artifact@v\d+\n\s+with:\n\s+name:\s*([^\s]+)",
        build_body,
        flags=re.MULTILINE,
    )


def _extract_download_names(job_body: str) -> list[str]:
    return re.findall(
        r"actions/download-artifact@v\d+\n\s+with:\n\s+name:\s*([^\s]+)",
        job_body,
        flags=re.MULTILINE,
    )


def _extract_job_names(text: str) -> list[str]:
    return extract_top_level_jobs(text, VERIFY_YML)


def _duplicates(items: list[str]) -> list[str]:
    counts = Counter(items)
    return sorted([name for name, count in counts.items() if count > 1])


def main() -> int:
    verify_text = VERIFY_YML.read_text(encoding="utf-8")
    job_names = _extract_job_names(verify_text)

    build_body = _extract_job_block(verify_text, "build")
    upload_names = _extract_upload_names(build_body)
    if not upload_names:
        raise ValueError(
            "Could not locate any build upload-artifact names in "
            f"{VERIFY_YML} build job"
        )

    upload_dupes = _duplicates(upload_names)
    errors: list[str] = []
    if upload_dupes:
        errors.append(
            "build job has duplicate upload-artifact names: "
            + ", ".join(upload_dupes)
        )

    uploaded = set(upload_names)
    consumed_missing: list[tuple[str, str]] = []
    consumed_summary: list[tuple[str, str]] = []

    for job in job_names:
        if job == "build":
            continue
        body = _extract_job_block(verify_text, job)
        downloads = _extract_download_names(body)
        if not downloads:
            continue
        download_dupes = _duplicates(downloads)
        if download_dupes:
            errors.append(
                f"{job} job has duplicate download-artifact names: "
                + ", ".join(download_dupes)
            )
        for name in downloads:
            consumed_summary.append((job, name))
            if name not in uploaded:
                consumed_missing.append((job, name))

    if consumed_missing:
        errors.append(
            "Downloaded artifacts missing from build uploads:\n"
            + "\n".join([f"  - {job}: {name}" for job, name in consumed_missing])
        )

    if errors:
        print("verify artifact upload/download sync check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        print(
            "\nBuild uploads found: "
            + ", ".join(sorted(uploaded)),
            file=sys.stderr,
        )
        if consumed_summary:
            print("Downloads found:", file=sys.stderr)
            for job, name in consumed_summary:
                print(f"  - {job}: {name}", file=sys.stderr)
        return 1

    print(
        "verify artifact upload/download names are synchronized "
        f"(build uploads: {len(upload_names)}, downstream downloads: {len(consumed_summary)})."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
