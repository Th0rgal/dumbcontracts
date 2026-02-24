"""Helpers for extracting top-level GitHub Actions jobs from verify.yml."""

from __future__ import annotations

import re
from pathlib import Path

_JOB_KEY_RE = re.compile(
    r"""^  (?P<key>(?:[A-Za-z0-9_-]+)|(?:"[^"\n]+")|(?:'[^'\n]+')):\s*(?:#.*)?$"""
)


def _unquote_key(raw: str) -> str:
    if len(raw) >= 2 and raw[0] == raw[-1] and raw[0] in {"'", '"'}:
        return raw[1:-1]
    return raw


def _jobs_region(lines: list[str], source: Path) -> tuple[int, int]:
    jobs_idx = next((i for i, line in enumerate(lines) if line == "jobs:"), None)
    if jobs_idx is None:
        raise ValueError(f"Could not locate jobs section in {source}")

    end_idx = len(lines)
    for i in range(jobs_idx + 1, len(lines)):
        line = lines[i]
        if line and not line.startswith(" "):
            end_idx = i
            break
    return jobs_idx + 1, end_idx


def _extract_headers(lines: list[str], source: Path) -> list[tuple[str, int]]:
    start_idx, end_idx = _jobs_region(lines, source)

    headers: list[tuple[str, int]] = []
    for i in range(start_idx, end_idx):
        m = _JOB_KEY_RE.match(lines[i])
        if m:
            headers.append((_unquote_key(m.group("key")), i))

    if not headers:
        raise ValueError(f"Could not locate any top-level jobs in {source}")
    return headers


def extract_top_level_jobs(text: str, source: Path) -> list[str]:
    return [name for name, _ in _extract_headers(text.splitlines(), source)]


def extract_job_body(text: str, job_name: str, source: Path) -> str:
    lines = text.splitlines()
    headers = _extract_headers(lines, source)

    for idx, (name, line_idx) in enumerate(headers):
        if name != job_name:
            continue
        body_start = line_idx + 1
        body_end = headers[idx + 1][1] if idx + 1 < len(headers) else len(lines)
        body = "\n".join(lines[body_start:body_end])
        return body + ("\n" if body else "")

    raise ValueError(f"Could not locate '{job_name}' job in {source}")
