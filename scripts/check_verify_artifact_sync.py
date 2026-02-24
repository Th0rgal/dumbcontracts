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


def _strip_yaml_inline_comment(raw: str) -> str:
    out: list[str] = []
    quote: str | None = None
    for ch in raw:
        if quote is None and ch in {"'", '"'}:
            quote = ch
            out.append(ch)
            continue
        if quote is not None and ch == quote:
            quote = None
            out.append(ch)
            continue
        if quote is None and ch == "#":
            break
        out.append(ch)
    return "".join(out).strip()


def _unquote_yaml_scalar(raw: str) -> str:
    if len(raw) >= 2 and raw[0] == raw[-1] and raw[0] in {"'", '"'}:
        return raw[1:-1]
    return raw


def _iter_step_blocks(job_body: str) -> list[str]:
    lines = job_body.splitlines()
    blocks: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if not re.match(r"^\s*-\s+\S", line):
            i += 1
            continue
        step_indent = len(line) - len(line.lstrip(" "))
        j = i + 1
        block_lines: list[str] = [line]
        while j < len(lines):
            child = lines[j]
            if child.strip() == "":
                block_lines.append(child)
                j += 1
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent <= step_indent:
                break
            block_lines.append(child)
            j += 1
        blocks.append("\n".join(block_lines))
        i = j
    return blocks


def _step_uses_action(step_block: str, action: str) -> bool:
    lines = step_block.splitlines()
    if not lines:
        return False
    step_indent = len(lines[0]) - len(lines[0].lstrip(" "))

    uses_value: str | None = None
    first = re.match(r"^\s*-\s+uses:\s*(?P<value>.+?)\s*$", lines[0])
    if first:
        uses_value = first.group("value")
    else:
        min_child_indent: int | None = None
        for line in lines[1:]:
            if not line.strip():
                continue
            child_indent = len(line) - len(line.lstrip(" "))
            if child_indent <= step_indent:
                continue
            if min_child_indent is None or child_indent < min_child_indent:
                min_child_indent = child_indent
        if min_child_indent is not None:
            for line in lines[1:]:
                if not line.strip():
                    continue
                child_indent = len(line) - len(line.lstrip(" "))
                if child_indent != min_child_indent:
                    continue
                m = re.match(r"^\s*uses:\s*(?P<value>.+?)\s*$", line)
                if m:
                    uses_value = m.group("value")
                    break

    if uses_value is None:
        return False
    uses_clean = _unquote_yaml_scalar(_strip_yaml_inline_comment(uses_value))
    return bool(re.fullmatch(rf"actions/{re.escape(action)}@v\d+", uses_clean))


def _iter_artifact_step_blocks(job_body: str, action: str) -> list[str]:
    return [block for block in _iter_step_blocks(job_body) if _step_uses_action(block, action)]


def _extract_name_from_with_block(step_block: str) -> str | None:
    lines = step_block.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^(?P<indent>\s*)with:\s*(?:#.*)?$", line)
        if not m:
            i += 1
            continue
        with_indent = len(m.group("indent"))
        j = i + 1
        block_lines: list[str] = []
        while j < len(lines):
            child = lines[j]
            if child.strip() == "":
                block_lines.append(child)
                j += 1
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent <= with_indent:
                break
            block_lines.append(child)
            j += 1

        min_child_indent: int | None = None
        for child in block_lines:
            if not child.strip():
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if min_child_indent is None or child_indent < min_child_indent:
                min_child_indent = child_indent

        if min_child_indent is None:
            i = j
            continue

        for child in block_lines:
            if not child.strip():
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent != min_child_indent:
                continue
            km = re.match(r"^\s*name:\s*(?P<value>.+?)\s*$", child)
            if not km:
                continue
            raw = _strip_yaml_inline_comment(km.group("value"))
            if not raw:
                continue
            return _unquote_yaml_scalar(raw)

        i = j
    return None


def _extract_upload_names(build_body: str) -> list[str]:
    names: list[str] = []
    for step_block in _iter_artifact_step_blocks(build_body, "upload-artifact"):
        name = _extract_name_from_with_block(step_block)
        if name is None:
            raise ValueError("Found upload-artifact step without a literal with.name entry")
        names.append(name)
    return names


def _extract_download_names(job_body: str) -> list[str]:
    names: list[str] = []
    for step_block in _iter_artifact_step_blocks(job_body, "download-artifact"):
        name = _extract_name_from_with_block(step_block)
        if name is None:
            raise ValueError("Found download-artifact step without a literal with.name entry")
        names.append(name)
    return names


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
