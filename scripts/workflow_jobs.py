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


def _extract_mapping_blocks(body: str, mapping_name: str) -> list[tuple[int, list[str]]]:
    lines = body.splitlines()
    blocks: list[tuple[int, list[str]]] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(rf"^(?P<indent>\s*){re.escape(mapping_name)}:\s*(?:#.*)?$", line)
        if not m:
            i += 1
            continue

        indent = len(m.group("indent"))
        j = i + 1
        block_lines: list[str] = []
        while j < len(lines):
            child = lines[j]
            if child.strip() == "":
                block_lines.append(child)
                j += 1
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent <= indent:
                break
            block_lines.append(child)
            j += 1

        if block_lines:
            blocks.append((indent, block_lines))
        i = j

    return blocks


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


def extract_literal_from_mapping_blocks(
    body: str, mapping_name: str, key: str, *, source: Path, context: str
) -> str:
    """Extract a scalar key from mapping blocks (for example `env:`) inside a job body.

    Fails closed when the key is missing or has conflicting values across blocks.
    """

    values: list[str] = []
    for parent_indent, block in _extract_mapping_blocks(body, mapping_name):
        min_child_indent: int | None = None
        for line in block:
            if not line.strip():
                continue
            child_indent = len(line) - len(line.lstrip(" "))
            if min_child_indent is None or child_indent < min_child_indent:
                min_child_indent = child_indent
        if min_child_indent is None:
            continue

        for line in block:
            if not line.strip():
                continue
            child_indent = len(line) - len(line.lstrip(" "))
            if child_indent != min_child_indent or child_indent <= parent_indent:
                continue
            m = re.match(rf"^\s*{re.escape(key)}:\s*(?P<value>.+?)\s*$", line)
            if m:
                raw = _strip_yaml_inline_comment(m.group("value"))
                if raw:
                    values.append(_unquote_yaml_scalar(raw))

    if not values:
        raise ValueError(
            f"Could not locate {key} in {context} {mapping_name} block in {source}"
        )

    unique = set(values)
    if len(unique) > 1:
        rendered = ", ".join(sorted(unique))
        raise ValueError(
            f"Found conflicting {key} values in {context} {mapping_name} blocks in {source}: {rendered}"
        )

    return values[0]


def extract_run_commands_from_job_body(body: str, *, source: Path, context: str) -> list[str]:
    """Extract executable shell command lines from `run:` steps in a job body.

    Parses only the `steps:` section and ignores comments/blank lines.
    """

    lines = body.splitlines()
    steps_idx = next(
        (
            i
            for i, line in enumerate(lines)
            if re.match(r"^\s*steps:\s*(?:#.*)?$", line)
        ),
        None,
    )
    if steps_idx is None:
        raise ValueError(f"Could not locate {context}.steps in {source}")

    steps_indent = len(lines[steps_idx]) - len(lines[steps_idx].lstrip(" "))
    step_lines: list[str] = []
    for line in lines[steps_idx + 1 :]:
        if line.strip():
            indent = len(line) - len(line.lstrip(" "))
            if indent <= steps_indent:
                break
        step_lines.append(line)

    commands: list[str] = []
    i = 0
    while i < len(step_lines):
        line = step_lines[i]
        m = re.match(r"^(?P<indent>\s*)(?:-\s*)?run:\s*(?P<payload>.*?)\s*$", line)
        if not m:
            i += 1
            continue

        indent = len(m.group("indent"))
        payload = m.group("payload")
        block_lines: list[str] = []
        if payload.startswith("|") or payload.startswith(">"):
            i += 1
            while i < len(step_lines):
                nxt = step_lines[i]
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

        for raw in block_lines:
            stripped = raw.strip()
            if not stripped or stripped.startswith("#"):
                continue
            commands.append(stripped)

    if not commands:
        raise ValueError(f"Could not locate executable run commands in {context} job in {source}")
    return commands
