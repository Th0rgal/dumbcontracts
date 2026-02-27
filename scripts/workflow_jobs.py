"""Helpers for extracting and comparing GitHub Actions workflow data."""

from __future__ import annotations

import re
import shlex
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


def strip_yaml_inline_comment(raw: str) -> str:
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


def unquote_yaml_scalar(raw: str) -> str:
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
                raw = strip_yaml_inline_comment(m.group("value"))
                if raw:
                    values.append(unquote_yaml_scalar(raw))

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
            is_folded = payload.startswith(">")
            i += 1
            scalar_lines: list[str] = []
            while i < len(step_lines):
                nxt = step_lines[i]
                if not nxt.strip():
                    scalar_lines.append("")
                    i += 1
                    continue
                if len(nxt) - len(nxt.lstrip(" ")) <= indent:
                    break
                scalar_lines.append(nxt[indent + 2 :])
                i += 1
            if is_folded:
                # Keep command boundaries, but merge obvious continuation fragments
                # (for example lines starting with CLI flags).
                current: str | None = None
                for raw_line in scalar_lines:
                    part = raw_line.strip()
                    if not part:
                        if current is not None:
                            block_lines.append(current)
                            current = None
                        continue
                    if current is None:
                        current = part
                        continue
                    if part.startswith(("-", "&&", "||", "|", ";")):
                        current += " " + part
                        continue
                    block_lines.append(current)
                    current = part
                if current is not None:
                    block_lines.append(current)
            else:
                block_lines.extend(scalar_lines)
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


def _strip_shell_inline_comment(raw: str) -> str:
    out: list[str] = []
    quote: str | None = None
    escaped = False
    for idx, ch in enumerate(raw):
        if escaped:
            out.append(ch)
            escaped = False
            continue
        if ch == "\\":
            out.append(ch)
            escaped = True
            continue
        if quote is None and ch in {"'", '"'}:
            quote = ch
            out.append(ch)
            continue
        if quote is not None and ch == quote:
            quote = None
            out.append(ch)
            continue
        if quote is None and ch == "#" and (idx == 0 or raw[idx - 1].isspace()):
            break
        out.append(ch)
    return "".join(out).rstrip()


def extract_python_script_commands(
    run_commands: list[str],
    *,
    source: Path,
    command_prefix: str = "python3 scripts/",
    include_args: bool = True,
) -> list[str]:
    """Extract normalized `python3 scripts/*` commands from run command lines.

    Supports shell line continuations and inline comments.
    """

    commands: list[str] = []
    i = 0
    while i < len(run_commands):
        stripped = run_commands[i].strip()
        if not stripped or stripped.startswith("#"):
            i += 1
            continue

        if not stripped.startswith(command_prefix):
            i += 1
            continue

        cmd = _strip_shell_inline_comment(stripped)
        while cmd.endswith("\\"):
            cmd = cmd[:-1].rstrip()
            i += 1
            if i >= len(run_commands):
                raise ValueError(
                    "Trailing line-continuation in scripts command "
                    f"in {source}: {stripped!r}"
                )
            continuation = _strip_shell_inline_comment(run_commands[i].strip())
            if continuation:
                cmd += " " + continuation

        normalized = " ".join(cmd.split())
        if not normalized.startswith(command_prefix):
            raise ValueError(f"Expected scripts command prefixed by {command_prefix!r}, got: {cmd!r}")

        script = normalized[len(command_prefix) :]
        if not include_args:
            script = script.split()[0]
        commands.append(script)
        i += 1

    return commands


_SHELL_ASSIGNMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=.*$")


def _basename_token(token: str) -> str:
    return token.rsplit("/", 1)[-1]


def _token_matches_program(token: str, program: str) -> bool:
    return token == program or _basename_token(token) == program


def _consume_time_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "time"):
        return i
    i += 1
    time_opts_with_arg = {"-f", "--format", "-o", "--output"}
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok in time_opts_with_arg:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if tok.startswith("-"):
            i += 1
            continue
        break
    return i


def _consume_timeout_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "timeout"):
        return i
    i += 1
    timeout_opts_with_arg = {"-k", "--kill-after", "-s", "--signal"}
    timeout_options_done = False
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            timeout_options_done = True
            i += 1
            continue
        if not timeout_options_done and tok in timeout_opts_with_arg:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if not timeout_options_done and tok.startswith("-"):
            i += 1
            continue
        break
    if i < len(tokens):
        i += 1
    return i


def _consume_nice_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "nice"):
        return i
    i += 1
    if i < len(tokens) and tokens[i] in {"-n", "--adjustment"}:
        i += 1
        if i < len(tokens):
            i += 1
    while i < len(tokens) and tokens[i].startswith("-"):
        i += 1
    return i


def _consume_nohup_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "nohup"):
        return i
    i += 1
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok.startswith("-"):
            i += 1
            continue
        break
    return i


def _consume_setsid_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "setsid"):
        return i
    i += 1
    setsid_opts_without_arg = {
        "-w",
        "--wait",
        "-c",
        "--ctty",
        "-f",
        "--fork",
        "-s",
        "--session-leader",
    }
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok in setsid_opts_without_arg:
            i += 1
            continue
        if tok.startswith("-"):
            i += 1
            continue
        break
    return i


def _consume_ionice_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "ionice"):
        return i
    i += 1
    ionice_opts_with_arg = {
        "-c",
        "--class",
        "-n",
        "--classdata",
        "-p",
        "--pid",
        "-P",
        "--pgid",
        "-u",
        "--uid",
    }
    ionice_opts_without_arg = {"-t", "--ignore"}
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok in ionice_opts_without_arg:
            i += 1
            continue
        if tok in ionice_opts_with_arg:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if any(tok.startswith(prefix + "=") for prefix in ionice_opts_with_arg if prefix.startswith("--")):
            i += 1
            continue
        if tok.startswith("-"):
            i += 1
            continue
        break
    return i


def _consume_chrt_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "chrt"):
        return i
    i += 1
    chrt_opts_without_arg = {
        "-a",
        "--all-tasks",
        "-d",
        "--deadline",
        "-f",
        "--fifo",
        "-i",
        "--idle",
        "-m",
        "--max",
        "-o",
        "--other",
        "-r",
        "--rr",
        "-R",
        "--reset-on-fork",
    }
    chrt_opts_with_arg = {
        "-p",
        "--pid",
        "-T",
        "--sched-runtime",
        "-P",
        "--sched-period",
        "-D",
        "--sched-deadline",
    }
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok in chrt_opts_with_arg:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if any(tok.startswith(prefix + "=") for prefix in chrt_opts_with_arg if prefix.startswith("--")):
            i += 1
            continue
        if tok.startswith("-"):
            i += 1
            continue
        break
    # For command-launch mode, `chrt` accepts a positional priority token
    # before the wrapped command (for example: `chrt --rr 50 forge test`).
    if i < len(tokens) and re.fullmatch(r"[+-]?\d+", tokens[i]):
        i += 1
    return i


def _consume_stdbuf_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "stdbuf"):
        return i
    i += 1
    stdbuf_opts_with_arg = {"-i", "-o", "-e"}
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok in stdbuf_opts_with_arg:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if any(tok.startswith(prefix) and len(tok) > 2 for prefix in stdbuf_opts_with_arg):
            i += 1
            continue
        if tok.startswith("-"):
            i += 1
            continue
        break
    return i


def _consume_sudo_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "sudo"):
        return i
    i += 1
    sudo_opts_with_arg = {
        "-u",
        "--user",
        "-g",
        "--group",
        "-h",
        "--host",
        "-p",
        "--prompt",
        "-C",
        "--close-from",
    }
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok in sudo_opts_with_arg:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if any(tok.startswith(prefix + "=") for prefix in sudo_opts_with_arg if prefix.startswith("--")):
            i += 1
            continue
        if tok.startswith("-"):
            i += 1
            continue
        break
    return i


def _consume_command_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "command"):
        return i
    i += 1
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok in {"-p", "-v", "-V"}:
            i += 1
            continue
        if (
            len(tok) > 1
            and tok.startswith("-")
            and not tok.startswith("--")
            and set(tok[1:]).issubset({"p", "v", "V"})
        ):
            i += 1
            continue
        break
    return i


def _consume_env_wrapper(tokens: list[str], i: int) -> int:
    if i >= len(tokens) or not _token_matches_program(tokens[i], "env"):
        return i
    i += 1
    env_opts_with_arg = {"-u", "--unset", "-C", "--chdir", "-S", "--split-string"}
    split_string_long_eq = "--split-string="
    env_options_done = False
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            env_options_done = True
            i += 1
            continue
        if not env_options_done and tok in env_opts_with_arg:
            if tok in {"-S", "--split-string"}:
                # `env -S 'FOO=1 forge test'` injects split-string tokens as if
                # they were written in argv directly. Expand in-place so wrapper
                # normalization can continue on the resulting assignments/command.
                i += 1
                if i < len(tokens):
                    try:
                        split_tokens = shlex.split(tokens[i], posix=True)
                    except ValueError:
                        split_tokens = []
                    tokens[i : i + 1] = split_tokens
                continue
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if not env_options_done and tok.startswith(split_string_long_eq):
            try:
                split_tokens = shlex.split(tok[len(split_string_long_eq) :], posix=True)
            except ValueError:
                split_tokens = []
            tokens[i : i + 1] = split_tokens
            continue
        if not env_options_done and tok.startswith("-S") and tok != "-S":
            try:
                split_tokens = shlex.split(tok[2:], posix=True)
            except ValueError:
                split_tokens = []
            tokens[i : i + 1] = split_tokens
            continue
        if (
            not env_options_done
            and (tok.startswith("--unset=") or tok.startswith("--chdir="))
        ):
            i += 1
            continue
        if not env_options_done and tok.startswith("-u") and tok != "-u":
            i += 1
            continue
        if not env_options_done and tok.startswith("-C") and tok != "-C":
            i += 1
            continue
        if not env_options_done and tok.startswith("-"):
            i += 1
            continue
        if _SHELL_ASSIGNMENT_RE.match(tok):
            i += 1
            continue
        break
    return i


def parse_shell_command_tokens(raw: str) -> list[str]:
    """Parse a shell command line into tokens after stripping inline comments."""

    stripped = _strip_shell_inline_comment(raw.strip())
    if not stripped:
        return []
    try:
        return shlex.split(stripped, posix=True)
    except ValueError:
        # Fail closed for malformed shell quoting.
        return []


def match_shell_command(
    raw: str,
    *,
    program: str,
    args_prefix: tuple[str, ...] = (),
) -> tuple[bool, list[str]]:
    """Match shell commands while tolerating leading env assignments.

    Supports forms like:
      FOO=1 BAR=2 forge test ...
      env FOO=1 BAR=2 forge test ...
      env -i FOO=1 forge test ...
      env -u FOO -- forge test ...
    """

    tokens = parse_shell_command_tokens(raw)
    if not tokens:
        return False, []

    i = 0
    changed = True
    while changed:
        changed = False

        while i < len(tokens) and _SHELL_ASSIGNMENT_RE.match(tokens[i]):
            i += 1
            changed = True

        while True:
            nxt = _consume_command_wrapper(tokens, i)
            if nxt == i:
                break
            i = nxt
            changed = True

        nxt = _consume_env_wrapper(tokens, i)
        if nxt != i:
            i = nxt
            changed = True

        while True:
            nxt = _consume_sudo_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_stdbuf_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_time_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_timeout_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_nice_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_nohup_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_setsid_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_ionice_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            nxt = _consume_chrt_wrapper(tokens, i)
            if nxt != i:
                i = nxt
                changed = True
                continue
            break

    if i >= len(tokens) or not _token_matches_program(tokens[i], program):
        return False, tokens

    for offset, expected in enumerate(args_prefix, start=1):
        idx = i + offset
        if idx >= len(tokens) or tokens[idx] != expected:
            return False, tokens

    return True, tokens[i:]


def compare_lists(
    reference_name: str,
    reference: list[str],
    other_name: str,
    other: list[str],
) -> list[str]:
    """Compare two ordered lists and return human-readable error descriptions.

    Detects missing items, extra items, and order-only mismatches.
    Returns an empty list when the lists are identical.
    """
    if reference == other:
        return []

    errors: list[str] = []
    ref_set = set(reference)
    other_set = set(other)

    missing = [item for item in reference if item not in other_set]
    extra = [item for item in other if item not in ref_set]

    if missing:
        errors.append(f"{other_name} is missing entries present in {reference_name}:")
        errors.extend([f"  - {m}" for m in missing])
    if extra:
        errors.append(f"{other_name} has entries not present in {reference_name}:")
        errors.extend([f"  - {e}" for e in extra])
    if not missing and not extra:
        errors.append(
            f"{other_name} contains the same entries as {reference_name} but in a different order."
        )
    return errors


def parse_csv_ints(raw: str, source: Path) -> list[int]:
    """Parse a comma-separated list of integers, failing closed on bad input."""
    parts = [part.strip() for part in raw.split(",")]
    if not parts or any(not part for part in parts):
        raise ValueError(f"Malformed integer CSV in {source}: {raw!r}")
    try:
        return [int(part) for part in parts]
    except ValueError as exc:
        raise ValueError(f"Non-integer value in {source}: {raw!r}") from exc
