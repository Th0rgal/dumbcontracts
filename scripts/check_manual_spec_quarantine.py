#!/usr/bin/env python3
"""Fail closed if canonical compiler paths reference quarantined manual specs.

Issue #999 keeps legacy/manual specs available for compatibility and proof migration,
but canonical compile/lowering/gas/CLI paths must not depend on manual `*Spec`
artifacts (except explicit compatibility allowlist entries).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

CANONICAL_FILES = [
    ROOT / "Compiler" / "CompileDriver.lean",
    ROOT / "Compiler" / "Gas" / "Report.lean",
    ROOT / "Compiler" / "Lowering" / "FromEDSL.lean",
    ROOT / "Compiler" / "Main.lean",
    ROOT / "Compiler" / "MainTest.lean",
]

ALLOWED_QUALIFIED_SPEC_REFERENCES = {
    "Compiler.Specs.cryptoHashSpec",
    "Specs.cryptoHashSpec",
}

QUALIFIED_SPEC_RE = re.compile(
    r"\b(?P<qual>(?:Compiler\.)?Specs\.(?P<name>[A-Za-z_][A-Za-z0-9_']*Spec))\b"
)


def _strip_lean_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    in_string = False
    raw_hashes: int | None = None

    while i < n:
        ch = text[i]

        if raw_hashes is not None:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == '"':
                j = i + 1
                hashes = 0
                while j < n and text[j] == "#" and hashes < raw_hashes:
                    hashes += 1
                    j += 1
                if hashes == raw_hashes:
                    out.append('"')
                    out.extend("#" * hashes)
                    i = j
                    raw_hashes = None
                    continue
            out.append(" ")
            i += 1
            continue

        if in_string:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
                continue
            if ch == '"':
                out.append('"')
                in_string = False
                i += 1
                continue
            out.append(" ")
            i += 1
            continue

        if ch == '"':
            out.append('"')
            in_string = True
            i += 1
            continue

        if ch == "r":
            j = i + 1
            hashes = 0
            while j < n and text[j] == "#":
                hashes += 1
                j += 1
            if j < n and text[j] == '"':
                out.append("r")
                out.extend("#" * hashes)
                out.append('"')
                i = j + 1
                raw_hashes = hashes
                continue

        out.append(ch)
        i += 1

    return "".join(out)


def scrub_lean_code(text: str) -> str:
    return _strip_lean_strings(strip_lean_comments(text))


def find_disallowed_references(content: str) -> list[str]:
    disallowed: list[str] = []
    for match in QUALIFIED_SPEC_RE.finditer(content):
        qualified = match.group("qual")
        if qualified in ALLOWED_QUALIFIED_SPEC_REFERENCES:
            continue
        disallowed.append(qualified)
    return disallowed


def main() -> int:
    errors: list[str] = []
    for path in CANONICAL_FILES:
        if not path.exists():
            errors.append(f"Missing canonical file: {path.relative_to(ROOT)}")
            continue
        scrubbed = scrub_lean_code(path.read_text(encoding="utf-8"))
        bad = sorted(set(find_disallowed_references(scrubbed)))
        if bad:
            rel = path.relative_to(ROOT)
            errors.append(
                f"{rel}: found quarantined manual spec reference(s): {', '.join(bad)}"
            )

    if errors:
        print("Manual-spec quarantine check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        print(
            "\nCanonical compiler paths must not reference manual Compiler.Specs.*Spec symbols. "
            "Route canonical flows through generated EDSL contracts and Specs.allSpecs.",
            file=sys.stderr,
        )
        return 1

    print(
        "Manual-spec quarantine check passed "
        f"({len(CANONICAL_FILES)} canonical files; only allowlisted compatibility specs used)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
