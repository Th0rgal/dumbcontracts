#!/usr/bin/env python3
"""Fail closed when active object rewrite rules lack proof metadata.

Issue #1150 acceptance slice (object rule type):
- Active object rules in shipped rewrite bundles must declare non-empty `proofId`.
- `proofId` may be a string literal or a String def alias.
- CI fails if metadata is missing/empty/unresolvable.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, report_errors, strip_lean_comments

PATCH_RULES_PATH = ROOT / "Compiler" / "Yul" / "PatchRules.lean"
BUNDLES_TO_CHECK = ["foundationRewriteBundle", "solcCompatRewriteBundle"]

_DEF_OBJECT_RULE_RE = re.compile(r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*ObjectPatchRule\s*:=\s*\{")
_DEF_STRING_RE = re.compile(r'^\s*def\s+([A-Za-z_][A-Za-z0-9_\']*)\s*:\s*String\s*:=\s*"([^"]*)"', re.MULTILINE)
_DEF_OBJECT_PACK_RE = re.compile(
    r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*List\s+ObjectPatchRule\s*:=",
    re.MULTILINE,
)


def _find_matching_delim(text: str, start: int, open_ch: str, close_ch: str) -> int:
    depth = 0
    i = start
    in_string = False
    escape = False
    while i < len(text):
        ch = text[i]
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError(f"Unbalanced delimiters: missing {close_ch!r} for {open_ch!r} at index {start}")


def _extract_object_rule_proof_tokens(text: str) -> dict[str, str]:
    rules: dict[str, str] = {}
    for match in _DEF_OBJECT_RULE_RE.finditer(text):
        rule_name = match.group(1)
        open_brace = text.find("{", match.end() - 1)
        if open_brace < 0:
            raise ValueError(f"Could not locate opening '{{' for object rule {rule_name}")
        close_brace = _find_matching_delim(text, open_brace, "{", "}")
        block = text[open_brace : close_brace + 1]
        proof_match = re.search(r"\bproofId\s*:=\s*([^,\n]+)", block)
        if proof_match is None:
            rules[rule_name] = ""
            continue
        rules[rule_name] = proof_match.group(1).strip()
    return rules


def _extract_string_defs(text: str) -> dict[str, str]:
    return {name: value for name, value in _DEF_STRING_RE.findall(text)}


def _extract_bundle_block(text: str, bundle_name: str) -> str:
    start_match = re.search(
        rf"\bdef\s+{re.escape(bundle_name)}\s*:\s*RewriteRuleBundle\s*:=\s*\{{",
        text,
    )
    if start_match is None:
        raise ValueError(f"Missing bundle definition: {bundle_name}")
    open_brace = text.find("{", start_match.end() - 1)
    if open_brace < 0:
        raise ValueError(f"Could not locate opening '{{' for bundle {bundle_name}")
    close_brace = _find_matching_delim(text, open_brace, "{", "}")
    return text[open_brace : close_brace + 1]


def _split_top_level_concat(expr: str) -> list[str]:
    parts: list[str] = []
    depth_round = 0
    depth_square = 0
    depth_curly = 0
    in_string = False
    escape = False
    start = 0
    i = 0
    while i < len(expr):
        ch = expr[i]
        nxt = expr[i + 1] if i + 1 < len(expr) else ""
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == "(":
            depth_round += 1
        elif ch == ")":
            depth_round = max(0, depth_round - 1)
        elif ch == "[":
            depth_square += 1
        elif ch == "]":
            depth_square = max(0, depth_square - 1)
        elif ch == "{":
            depth_curly += 1
        elif ch == "}":
            depth_curly = max(0, depth_curly - 1)
        elif (
            ch == "+"
            and nxt == "+"
            and depth_round == 0
            and depth_square == 0
            and depth_curly == 0
        ):
            parts.append(expr[start:i].strip())
            i += 2
            start = i
            continue
        i += 1
    tail = expr[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def _extract_object_pack_defs(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for match in _DEF_OBJECT_PACK_RE.finditer(text):
        name = match.group(1)
        pos = match.end()
        while pos < len(text) and text[pos].isspace():
            pos += 1
        if pos >= len(text):
            raise ValueError(f"Missing value expression for object pack {name}")
        if text[pos] == "[":
            end = _find_matching_delim(text, pos, "[", "]")
            out[name] = text[pos : end + 1].strip()
        else:
            line_end = text.find("\n", pos)
            if line_end == -1:
                line_end = len(text)
            out[name] = text[pos:line_end].strip()
    return out


def _extract_object_rules_from_expression(
    expr: str,
    object_packs: dict[str, str],
    *,
    stack: set[str] | None = None,
) -> list[str]:
    names: list[str] = []
    stack = set() if stack is None else stack
    for part in _split_top_level_concat(expr):
        if part.startswith("[") and part.endswith("]"):
            names.extend(re.findall(r"\b([A-Za-z_][A-Za-z0-9_']*)\b", part[1:-1]))
            continue
        ident_match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_']*)", part)
        if ident_match is None:
            raise ValueError(f"Unsupported objectRules expression segment: {part!r}")
        ident = ident_match.group(1)
        if ident in object_packs:
            if ident in stack:
                raise ValueError(f"Cyclic object pack definition: {ident}")
            nested = _extract_object_rules_from_expression(
                object_packs[ident], object_packs, stack=stack | {ident}
            )
            names.extend(nested)
        else:
            names.append(ident)
    return names


def _extract_object_rules_from_bundle(bundle_block: str, object_packs: dict[str, str]) -> list[str]:
    field_match = re.search(r"\bobjectRules\s*:=", bundle_block)
    if field_match is None:
        raise ValueError("Bundle block missing objectRules field")
    expr = bundle_block[field_match.end() :].rsplit("}", 1)[0].strip()
    return _extract_object_rules_from_expression(expr, object_packs)


def _resolve_proof_ref(token: str, string_defs: dict[str, str]) -> str:
    token = token.strip()
    if token.startswith('"') and token.endswith('"') and len(token) >= 2:
        return token[1:-1]
    return string_defs.get(token, "")


def check_active_object_rule_proofs(path: Path) -> list[str]:
    if not path.exists():
        raise ValueError(f"Missing PatchRules file: {path}")

    text = strip_lean_comments(path.read_text(encoding="utf-8"))
    object_rule_tokens = _extract_object_rule_proof_tokens(text)
    string_defs = _extract_string_defs(text)
    object_packs = _extract_object_pack_defs(text)

    errors: list[str] = []
    for bundle_name in BUNDLES_TO_CHECK:
        bundle_block = _extract_bundle_block(text, bundle_name)
        active_rules = _extract_object_rules_from_bundle(bundle_block, object_packs)
        for rule_name in active_rules:
            if rule_name not in object_rule_tokens:
                errors.append(
                    f"{bundle_name}: objectRules entry {rule_name!r} is not defined as ObjectPatchRule"
                )
                continue
            token = object_rule_tokens[rule_name]
            if not token:
                errors.append(f"{bundle_name}: {rule_name} missing proofId field")
                continue
            proof_ref = _resolve_proof_ref(token, string_defs)
            if not proof_ref:
                errors.append(
                    f"{bundle_name}: {rule_name} has unresolved or empty proofId token {token!r}"
                )

    return errors


def main() -> int:
    try:
        errors = check_active_object_rule_proofs(PATCH_RULES_PATH)
    except ValueError as exc:
        print(f"Rewrite proof metadata check failed: {exc}", file=sys.stderr)
        return 1

    report_errors(errors, "Rewrite proof metadata check failed")
    print("Rewrite proof metadata check passed (active object rewrite rules have non-empty proof refs).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
