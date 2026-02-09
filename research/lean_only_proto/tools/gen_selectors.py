#!/usr/bin/env python3
import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path

def parse_signatures(text: str):
    sigs = {}
    # Match comment lines like: -- getSlot(uint256) -> 0x7eba7ba6
    pattern = re.compile(r"--\s*([A-Za-z0-9_]+\([^)]*\))\s*->\s*(0x[0-9a-fA-F]+)")
    for m in pattern.finditer(text):
        signature = m.group(1)
        name = signature.split("(", 1)[0]
        sigs[name] = signature
    return sigs


def parse_entrypoints(text: str):
    entries = []
    # Match blocks like: def name : EntryPoint := { ... }
    pattern = re.compile(r"def\s+(\w+)\s*:\s*EntryPoint\s*:=\s*\{([\s\S]*?)\}", re.MULTILINE)
    sigs = parse_signatures(text)
    for m in pattern.finditer(text):
        def_name = m.group(1)
        block = m.group(2)
        name_m = re.search(r'name\s*:=\s*"([^"]+)"', block)
        selector_m = re.search(r'selector\s*:=\s*(0x[0-9a-fA-F]+)', block)
        args_m = re.search(r'args\s*:=\s*\[(.*?)\]', block, re.DOTALL)
        returns_m = re.search(r'returns\s*:=\s*(true|false)', block)
        if not name_m or not selector_m:
            continue
        args = []
        if args_m:
            args = re.findall(r'"([^"]+)"', args_m.group(1))
        returns = returns_m.group(1) == "true" if returns_m else False
        name = name_m.group(1)
        entries.append({
            "def": def_name,
            "name": name,
            "selector": selector_m.group(1).lower(),
            "args": args,
            "returns": returns,
            "signature": sigs.get(name),
        })
    return entries


def cast_keccak(signature: str):
    if not signature:
        return None
    if not shutil.which("cast"):
        return None
    try:
        out = subprocess.check_output(["cast", "keccak", signature], text=True).strip()
        if not out.startswith("0x"):
            return None
        return out
    except Exception:
        return None


def enrich_with_abi(entries):
    for e in entries:
        keccak = cast_keccak(e.get("signature"))
        if keccak:
            abi_selector = "0x" + keccak[2:10]
            e["abi_selector"] = abi_selector
            e["abi_selector_match"] = (abi_selector.lower() == e["selector"].lower())
            e["abi_selector_source"] = "cast keccak"
        else:
            e["abi_selector"] = None
            e["abi_selector_match"] = None
            e["abi_selector_source"] = None
    return entries


def render_markdown(entries):
    lines = [
        "# Selector Map",
        "",
        "This file is generated from `DumbContracts/Compiler.lean`.",
        "",
        "If `cast` is available, ABI selectors are derived from the signature",
        "comments in `Compiler.lean` (e.g., `name(type,...)`).",
        "",
        "| Function | Signature | Fixed Selector | ABI Selector | Args | Returns |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for e in entries:
        args = ", ".join(e["args"]) if e["args"] else "(none)"
        returns = "yes" if e["returns"] else "no"
        signature = e.get("signature") or "(unknown)"
        abi_selector = e.get("abi_selector") or "(unavailable)"
        lines.append(
            f"| `{e['name']}` | `{signature}` | `{e['selector']}` | `{abi_selector}` | {args} | {returns} |"
        )
    lines.append("")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="input_path", required=True)
    ap.add_argument("--json", dest="json_path", required=True)
    ap.add_argument("--md", dest="md_path", required=True)
    args = ap.parse_args()

    text = Path(args.input_path).read_text(encoding="utf-8")
    entries = enrich_with_abi(parse_entrypoints(text))

    out_json = {
        "source": "DumbContracts/Compiler.lean",
        "entries": entries,
    }

    Path(args.json_path).write_text(json.dumps(out_json, indent=2) + "\n", encoding="utf-8")
    Path(args.md_path).write_text(render_markdown(entries), encoding="utf-8")


if __name__ == "__main__":
    main()
