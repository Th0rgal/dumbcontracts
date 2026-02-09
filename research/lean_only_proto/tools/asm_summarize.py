#!/usr/bin/env python3
import collections
import pathlib
import sys

def normalize_hex(hex_token: str) -> str:
    h = hex_token[2:]
    if len(h) % 2 == 1:
        h = "0" + h
    return h

def summarize(asm_text: str):
    op_counts = collections.Counter()
    push_counts = collections.Counter()
    labels = []
    total_ops = 0

    for raw in asm_text.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("======="):
            continue
        if line.startswith("Text representation"):
            continue
        if line.startswith("EVM assembly"):
            continue
        if line.startswith("/*"):
            continue

        if line.startswith("tag_"):
            label = line.rstrip(":")
            labels.append(label)
            continue

        token = line.split()[0]
        if token.startswith("0x"):
            h = normalize_hex(token)
            size = max(1, len(h) // 2)
            op = f"PUSH{size}"
            op_counts[op] += 1
            push_counts[op] += 1
            total_ops += 1
            continue

        op = token.upper()
        op_counts[op] += 1
        total_ops += 1

    unique_ops = len(op_counts)
    unique_labels = len(set(labels))
    return {
        "total_ops": total_ops,
        "unique_ops": unique_ops,
        "op_counts": op_counts,
        "push_counts": push_counts,
        "labels": labels,
        "unique_labels": unique_labels,
    }

def render_summary(summary, source_path: str):
    lines = []
    lines.append("# ASM Summary")
    lines.append("")
    lines.append(f"Source: {source_path}")
    lines.append(f"Total ops: {summary['total_ops']}")
    lines.append(f"Unique ops: {summary['unique_ops']}")
    lines.append(f"Labels: {summary['unique_labels']}")
    lines.append("")

    if summary["labels"]:
        lines.append("Labels (order of appearance):")
        for label in summary["labels"]:
            lines.append(f"- {label}")
        lines.append("")

    if summary["push_counts"]:
        lines.append("PUSH sizes:")
        for op, count in summary["push_counts"].most_common():
            lines.append(f"- {op}: {count}")
        lines.append("")

    lines.append("Opcode counts:")
    for op, count in summary["op_counts"].most_common():
        lines.append(f"- {op}: {count}")

    lines.append("")
    lines.append("Notes:")
    lines.append("- The summary treats hex literals as PUSHn based on byte length.")
    lines.append("- Labels come from tag_ lines emitted by solc's --asm output.")

    return "\n".join(lines) + "\n"


def main(argv):
    if len(argv) < 2 or len(argv) > 3:
        print("Usage: asm_summarize.py <input.asm> [output.summary]", file=sys.stderr)
        return 2

    asm_path = pathlib.Path(argv[1])
    if not asm_path.exists():
        print(f"Missing input: {asm_path}", file=sys.stderr)
        return 2

    summary_path = pathlib.Path(argv[2]) if len(argv) == 3 else asm_path.with_suffix(".asm.summary")

    summary = summarize(asm_path.read_text(encoding="utf-8"))
    summary_path.write_text(render_summary(summary, str(asm_path)), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
