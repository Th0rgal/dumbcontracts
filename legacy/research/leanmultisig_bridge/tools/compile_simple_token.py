#!/usr/bin/env python3
"""POC compiler: dumb-contract DSL -> leanISA-style checker skeleton.

This is intentionally narrow: it recognizes the simple_token Transfer spec
and emits a fixed checker layout that mirrors the spec rules.
"""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SPEC_DEFAULT = ROOT / "specs" / "simple_token.dc"
OUT_DEFAULT = ROOT / "out" / "transfer_check.leanisa"

TEMPLATE = """; GENERATED FILE - POC compiler output
; Source spec: {spec_name}
;
; leanISA-style checker program for Transfer spec
; This is a *checker* (not an implementation). The trace exists iff the diff satisfies the spec.
;
; ISA primitives from minimal_zkVM.pdf:
;   ADD:  a + c = b
;   MUL:  a * c = b
;   DEREF / JUMP exist but are omitted in this macro listing.
;
; Memory layout (public input region, read-only). fp points at index 0.
;  0  old_total_supply
;  1  new_total_supply
;  2  from
;  3  to
;  4  amount
;  5  old_balance_from
;  6  old_balance_to
;  7  new_balance_from
;  8  new_balance_to
;  9  sum_old_balances
;  10 sum_new_balances
;  11 witness_count
;  12 inv_to                      ; witness: inverse(to) to prove to != 0
;  13 const_one                   ; must be 1
;  14 witness_base                ; start of witness table
;
; Each witness entry i occupies 5 cells starting at witness_base + 5*i:
;  0 addr
;  1 old_balance
;  2 new_balance
;  3 diff_from                    ; addr - from (witnessed)
;  4 diff_to                      ; addr - to   (witnessed)
; Plus two global witness arrays (same indexing):
;  inv_diff_from[i], inv_diff_to[i] stored after the table (not shown here)
;
; -----------------------------------------------------------------------------
; 1) require: to != 0
; Prove nonzero via inverse witness: to * inv_to = 1
MUL a=fp+3  c=fp+12 -> b=fp+13

; 2) ensure: balance[from] == old(balance[from]) - amount
; Equivalent: old_balance_from = new_balance_from + amount
ADD a=fp+7  c=fp+4  -> b=fp+5

; 3) ensure: balance[to] == old(balance[to]) + amount
ADD a=fp+6  c=fp+4  -> b=fp+8

; 4) invariant: NonNegativeBalances (range checks on new balances)
; Use the range-check macro from minimal_zkVM.pdf to enforce 0 <= x < 2^t.
; RANGE_CHECK(fp+7, t)  ; new_balance_from
; RANGE_CHECK(fp+8, t)  ; new_balance_to

; 5) invariant: SupplyConservation
; sum_new_balances == new_total_supply, sum_old_balances == old_total_supply
ADD a=fp+10 c=imm(0) -> b=fp+1
ADD a=fp+9  c=imm(0) -> b=fp+0
ADD a=fp+10 c=imm(0) -> b=fp+9

; 6) forall addr != from && addr != to: balance[addr] unchanged
; For each witness entry i:
;   - addr = from + diff_from
;   - addr = to   + diff_to
;   - diff_from * inv_diff_from = 1
;   - diff_to   * inv_diff_to   = 1
;   - new_balance = old_balance
; Loop compiled via recursion in leanISA (see minimal_zkVM.pdf).

; pseudo (per entry i):
; ADD a=fp+w_addr   c=imm(0) -> b=fp+w_addr        ; keep addr in place
; ADD a=fp+2        c=fp+w_diff_from -> b=fp+w_addr
; ADD a=fp+3        c=fp+w_diff_to   -> b=fp+w_addr
; MUL a=fp+w_diff_from c=fp+inv_diff_from[i] -> b=fp+13
; MUL a=fp+w_diff_to   c=fp+inv_diff_to[i]   -> b=fp+13
; ADD a=fp+w_old   c=imm(0) -> b=fp+w_new

; If all constraints are satisfied, the trace is valid and the checker "accepts".
"""


def main() -> int:
    spec_path = Path(sys.argv[1]) if len(sys.argv) > 1 else SPEC_DEFAULT
    out_path = Path(sys.argv[2]) if len(sys.argv) > 2 else OUT_DEFAULT

    spec_text = spec_path.read_text(encoding="utf-8")
    if "spec Transfer" not in spec_text or "SupplyConservation" not in spec_text:
        raise SystemExit(
            "POC compiler only supports the simple_token Transfer spec right now."
        )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        TEMPLATE.format(spec_name=spec_path.name), encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
