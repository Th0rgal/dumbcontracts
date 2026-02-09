# leanMultisig bridge sketch

This folder is a **concrete bridge sketch** showing how a dumb-contract spec could compile into
leanMultisig's minimal zkVM ("leanISA") as a *checker* program rather than a full implementation.

We keep the DSL identical to our existing spec style and compile it into a zkVM program that
verifies a proposed state transition (diff) against the spec. A prover supplies the witness (the
post-state and any quantifier witnesses) and produces a proof that the checker program accepts.

## Files

- `specs/simple_token.dc`: the spec DSL input (same structure as our current DSL examples)
- `leanisa/transfer_check.leanisa`: a leanISA-style checker that uses ADD/MUL constraints
  and inverse witnesses for non-zero checks
- `tools/compile_simple_token.py`: a tiny POC compiler that emits a checker skeleton
- `out/transfer_check.leanisa`: generated output from the POC compiler

## Spec -> checker -> proof

1. **Spec** (rules only)
   - The spec owns variables like `balance` and `totalSupply`.
   - It has `require` and `ensure` clauses plus invariants.

2. **Implementation** (offchain)
   - An offchain executor computes a *diff*:
     - `old_balance_from`, `new_balance_from`, etc.
     - Witnesses for the `forall` clause (addresses + old/new balances).
     - Inverse witnesses for non-zero checks, e.g. `inv_to` so `to * inv_to = 1`.
   - This is the "implementation logic" that is *not* baked into the contract.

3. **Checker program** (leanISA)
   - A minimal program validates the diff against the spec using only
     arithmetic and memory reads:
     - `ADD` enforces equalities (e.g., `old = new + amount`).
     - `MUL` enforces non-zero via inverse witnesses.
     - Range-checks are enforced with the `DEREF` trick described in the VM spec.
   - This is what gets proven in the zkVM.

4. **Proof + Onchain verify**
   - The verifier checks a proof that the checker accepted the diff.
   - The contract stores the resulting state updates (or accepts the diff).

## Why this reuses the DSL

- The same spec syntax (invariants + per-call ensures) can target:
  - our existing Lean -> Yul compiler path, or
  - a leanISA checker program for zk proof generation.
- The DSL stays stable; only the backend changes.

## What is *not* implemented yet

This is a sketch. It does **not** encode the checker into the real leanISA binary format,
nor does it generate actual proofs. It is a concrete shape for the pipeline and memory layout
needed to bridge the DSL to a minimal zkVM.

## POC compiler usage

This is a narrow, demo-only compiler for the simple token spec:

```bash
./tools/compile_simple_token.py
```

The generated file lands at `out/transfer_check.leanisa`.
