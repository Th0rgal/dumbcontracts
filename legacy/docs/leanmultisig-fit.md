# leanMultisig fit with dumb contracts

## What leanMultisig is (from the repo docs)

leanMultisig presents a **minimal, hash-focused zkVM** aimed at post-quantum Ethereum by
supporting hash-based signature aggregation and recursion. The repo includes a design PDF
(`minimal_zkVM.pdf`) describing a lean instruction set (ADD/MUL/DEREF/JUMP), read-only memory,
and a proving stack built around WHIR + SuperSpartan + logup, inspired by Cairo.

Key characteristics in the VM spec:

- **Read-only memory** with a public-input prefix for program arguments.
- **Small ISA** with arithmetic constraints: `a + c = b` and `a * c = b`.
- **Conditional jumps** and a `DEREF` operator for indirect memory checks.
- **Precompiles** for Poseidon2 and dot-product operations.
- **Range checks** implemented via a `DEREF` trick (useful for unsigned bounds).

This is explicitly optimized for hash-heavy proof workloads (e.g., XMSS aggregation) and recursion.

## How it fits the dumb-contract goal

Our goal is to make contracts "dumb": write specs, and let implementations be supplied
as offchain computations accompanied by proofs. A minimal zkVM fits as the **checker runtime**
that verifies a proposed state transition (diff) satisfies the spec.

- The VM is the **proof engine**, not a full execution engine.
- The spec is the **source of truth** and compiles to a checker program.
- The implementation is just a witness + diff validated by the checker.

In this framing, the VM's ISA effectively *is* a DSL for provable correctness: it encodes
just enough operations (hashing, arithmetic, jumps, memory reads) to check rules.
That aligns with "one VM, one DSL" if the DSL stays spec-centric and compiles to checker logic.

## Implications and tradeoffs

- **Strengths**: Minimal ISA, hash-first proving, and recursion are a strong match for
  proof-oriented state transition checks.
- **Limits**: The VM is specialized; we should treat it as a verification backend,
  not a drop-in replacement for the full EVM execution model.
- **Design requirement**: The DSL should avoid full imperative logic and instead express
  constraints and invariants that are efficient to check.

## Concrete bridge (in this repo)

A concrete sketch lives in `research/leanmultisig_bridge/`:

- `specs/simple_token.dc` is the DSL spec.
- `leanisa/transfer_check.leanisa` is a leanISA-style checker using ADD/MUL constraints
  and inverse witnesses for non-zero checks.

This shows a realistic **spec -> checker -> proof** pipeline while keeping the DSL intact.

## Next steps to make it real

- Lock a canonical **public-input layout** for diffs and witnesses.
- Define a **Lean spec IR -> leanISA** compiler that emits actual instruction encodings.
- Use Poseidon2 precompile for hashing state commitments if we move to sparse state models.
