# Audit Guide

This is the first file to read before auditing Verity. If you want full formal details after this quick pass, read [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) and [AXIOMS.md](AXIOMS.md).

## Start Here: What Verity Is

Think of Verity as two roads that both end in EVM bytecode:

1. `EDSL -> ContractSpec -> IR -> Yul -> solc -> bytecode` (the formally verified road)
2. `Unified AST (--ast) -> Yul -> solc -> bytecode` (the migration road, not fully proven end-to-end)

The first road is where the formal guarantees live.
The second road is useful and tested, but still relies on testing rather than full proof equivalence.

## Mental Model (Simple)

If you are new to compiler audits, use this model:

- Layer 1: "Did the Lean contract code match the stated contract behavior?" Yes, proven.
- Layer 2: "Did compiler lowering to IR keep that behavior?" Yes, proven.
- Layer 3: "Did IR lowering to Yul keep that behavior?" Yes, proven, with one documented axiom.
- Final step: "Did solc compile Yul correctly?" Trusted external compiler (pinned version).

That is the core trust boundary story.

## Current Architecture (What Exists Today)

### Verified path (`ContractSpec` path)

- `Verity/` contains EDSL contracts and proofs.
- `Compiler/ContractSpec.lean` validates and compiles specs.
- `Compiler/Codegen.lean` lowers IR to Yul AST.
- `Compiler/Yul/PrettyPrint.lean` renders Yul text.
- `solc` compiles Yul to bytecode.

### AST path (`--ast` flag)

- `Verity/AST.lean` defines the unified AST.
- `Compiler/ASTCompile.lean` translates AST statements to Yul statements.
- `Compiler/ASTDriver.lean` orchestrates AST compilation and ABI generation.

Important status:

- The AST path is available and tested.
- It now supports mutability metadata (`isPayable`, `isView`, `isPure`) in specs/ABI.
- It is still not fully covered by the Layer 2/3 proof chain used by `ContractSpec`.

## Key Files Auditors Should Read

- `Compiler/ContractSpec.lean`: compile-time validation and core lowering logic.
- `Compiler/Selector.lean` and `Compiler/Selectors.lean`: selector generation and selector axiom surface.
- `Compiler/Linker.lean`: external Yul library injection (outside proof boundary).
- `Compiler/ASTDriver.lean` and `Compiler/ASTCompile.lean`: AST pipeline.
- `Verity/Core.lean`: execution model and semantics assumptions.
- `scripts/check_yul_compiles.py`: compile and drift checks.
- `scripts/check_selectors.py`: selector and constant consistency checks.
- `scripts/check_doc_counts.py`: documentation metric consistency.

## Trust Boundaries (Plain Language)

1. `solc` is trusted.
2. Keccak selector hashing has one explicit axiom, continuously cross-checked in CI.
3. External linked Yul libraries are trusted for semantics (only interface-level checks are enforced).
4. Mapping slot collision freedom relies on the standard Ethereum keccak assumption.
5. Gas is not formally modeled in proof semantics.

## Main Risks to Review

1. Revert-state modeling gap in high-level semantics: verify checks-before-effects discipline in contracts.
2. External library linkage: audit linked Yul code as separate critical code.
3. Wrapping arithmetic semantics: verify intentionality or explicit guards where checked behavior is expected.
4. AST-vs-ContractSpec drift: watch the allowlist-backed diffs and require explicit review for any new drift.

## Quick Auditor Checklist

1. Confirm target contract compiles through `ContractSpec` path unless AST path is explicitly required.
2. Read `AXIOMS.md` and verify current axiom list is minimal and justified.
3. Read `TRUST_ASSUMPTIONS.md` and confirm all trust boundaries in your deployment are acceptable.
4. Run CI scripts for selectors, Yul compileability, storage layout, and doc consistency.
5. If libraries are linked, audit them separately and treat as part of TCB.

## How To Keep This Easy and Pleasant (Suggestions)

1. Keep one page, one job: this file is orientation, not exhaustive proof detail.
2. Use short "story" headings ("Where trust enters", "What can go wrong", "What to check first").
3. Prefer concrete examples over abstract labels (show one real file per boundary).
4. Keep numbers script-backed only; avoid hand-maintained metrics unless `check_doc_counts.py` enforces them.
5. Every architecture change should update this file in the same PR so auditors never read stale boundaries.
