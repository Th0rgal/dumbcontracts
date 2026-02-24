# AUDIT

## Architecture & trust boundaries

Components and flow:
1. `Verity/*` EDSL contracts and logical specs (`Prop`).
2. `Compiler/ContractSpec.lean` validates and lowers `ContractSpec` to IR.
3. `Compiler/Codegen.lean` lowers IR to Yul AST.
4. `Compiler/Yul/PrettyPrint.lean` renders Yul text.
5. `solc` compiles Yul to EVM bytecode.
6. Optional migration path: `Verity/AST.lean` + `Compiler/ASTCompile.lean` + `Compiler/ASTDriver.lean` (`--ast`).

Trust changes:
1. Lean proofs stop at generated Yul; `solc` correctness is trusted.
2. Selector hashing includes a documented keccak axiom (see `AXIOMS.md`).
3. Linked external Yul libraries are trusted TCB code.
4. CI scripts consume repo/workspace files as untrusted input and must validate format before use.

## Security model

Threat assumptions:
1. Adversary may submit malformed source/contracts/docs/artifacts through PRs.
2. CI runners execute checks on attacker-controlled branch contents.
3. Deployers choose whether to use proof-backed path (ContractSpec) or migration path (AST).

Access control and checks:
1. Solidity runtime access control is contract-specific and tested in Foundry suites under `test/`.
2. Build/verification gate is deny-by-default: CI fails on invariant drift (selectors, storage layout, docs/proof counts, property coverage, warning regressions).
3. `scripts/workflow_jobs.py` centralizes top-level `jobs:` parsing (quoted and unquoted keys) for workflow-sync checkers, so cross-job boundary extraction is explicit and shared.
4. `scripts/check_lean_warning_regression.py` validates baseline schema/invariants and fails on mismatch. Uses `type(value) is not int` to reject booleans, raises `ValueError` on malformed UTF-8 log input, and validates `by_file`/`by_message` counter fields strictly.
5. `scripts/check_doc_counts.py` uses `_expect_int` with `type(value) is not int` to reject booleans in integer metric fields.
6. `scripts/check_verify_artifact_sync.py` uses step-level `with:` block parsing that is key-order independent.
7. `scripts/check_verify_checks_docs_sync.py` uses `extract_run_commands_from_job_body` which handles both single-line and multiline `run: |` commands.
8. `scripts/check_verify_foundry_patched_sync.py` uses `extract_literal_from_mapping_blocks` to scope `DIFFTEST_*` extraction to `env:` blocks only.
9. `scripts/check_verify_foundry_job_sync.py` uses `extract_literal_from_mapping_blocks` to scope `FOUNDRY_PROFILE`/`DIFFTEST_*` extraction to `env:` blocks only.
10. `scripts/check_verify_foundry_shard_sync.py` uses `extract_literal_from_mapping_blocks` to scope `DIFFTEST_SHARD_COUNT`/`DIFFTEST_RANDOM_SEED` extraction to `env:` blocks only.
11. `scripts/check_verify_foundry_gas_calibration_sync.py` uses step-scoped parsing for `FOUNDRY_PROFILE` and artifact names.
12. `scripts/check_verify_multiseed_sync.py` scopes seed extraction to `strategy.matrix.seed`.
13. `scripts/check_verify_paths_sync.py` scopes path-filter extraction to `jobs.changes`.
14. `scripts/check_interop_matrix_sync.py` detects duplicate normalized feature rows with explicit error reporting.
15. `scripts/check_builtin_list_sync.py` strips Lean comments before `def` extraction, preventing comment-decoy bypass.
16. `scripts/check_solc_pin.py` collects all `SOLC_*` matches via `finditer` and fails on conflicting values across occurrences.
17. `scripts/check_yul_builtin_boundary.py` uses `scrub_lean_code` to strip comments and string literals before boundary checks.
18. `scripts/check_mapping_slot_boundary.py` uses `scrub_lean_code` to strip comments and string literals before boundary checks.
19. `scripts/check_evmyullean_capability_boundary.py` detects non-literal builtin dispatch patterns and reports them as fail-closed diagnostics.

Crypto choices:
1. Function selectors use keccak256 (Ethereum ABI standard interoperability requirement).
2. Mapping slot addressing follows standard keccak-based EVM storage scheme.
3. No custom cryptography is introduced in this repo.

## Design decisions

1. Keep both compiler front-ends (`ContractSpec` and AST) to get differential signals during migration instead of a single failure channel.
2. Use many small explicit CI check scripts rather than one opaque mega-check; each guard maps to one invariant and one failure reason.
3. Keep warning-regression baseline as checked JSON artifact for deterministic CI behavior; validate schema strictly to avoid silent acceptance of malformed data.
4. Prefer generated artifacts and sync checks over handwritten counts/metadata to reduce review-time ambiguity.

## Known risks

1. `solc` is trusted and outside Lean proof scope.
2. AST path is implemented/tested but not yet in the same end-to-end proof chain as ContractSpec path.
3. Linked external Yul libraries remain trusted dependencies and must be audited separately.
4. Gas bounds are engineering checks, not semantic security proofs.

## External dependencies

1. `solc`: trusted compiler from Yul to EVM bytecode.
2. Foundry (`forge`/`anvil` tooling): trusted test harness/runtime for Solidity tests.
3. Lean toolchain (`lake`, Lean compiler): trusted proof checker and build runtime.
4. Python 3 standard library scripts: trusted CI execution environment; scripts validate untrusted file inputs where used.

## Attack surface

External input entry points:
1. CLI/compiler inputs and contract sources (`Verity/*`, `Compiler/*`).
2. Foundry test inputs, calldata/value fuzzing, and FFI-enabled differential/property test harnesses (`test/*`).
3. CI/workflow-consumed files and generated artifacts (`artifacts/*.json`, docs tables, manifests, gas reports, logs).
4. Newly hardened boundary: `artifacts/lean_warning_baseline.json` consumed by `scripts/check_lean_warning_regression.py`.

Primary review focus:
1. Selector/ABI drift (`Compiler/Selector.lean`, `Compiler/Selectors.lean`, `scripts/check_selectors.py`).
2. Storage slot/type drift across layers (`scripts/check_storage_layout.py`).
3. Cross-path output drift and Yul compileability (`scripts/check_yul_compiles.py`).
4. Contract access-control/property behavior (`test/Property*.t.sol`, `test/Differential*.t.sol`).
