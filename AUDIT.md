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
3. `scripts/workflow_jobs.py` now centralizes top-level `jobs:` parsing (quoted and unquoted keys) for workflow-sync checkers, so cross-job boundary extraction is explicit and shared.
4. `scripts/check_lean_warning_regression.py` validates baseline schema/invariants and fails on mismatch. Current gaps: `by_file`/`by_message` set to `null` may be normalized as empty objects when `total_warnings=0` (issue #858), omitted `by_file`/`by_message` fields are also normalized as empty objects when `total_warnings=0` (issue #862), JSON boolean counter values are accepted as integers due to Python `bool`/`int` subtype behavior (issue #859), JSON boolean scalar fields are accepted for `schema_version`/`total_warnings` (`true == 1`, `false == 0`) due to the same subtype behavior (issue #861), and malformed UTF-8 log bytes are silently replaced during parsing which can suppress warning matching (issue #860).
5. `scripts/check_doc_counts.py` compares an artifact JSON against live metrics but currently accepts JSON booleans in integer metric fields (`bool` subtype of `int`), allowing malformed artifact types to pass in specific `0/1` fields (issue #863).
6. `scripts/check_verify_artifact_sync.py` currently parses artifact names with regexes that require `name:` to be the first `with:` key, so equivalent YAML key reordering can hide uploads/downloads from the sync check (issue #864).
7. `scripts/check_verify_checks_docs_sync.py` currently extracts workflow commands only from single-line `run: python3 scripts/...` entries; multiline `run: |` commands are ignored, so docs/workflow drift can bypass this CI guard in mixed-style jobs (issue #865).
8. `scripts/check_verify_foundry_patched_sync.py` currently extracts required `DIFFTEST_*` values from anywhere in the `foundry-patched` job body instead of only the `env:` block, so lookalike keys under other mappings can make the check pass while runtime env wiring is missing (issue #866).
9. `scripts/check_verify_foundry_job_sync.py` currently extracts required `FOUNDRY_PROFILE`/`DIFFTEST_*` values from anywhere in each foundry job body instead of only each job `env:` block, so lookalike keys under other mappings can make the check pass while runtime env wiring is missing (issue #867).
10. `scripts/check_verify_foundry_shard_sync.py` currently extracts required `DIFFTEST_SHARD_COUNT`/`DIFFTEST_RANDOM_SEED` values from anywhere in the `foundry` job body instead of only the `env:` block, so lookalike keys under other mappings can make the check pass while runtime env wiring is missing (issue #868).
11. `scripts/check_verify_foundry_gas_calibration_sync.py` currently extracts `FOUNDRY_PROFILE` and artifact `with.name` via broad job-body regexes instead of target-step-scoped parsing, so lookalike values in unrelated steps can make the check pass while real calibration wiring is wrong (issue #869).
12. `scripts/check_verify_multiseed_sync.py` currently extracts `seed: [...]` from anywhere in the `foundry-multi-seed` job body instead of enforcing `strategy.matrix.seed`, so unrelated step keys can make the check pass while matrix seed wiring is missing (issue #870).
13. `scripts/check_verify_paths_sync.py` currently extracts `changes.filter.code` with a global regex search over the workflow text instead of scoping to `jobs.changes.steps[*].with.filters.code`, so a decoy `filters: |` block in another job can make the check pass while the real `changes` gate is misconfigured (issue #871).
14. `scripts/check_interop_matrix_sync.py` currently stores parsed rows in dicts keyed by normalized feature label without duplicate-key detection, so multiple rows collapsing to one normalized feature can be silently overwritten and still report synchronization success (issue #872).
15. `scripts/check_builtin_list_sync.py` currently locates `def` targets with an unanchored regex and then scrapes quoted strings from that point, so commented decoy `def yulBuiltins`/`def interopBuiltinCallNames` lines can satisfy the sync check while real definitions diverge (issue #875).
16. `scripts/check_solc_pin.py` currently parses `SOLC_VERSION`/`SOLC_URL`/`SOLC_SHA256` by first global regex match over `verify.yml` instead of enforcing an authoritative scope, so conflicting later job-level `env` overrides can change effective compiler pinning while the checker still reports success (issue #883).
17. `scripts/check_yul_builtin_boundary.py` currently validates required `evalBuiltinCall` usage with a raw substring regex over full file text, so comment-only decoy literals can satisfy the boundary check while real runtime dispatch no longer routes through the centralized builtins module (issue #884).
18. `scripts/check_mapping_slot_boundary.py` currently validates several required mapping-slot boundary symbols/usages via raw substring regex search over full file text, so comment-only decoy literals can satisfy the check while executable mapping-slot wiring is missing (issue #885).
19. `scripts/check_evmyullean_capability_boundary.py` currently relies on `extract_found_builtins` regex extraction of direct `func = "..."` literals, so unsupported builtin behavior expressed via indirection (for example `let op := "create"; if func = op then ...`) can evade detection and still report boundary enforcement success (issue #886).

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
5. Lean warning baseline checker currently accepts malformed baseline data in four cases (`null` objects in a specific shape, issue #858; omitted counter objects in a specific shape, issue #862; boolean counter values, issue #859; boolean scalar fields for `schema_version`/`total_warnings`, issue #861), and the log parser currently decodes with replacement on malformed UTF-8 (issue #860); all are tracked for fail-closed remediation.
6. Documentation-count checker currently accepts malformed boolean types in some artifact integer fields (issue #863), so type-level schema guarantees are not yet fail-closed at that boundary.
7. Verify artifact sync checker can miss real upload/download artifact names when workflow `with:` keys are reordered (issue #864), leaving a parser-level bypass in that CI guard.
8. Verify checks/docs sync checker can ignore multiline `run: |` script commands (issue #865), leaving a parser-level bypass where some workflow checks are not enforced against documentation.
9. Verify foundry-patched sync checker can accept `DIFFTEST_*` literals outside the job `env:` block (issue #866), leaving a parser-level bypass that can hide missing runtime env configuration.
10. Verify foundry-job sync checker can accept `FOUNDRY_PROFILE`/`DIFFTEST_*` literals outside each job `env:` block (issue #867), leaving a parser-level bypass that can hide missing runtime env configuration.
11. Verify foundry-shard sync checker can accept `DIFFTEST_SHARD_COUNT`/`DIFFTEST_RANDOM_SEED` literals outside the job `env:` block (issue #868), leaving a parser-level bypass that can hide missing runtime env configuration.
12. Verify foundry-gas-calibration sync checker can accept `FOUNDRY_PROFILE` and artifact name values sourced from unrelated steps in the same job body (issue #869), leaving a parser-level bypass that can hide incorrect runtime calibration wiring.
13. Verify multi-seed sync checker can accept `seed: [...]` values sourced outside `strategy.matrix.seed` (issue #870), leaving a parser-level bypass that can hide missing workflow matrix seed wiring.
14. Verify path-sync checker can accept `changes.filter.code` data from a decoy block outside `jobs.changes` (issue #871), leaving a parser-level bypass that can hide a misconfigured real path-filter gate.
15. Interop matrix sync checker can silently collapse duplicate normalized feature rows due to dict key overwrite without duplicate detection (issue #872), leaving an ambiguity bypass in docs status reporting.
16. Builtin-list sync checker can parse decoy commented definitions instead of real Lean definitions (issue #875), leaving a parser-level bypass where opcode allowlist/denylist drift can be hidden from CI.
17. Solc pin checker can validate only the first global `SOLC_*` assignments in `verify.yml` and miss conflicting later job-level overrides (issue #883), leaving a parser-level bypass where compiler-pin consistency can appear enforced while effective CI job pinning diverges.
18. Yul builtin boundary checker can accept comment-only `Compiler.Proofs.YulGeneration.evalBuiltinCall` literals as proof of required runtime dispatch wiring (issue #884), leaving a parser-level bypass where builtin semantics centralization can drift without CI failure.
19. Mapping-slot boundary checker can accept comment-only marker literals for required backend/function/usage checks (issue #885), leaving a parser-level bypass where mapping-slot abstraction wiring can drift without CI failure.
20. EVMYulLean capability boundary checker can miss unsupported builtin behavior when dispatch uses non-literal indirection instead of direct `func = "..."` string comparisons (issue #886), leaving a parser-level bypass where unsupported operations may enter `Builtins.lean` without CI failure.

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
