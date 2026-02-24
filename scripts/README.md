# Verity Scripts

This directory contains verification and testing scripts for the Verity project.

## Property Test Coverage Scripts

These scripts manage the relationship between proven Lean theorems and their corresponding Foundry test implementations.

### Core Scripts

- **`check_property_manifest.py`** - Verifies that `property_manifest.json` contains all property theorems from Lean proofs
- **`check_property_coverage.py`** - Ensures all properties are either tested or explicitly excluded
- **`report_property_coverage.py`** - Generates detailed coverage statistics

### Usage

#### Check Coverage (CI)
```bash
# Verify manifest is up-to-date
python3 scripts/check_property_manifest.py

# Verify all properties are covered or excluded
python3 scripts/check_property_coverage.py
```

#### Generate Coverage Reports
```bash
# Text report (default)
python3 scripts/report_property_coverage.py

# Markdown report (for GitHub)
python3 scripts/report_property_coverage.py --format=markdown

# JSON report (for tooling)
python3 scripts/report_property_coverage.py --format=json

# Fail if coverage is below threshold
python3 scripts/report_property_coverage.py --fail-below 50.0
```

#### Find Missing Properties
```bash
# List properties without test coverage
python3 scripts/report_property_gaps.py

# Generate test stubs for missing properties
python3 scripts/report_property_gaps.py --stubs
```

### Coverage Report Format

The coverage report shows:
- **Total Properties**: All proven theorems across all contracts
- **Covered**: Properties with corresponding Foundry tests (tagged with `Property: <theorem_name>`)
- **Excluded**: Properties explicitly marked as proof-only or requiring special modeling
- **Missing**: Properties that need test coverage (should be 0 after verification)

Example output:
```
✅ SimpleToken
   Total:      59 properties
   Covered:    52 ( 88.1%)
   Excluded:     7 (proof-only)

Overall: 59% coverage (220/371 properties)
```

### Property Exclusions

Properties are excluded in `test/property_exclusions.json` for valid reasons:
- **Proof-only**: Low-level helpers (e.g., `setStorage_*`, `getStorage_*`) that are internal proof machinery
- **Sum equations**: Properties requiring finite address set modeling (e.g., total supply invariants)
- **Internal helpers**: Functions like `isOwner_*` that are tested implicitly through other operations

## Validation Scripts

These CI-critical scripts validate cross-layer consistency:

- **`check_property_manifest_sync.py`** - Ensures `property_manifest.json` stays in sync with actual Lean theorems (detects added/removed theorems)
- **`check_storage_layout.py`** - Validates storage slot consistency across EDSL, Spec, Compiler, and AST layers; strips Lean comments/docstrings with a shared string-aware parser (so `--` and `/- -/` inside string literals are preserved), detects intra-contract slot collisions, derives Spec slot usage from `Verity/Specs/*/Spec.lean` literal state accesses, enforces Spec↔EDSL slot/type parity for compiled non-external contracts, enforces ASTSpec coverage for non-external compiler specs, and checks AST-vs-Compiler slot/type drift
- **`check_mapping_slot_boundary.py`** - Enforces the mapping-slot abstraction boundary for proof interpreters: no proof semantics file may import `MappingEncoding`; builtin dispatch in `Compiler/Proofs/YulGeneration/Builtins.lean` must route through `abstractMappingSlot`/`abstractLoadStorageOrMapping`; runtime interpreters must import `MappingSlot`, use `abstractStoreStorageOrMapping`/`abstractStoreMappingEntry`, avoid legacy mapping internals (`mappingTag`/`encodeMappingSlot`/`decodeMappingSlot`/`encodeNestedMappingSlot`/`normalizeMappingBaseSlot`) including local aliases, and must not define a separate execution-state `mappings` table (`IRState`/`YulState` remain flat-storage only); also enforces explicit backend-scope markers (`activeMappingSlotBackend := .keccak`), presence of keccak helpers (`abiEncodeMappingSlot`, `solidityMappingSlot`), keccak routing through `solidityMappingSlot`, flat-storage keccak routing in `abstractLoadMappingEntry`/`abstractStoreMappingEntry`, smoke-test avoidance of legacy tagged helpers, and matching trust-boundary documentation in `TRUST_ASSUMPTIONS.md`; Lean source checks are comment/string-aware so comment-only or string-literal decoys cannot satisfy required markers
- **`check_yul_builtin_boundary.py`** - Enforces a centralized Yul builtin semantics boundary: runtime interpreters must import `Compiler/Proofs/YulGeneration/Builtins.lean`, call `evalBuiltinCall` or `evalBuiltinCallWithBackend`, and avoid inline builtin dispatch branches (`func = "add"`, `func = "sload"`, etc.); Lean source checks are comment/string-aware so comment-only or string-literal decoys cannot satisfy required call markers
- **`check_builtin_list_sync.py`** - Ensures `Compiler/Linker.lean` `yulBuiltins` stays synchronized with `Compiler/ContractSpec.lean` (`interopBuiltinCallNames ∪ isLowLevelCallName`) while allowing expected Linker-only Yul-object builtins (`datasize`, `dataoffset`, `datacopy`); Lean source checks are comment-aware so commented decoy `def` lines cannot satisfy extraction
- **`check_evmyullean_capability_boundary.py`** - Enforces the current `#294` EVMYulLean overlap capability matrix in `Compiler/Proofs/YulGeneration/Builtins.lean`: allows only the explicit overlap builtin set plus Verity helper `mappingSlot`, blocks known unsupported builtins (`create`, `create2`, `extcodesize`, `extcodecopy`, `extcodehash`) from silently entering the migration seam, and fails closed on non-literal builtin dispatch patterns (`func = op`) unless they resolve through local alias bindings to explicit string literals (including typed and chained aliases)
- **`generate_evmyullean_capability_report.py`** - Deterministically generates `artifacts/evmyullean_capability_report.json` from `Compiler/Proofs/YulGeneration/Builtins.lean` and `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean`, and emits `artifacts/evmyullean_unsupported_nodes.json` as a dedicated machine-readable unsupported-node artifact for adapter lowering gaps; supports `--check` mode for CI freshness gating
- **`generate_evmyullean_adapter_report.py`** - Deterministically generates `artifacts/evmyullean_adapter_report.json` with constructor-level lowering coverage (`supported`/`partial`/`gap`) for `lowerExpr` and `lowerStmt` plus explicit adapter-gap reasons and runtime-seam status (`stub-none` vs `implemented`); supports `--check` mode for CI freshness gating
- **`check_doc_counts.py`** - Validates theorem, axiom, test, suite, coverage, and contract counts across 13 documentation files (README, llms.txt, compiler.mdx, verification.mdx, research.mdx, index.mdx, core.mdx, examples.mdx, getting-started.mdx, TRUST_ASSUMPTIONS, VERIFICATION_STATUS, ROADMAP, test/README), theorem-name completeness in verification.mdx tables, and proven-theorem counts in Property*.t.sol file headers; fails closed on malformed `artifacts/verification_status.json` (strict schema, exact keys, no boolean-as-integer coercions)
- **`check_interop_matrix_sync.py`** - Ensures the Solidity interop support matrix in `docs/ROADMAP.md` and `docs/VERIFICATION_STATUS.md` stays synchronized (row coverage + status-column parity), and rejects duplicate rows that normalize to the same feature key in either document
- **`check_verify_paths_sync.py`** - Ensures `.github/workflows/verify.yml` keeps `on.push.paths` and `on.pull_request.paths` identical, while validating `jobs.changes.filters.code` is duplicate-free and exactly equals trigger paths minus explicit check-only/doc exclusions
- **`check_verify_checks_docs_sync.py`** - Ensures `.github/workflows/verify.yml` `checks` job python-script command sequence matches the documented `**\`checks\` job**` list in this README
- **`check_verify_build_docs_sync.py`** - Ensures `.github/workflows/verify.yml` `build` job python-script command sequence matches the documented `**\`build\` job**` list in this README
- **`check_verify_ci_jobs_docs_sync.py`** - Ensures `.github/workflows/verify.yml` top-level job order matches the CI job summary list in this README (`## CI Integration`)
- **`check_verify_multiseed_sync.py`** - Ensures `foundry-multi-seed` seed lists stay synchronized across `.github/workflows/verify.yml`, `scripts/test_multiple_seeds.sh`, and this README
- **`check_verify_foundry_shard_sync.py`** - Ensures `foundry` shard settings stay synchronized across `.github/workflows/verify.yml` (`matrix.shard_index`, `DIFFTEST_SHARD_COUNT`, `DIFFTEST_RANDOM_SEED`) and this README summary; required env keys must come from `env:` mappings (not lookalike `with:` entries)
- **`check_verify_foundry_patched_sync.py`** - Ensures `foundry-patched` smoke-test settings stay synchronized across `.github/workflows/verify.yml` and this README summary (seed, single-shard mode, and `--no-match-test "Random10000"`); required env keys must come from `env:` mappings; `forge test` detection is shell-token-aware (supports leading `VAR=...`, `env VAR=...`, `/usr/bin/env ...`, `command -- ...`, `env` option wrappers like `env -i ...` / `env -- ...`, and common wrappers such as `time`, `timeout`, `nice`, `nohup`, `setsid`, `ionice`, `chrt` including no-arg flags and positional priority forms, `stdbuf`, and `sudo`)
- **`check_verify_foundry_job_sync.py`** - Ensures shared Foundry job settings stay synchronized across `foundry`, `foundry-patched`, and `foundry-multi-seed` in `.github/workflows/verify.yml` (profile, random params, Yul dir/download wiring, and `Random10000` skip policy); required env keys are extracted from `env:` mappings only, and `forge test` matching is shell-token-aware (supports leading `VAR=...`, `env VAR=...`, `/usr/bin/env ...`, `command -- ...`, `env` option wrappers, and common wrappers such as `time`, `timeout`, `nice`, `nohup`, `setsid`, `ionice`, `chrt` including no-arg flags and positional priority forms, `stdbuf`, and `sudo`)
- **`check_verify_foundry_gas_calibration_sync.py`** - Ensures `foundry-gas-calibration` settings stay synchronized across `.github/workflows/verify.yml` and this README summary (profile, static report artifact/input, and calibration command)
- **`check_verify_artifact_sync.py`** - Ensures downstream artifact downloads in `.github/workflows/verify.yml` match build-job artifact uploads (and rejects duplicate artifact names per producer/consumer job)
- **`generate_verification_status.py`** - Deterministically generates `artifacts/verification_status.json` (theorem/test/axiom/sorry/toolchain metrics) and supports `--check` mode for CI freshness gating
- **`check_solc_pin.py`** - Enforces pinned solc consistency across CI/tooling/docs: `verify.yml` (`SOLC_VERSION`, `SOLC_URL`, `SOLC_SHA256`), `foundry.toml` (`solc_version`), `setup-solc` action URL/SHA usage, and `TRUST_ASSUMPTIONS.md` pinned version line; fails closed on conflicting repeated `SOLC_*` assignments (including job-level overrides)
- **`check_axiom_locations.py`** - Validates that AXIOMS.md line number references match actual axiom locations in source files
- **`check_contract_structure.py`** - Validates all contracts in Examples/ have complete file structure (Spec, Invariants, Basic proofs, Correctness proofs)
- **`check_lean_hygiene.py`** - Validates proof hygiene (`#eval/#check/#print/#reduce`, `native_decide`, `sorry`) and exactly 1 `allowUnsafeReducibility`; parsing is comment/string-aware (including Lean raw strings) via shared Lean lexer utilities
- **`check_lean_warning_regression.py`** - Enforces Lean warning non-regression from `lake build` output against `artifacts/lean_warning_baseline.json` (allows warning reduction, blocks warning increases by total/file/message), with strict baseline schema enforcement (required keys, no null counters, no boolean-as-integer coercions) and fail-closed UTF-8 log decoding

```bash
# Run locally before submitting documentation changes
python3 scripts/generate_verification_status.py
python3 scripts/check_doc_counts.py
python3 scripts/check_interop_matrix_sync.py
python3 scripts/check_verify_paths_sync.py
python3 scripts/check_verify_checks_docs_sync.py
python3 scripts/check_verify_build_docs_sync.py
python3 scripts/check_verify_ci_jobs_docs_sync.py
python3 scripts/check_verify_multiseed_sync.py
python3 scripts/check_verify_foundry_shard_sync.py
python3 scripts/check_verify_foundry_patched_sync.py
python3 scripts/check_verify_foundry_job_sync.py
python3 scripts/check_verify_foundry_gas_calibration_sync.py
python3 scripts/check_verify_artifact_sync.py

# Run locally after modifying storage slots or adding contracts
python3 scripts/check_storage_layout.py

# After a lake build, enforce warning non-regression
python3 scripts/check_lean_warning_regression.py --log lake-build.log

# After intentionally reducing warning baseline, refresh artifact
python3 scripts/check_lean_warning_regression.py --log lake-build.log --write-baseline artifacts/lean_warning_baseline.json

# Run locally after adding/removing theorems
python3 scripts/check_property_manifest_sync.py

# Run locally after adding a new contract
python3 scripts/check_contract_structure.py

# Regenerate capability artifact after builtin-boundary updates
python3 scripts/generate_evmyullean_capability_report.py
python3 scripts/generate_evmyullean_adapter_report.py
```

## Selector & Yul Scripts

- **`check_selectors.py`** - Verifies selector hash consistency across ContractSpec, compile selector tables, and generated Yul (`generated/yul` and `generated/yul-ast` when present); strips Lean comments/docstrings with the same shared string-aware parser used by storage checks; parses `ParamType` expressions recursively (including `bool`, tuple, array, and fixed-array forms) when extracting Solidity signatures; enforces compile selector table coverage for all specs except those with non-empty `externals`
- **`check_selector_fixtures.py`** - Cross-checks selectors against solc-generated hashes; fixture signature extraction is comment/string-aware so commented examples/debug strings cannot create false selector expectations, scans full function headers (so visibility can appear after modifiers like `virtual`), includes only `public`/`external` selectors (matching `solc --hashes`), canonicalizes ABI-sensitive param forms (`function(...)`, `uint/int` aliases, user-defined `contract`/`enum`/`type` aliases, and struct params into canonical tuple signatures), parses both `solc --hashes` output layouts robustly (including nested tuple signatures), and enforces reverse completeness (every `solc --hashes` signature must be present in extracted fixtures)
- **`check_yul_compiles.py`** - Ensures generated Yul code compiles with solc, fails closed when any requested `--dir` is missing/empty, can enforce filename-set parity between directories (e.g. legacy vs patched outputs), can compare bytecode parity between directories, and can enforce a checked baseline of known compare diffs via allowlist
- **`check_gas_report.py`** - Validates `lake exe gas-report` output shape, arithmetic consistency of totals, and monotonicity under more conservative static analysis settings
- **`check_patch_gas_delta.py`** - Compares baseline vs patch-enabled static gas reports, reports median/p90 deltas for total/deploy/runtime gas, enforces total-gas median/p90 non-regression thresholds, and supports configurable minimum improved-contract thresholds
- **`check_gas_model_coverage.py`** - Verifies that every call emitted in generated Yul has an explicit cost branch in `Compiler/Gas/StaticAnalysis.lean` (prevents silent fallback to unknown-call costs)
- **`check_gas_calibration.py`** - Compares static bounds (`lake exe gas-report`) against Foundry `--gas-report` measurements for `test/yul/*.t.sol`, requiring runtime bounds + transaction base gas to dominate observed max call gas, deploy bounds + creation/code-deposit overhead to dominate deployment gas, and every static-report contract to have both runtime + deployment Foundry measurements (unless explicitly allowlisted). Parsing is header-driven (not fixed-column) and strips ANSI color escapes to tolerate Foundry output-format drift. Accepts precomputed `--static-report` and `--foundry-report` files for deterministic replay/debugging.

```bash
# Default: check generated/yul
python3 scripts/check_yul_compiles.py

# Check multiple directories and enforce legacy/AST known-diff baseline
python3 scripts/check_yul_compiles.py \
  --dir generated/yul \
  --dir generated/yul-patched \
  --dir generated/yul-ast \
  --require-same-files generated/yul generated/yul-patched \
  --compare-dirs generated/yul generated/yul-ast \
  --allow-compare-diff-file scripts/fixtures/yul_ast_bytecode_diffs.allowlist

# Check static gas model coverage against legacy + patched + AST Yul outputs
python3 scripts/check_gas_model_coverage.py \
  --dir generated/yul \
  --dir generated/yul-patched \
  --dir generated/yul-ast

# Check patch-enabled static gas deltas (median/p90 non-regression + configurable improvement floor)
python3 scripts/check_patch_gas_delta.py \
  --baseline-report gas-report-static.tsv \
  --patched-report gas-report-static-patched.tsv \
  --min-improved-contracts 0
```

## Contract Scaffold Generator

- **`generate_contract.py`** - Generates all boilerplate files for a new contract

```bash
# Simple contract
python3 scripts/generate_contract.py MyContract

# Contract with typed fields and custom functions
python3 scripts/generate_contract.py MyToken \
  --fields "balances:mapping,totalSupply:uint256,owner:address" \
  --functions "deposit(uint256),withdraw(uint256),getBalance(address)"

# Preview without creating files
python3 scripts/generate_contract.py MyContract --dry-run
```

Creates 9 files: EDSL implementation, AST bridge scaffold, Spec, Invariants, Proofs re-export, Basic proofs, Correctness proofs, SpecCorrectness scaffold, and Property tests. Prints instructions for manual steps (All.lean imports, Compiler/Specs.lean entry).

Identifier rules (fail-fast validation):
- Contract name: PascalCase alphanumeric (existing rule), e.g. `MyToken`
- Field names: `[A-Za-z_][A-Za-z0-9_]*`
- Function names: `[A-Za-z_][A-Za-z0-9_]*`
- Reserved Lean/Solidity keywords are rejected for generated field/function names
- `--functions` signatures must be comma-separated and parenthesis-balanced
- Supported function parameter types are `uint256` and `address` (unknown types are rejected)
- Getter property test scaffolds are emitted as explicit `testTODO_*` placeholders that revert until return-value and non-mutation assertions are implemented

## Utilities

- **`property_utils.py`** - Shared utilities for loading manifests, exclusions, and test coverage
- **`keccak256.py`** - Keccak-256 hashing implementation for selector verification
- **`extract_property_manifest.py`** - Extracts theorem names from Lean proofs to regenerate `property_manifest.json`
- **`test_multiple_seeds.sh`** - Runs Foundry tests with multiple random seeds to detect flakiness

## CI Integration

Scripts run automatically in GitHub Actions (`verify.yml`) across 7 jobs:

**`changes`** — Path filter that gates code-dependent jobs (doc-only PRs skip build/test)

**`checks` job** (fast, no Lean build required):
1. Property manifest validation (`check_property_manifest.py`)
2. Property coverage validation (`check_property_coverage.py`)
3. Contract file structure validation (`check_contract_structure.py`)
4. Axiom location validation (`check_axiom_locations.py`)
5. Verification status artifact freshness (`generate_verification_status.py --check`)
6. Documentation count validation (`check_doc_counts.py`)
7. Solidity interop matrix sync (`check_interop_matrix_sync.py`)
8. Verify workflow path-filter sync (`check_verify_paths_sync.py`)
9. Verify checks/docs sync (`check_verify_checks_docs_sync.py`)
10. Verify build/docs sync (`check_verify_build_docs_sync.py`)
11. Verify CI job/docs sync (`check_verify_ci_jobs_docs_sync.py`)
12. Verify multi-seed sync (`check_verify_multiseed_sync.py`)
13. Verify foundry shard sync (`check_verify_foundry_shard_sync.py`)
14. Verify foundry-patched sync (`check_verify_foundry_patched_sync.py`)
15. Verify foundry job sync (`check_verify_foundry_job_sync.py`)
16. Verify foundry-gas-calibration sync (`check_verify_foundry_gas_calibration_sync.py`)
17. Verify artifact upload/download sync (`check_verify_artifact_sync.py`)
18. Solc pin consistency (`check_solc_pin.py`)
19. Property manifest sync (`check_property_manifest_sync.py`)
20. Storage layout consistency (`check_storage_layout.py`)
21. Lean hygiene (`check_lean_hygiene.py`)
22. Static gas model builtin coverage (`check_gas_model_coverage.py`)
23. Mapping-slot abstraction boundary (`check_mapping_slot_boundary.py`)
24. Yul builtin abstraction boundary (`check_yul_builtin_boundary.py`)
25. Builtin list sync (Linker ↔ ContractSpec) (`check_builtin_list_sync.py`)
26. EVMYulLean capability boundary (`check_evmyullean_capability_boundary.py`)
27. EVMYulLean capability + unsupported-node report freshness (`generate_evmyullean_capability_report.py --check`)
28. EVMYulLean adapter report freshness (`generate_evmyullean_adapter_report.py --check`)

**`build` job** (requires `lake build` artifacts):
1. Lean warning non-regression (`check_lean_warning_regression.py` over `lake-build.log`)
2. Static gas model coverage on generated Yul (legacy + patched + AST) (`check_gas_model_coverage.py`)
3. Keccak-256 self-test (`keccak256.py --self-test`)
4. Selector hash verification (`check_selectors.py`)
5. Yul compilation (legacy + patched + AST) + legacy/AST diff-baseline check (`check_yul_compiles.py`)
6. Selector fixture check (`check_selector_fixtures.py`)
7. Static gas report invariants (`check_gas_report.py`)
8. Save baseline + patch-enabled static gas report artifacts (`gas-report-static.tsv`, `gas-report-static-patched.tsv`)
9. Patch gas delta non-regression + measurable improvement gate (`check_patch_gas_delta.py`)
10. Coverage and storage layout reports in workflow summary (`report_property_coverage.py`, `check_storage_layout.py`)

**`foundry-gas-calibration`** — Static-vs-Foundry gas calibration check (`check_gas_calibration.py`) using build-artifact static report + Foundry gas report (runtime + deployment)
**`foundry`** — 8-shard parallel Foundry tests with seed 42
**`foundry-patched`** — Patched-Yul smoke gate on differential/property harness (seed 42, single shard, no `Random10000`)
**`foundry-multi-seed`** — 7-seed flakiness detection (seeds: 0, 1, 42, 123, 999, 12345, 67890)

## Adding New Property Tests

To add test coverage for a proven theorem:

1. Add a `Property: <theorem_name>` comment in your test function:
   ```solidity
   /**
    * Property: transfer_preserves_balance
    * Theorem: Transfer doesn't change total balance
    */
   function testProperty_TransferPreservesBalance() public { ... }
   ```

2. Run verification:
   ```bash
   python3 scripts/check_property_coverage.py
   python3 scripts/report_property_coverage.py
   ```

3. If the property cannot be tested in Foundry (e.g., proof-only helper), add it to `test/property_exclusions.json`
