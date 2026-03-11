# Verification Status

## Architecture

Verity implements a **three-layer verification stack** proving smart contracts correct from specification to Yul bytecode:

```
EDSL contracts (Lean)
    ↓ Layer 1: EDSL ≡ CompilationModel [PROVEN FOR CURRENT CONTRACTS; GENERIC CORE, CONTRACT BRIDGES]
CompilationModel (declarative compiler-facing model)
    ↓ Layer 2: CompilationModel → IR [GENERIC WHOLE-CONTRACT THEOREM, AXIOM-FREE]
Intermediate Representation (IR)
    ↓ Layer 3: IR → Yul [GENERIC SURFACE, EXPLICIT BRIDGE HYPOTHESIS]
Yul (EVM Assembly)
    ↓ (Trusted: solc compiler)
EVM Bytecode
```

## Layer 1: EDSL ≡ CompilationModel, PROVEN FOR CURRENT CONTRACTS

**What it proves today**: The EDSL `Contract` monad execution is equivalent to `CompilationModel` interpretation for the current supported contract set. This is the frontend semantic bridge. The proof stack has a generic typed-IR core, but the active bridge theorems are still instantiated per contract. Separate per-contract proofs under `Contracts/<Name>/Proofs/` then show these contracts satisfy their human-readable specifications; those specification theorems are downstream contract proofs, not the definition of Layer 1 itself.

### Verified Contracts

| Contract | Properties | Status | Location |
|----------|------------|--------|----------|
| SimpleStorage | 20 | Complete | `Contracts/SimpleStorage/Proofs/` |
| Counter | 28 | Complete | `Contracts/Counter/Proofs/` |
| SafeCounter | 25 | Complete | `Contracts/SafeCounter/Proofs/` |
| Owned | 23 | Complete | `Contracts/Owned/Proofs/` |
| OwnedCounter | 48 | Complete | `Contracts/OwnedCounter/Proofs/` |
| Ledger | 33 | Complete | `Contracts/Ledger/Proofs/` |
| LocalObligationMacroSmoke | 4 | Baseline | `Contracts/LocalObligationMacroSmoke/Proofs/` |
| SimpleToken | 61 | Complete | `Contracts/SimpleToken/Proofs/` |
| ERC20 | 19 | Baseline | `Contracts/ERC20/Proofs/` |
| ERC721 | 11 | Baseline | `Contracts/ERC721/Proofs/` |
| ReentrancyExample | 5 | Complete | `Contracts/ReentrancyExample/Contract.lean` |
| CryptoHash | 0 | No specs | `Contracts/CryptoHash/Contract.lean` |
| **Total** | **277** | **✅ 100%** | — |

> **Note**: Stdlib (0 internal proof-automation properties) is excluded from the contract-spec theorem table above but included in overall coverage statistics (277 total properties).

Layer 1 uses macro-generated EDSL-to-`CompilationModel` bridge theorems backed by a generic typed-IR compilation-correctness theorem ([`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)). Tuple/bytes/fixed-array/dynamic-array/string parameters now stay inside that proof path when they are carried as ABI head words/offsets. Advanced constructs beyond that typed-IR head-word surface (linked libraries, ECMs, fully custom ABI behavior) are still expressed directly in `CompilationModel` and trusted at that boundary.

Internal helper calls are supported operationally in `CompilationModel` and the fuel-based interpreter path, but helper-level compositional proof reuse across callers is not yet a first-class verified interface. Current EDSL-to-`CompilationModel` bridge instantiations remain contract-specific; the reusable internal-helper proof boundary is tracked in [#1335](https://github.com/Th0rgal/verity/issues/1335).

## Layer 2: CompilationModel → IR — GENERIC WHOLE-CONTRACT THEOREM

Tracking:
- Follow-on widening and migration work: [#1510](https://github.com/Th0rgal/verity/issues/1510)
- Axiom-elimination work completed in: [#1618](https://github.com/Th0rgal/verity/issues/1618)
- Proof decomposition plan: [GENERIC_LAYER2_PLAN.md](./GENERIC_LAYER2_PLAN.md)

**What is generic today**:
- a structural theorem for raw statement lists inside the explicit `SupportedStmtList` fragment witness in [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean), re-exported for the compiler-proof layer in [`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean)
- a whole-contract theorem surface, [`compile_preserves_semantics`](../Compiler/Proofs/IRGeneration/Contract.lean), quantified over arbitrary supported `CompilationModel`s, selectors, a `SupportedSpec` witness, and successful `CompilationModel.compile` output

**What is not yet covered**:
- the supported whole-contract fragment is still intentionally narrower than the full `CompilationModel` surface; unsupported features remain documented at the boundary instead of being claimed as proved

### What is not fully migrated yet

- The generic theorem surface is in place, but the supported whole-contract fragment is still narrower than the full `CompilationModel` / EDSL surface.
- Contracts and features outside `SupportedSpec` still rely on explicit trust-surface documentation, targeted testing, or future fragment-widening work rather than a claim of full generic compile-preservation.

**Current boundary**:
- Generic: supported statement-list compilation and the whole-contract theorem itself
- Proved generically: initial-state normalization between `withTransactionContext` and `initialIRStateForTx`, under explicit transaction-context normalization hypotheses
- No Lean axioms remain in Layer 2
- Additional explicit precondition: the generic theorem surface now requires the observed transaction-context fields (`sender`, `thisAddress`, `msgValue`, `blockTimestamp`, `blockNumber`, `chainId`) to already fit the bounded source-side `Address`/`Uint256` domains
- Outside the current generic theorem or current proof model: events/logs, proxy/delegatecall upgradeability, linked externals, local unsafe obligations, and other trust-surfaced features not captured by the current supported whole-contract fragment

Key files:
- [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)
- [`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean)
- [`Function.lean`](../Compiler/Proofs/IRGeneration/Function.lean)
- [`Contract.lean`](../Compiler/Proofs/IRGeneration/Contract.lean)
- [`EndToEnd.lean`](../Compiler/Proofs/EndToEnd.lean)

## Layer 3: IR → Yul, GENERIC, WITH EXPLICIT AXIOM BOUNDARY

**What it proves today**: Yul code generation preserves IR semantics through a generic statement/function equivalence stack, but the current full dispatch-preservation path still depends on 1 documented bridge hypothesis in [`Preservation.lean`](../Compiler/Proofs/YulGeneration/Preservation.lean). The checked contract-level theorem surface now explicitly requires dispatch-guard safety for each selected function case: word-level zero `msg.value` on non-payable paths and a non-wrapping calldata-width bound for each case guard.

All 8 Yul statement types proven equivalent to IR counterparts. Universal dispatcher theorem:

```lean
theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    statesAligned selector irState yulState →
    execResultsAligned selector
      (execIRStmt irState stmt)
      (execYulStmtFuel fuel yulState stmt)
```

Key files: [`StatementEquivalence.lean`](../Compiler/Proofs/YulGeneration/StatementEquivalence.lean), [`Preservation.lean`](../Compiler/Proofs/YulGeneration/Preservation.lean), [`AXIOMS.md`](../AXIOMS.md)

## Example Contract Compilation Coverage

The repository contains several different kinds of contract examples. Their current compile-preservation status is not uniform.

### Contracts covered by the generic Layer 2 theorem

All contracts within the `SupportedSpec` fragment are covered by the generic whole-contract theorem in `Compiler/Proofs/IRGeneration/Contract.lean`. No manual per-contract bridge proofs are needed.

### Spec proofs exist, contract-level compile-preservation is generic

All current contracts with spec proofs benefit from the generic Layer 2 theorem if they fall within the supported fragment. Contracts outside the fragment (e.g., those using linked externals or unsupported features) rely on testing for compile-preservation confidence.

### Semantic example, not a current `verity_contract` compilation example

- `ReentrancyExample`

`ReentrancyExample` is proved as a semantic case study in Lean, but it is not a current `verity_contract` macro contract with a contract-level compilation-preservation theorem surface in this repo.

### Intentionally outside the current proof-complete compilation subset

- `CryptoHash`: linked external Yul libraries / external call oracle surface
- `RawLogTrustSurface`: raw event emission trust surface
- `LocalObligationTrustSurface`: explicit local unsafe/refinement obligation surface
- `ProxyUpgradeabilityMacroSmoke`, `ProxyUpgradeabilityLayoutCompatibleSmoke`, `ProxyUpgradeabilityLayoutIncompatibleSmoke`: proxy / `delegatecall` / upgradeability semantics are outside the current proof model
- `StringSmoke`, `StringEventSmoke`, `StringErrorSmoke`: smoke examples for string, error, and event surfaces rather than current end-to-end proof-complete examples

Also note that the macro-generated `*_semantic_preservation` theorems are not contract-to-Yul semantic-preservation theorems. They are body-alignment equalities between generated `CompilationModel` bodies and macro-generated body fixtures, not full execution-preservation proofs for compiled IR/Yul.

## Property Test Coverage

| Contract | Coverage | Exclusions |
|----------|----------|------------|
| ERC20 | 100% (19/19) | 0 |
| ERC721 | 100% (11/11) | 0 |
| SafeCounter | 100% (25/25) | 0 |
| ReentrancyExample | 100% (5/5) | 0 |
| Ledger | 100% (33/33) | 0 |
| LocalObligationMacroSmoke | 100% (4/4) | 0 |
| SimpleStorage | 95% (19/20) | 1 proof-only |
| OwnedCounter | 92% (44/48) | 4 proof-only |
| Owned | 87% (20/23) | 3 proof-only |
| SimpleToken | 85% (52/61) | 9 proof-only |
| Counter | 82% (23/28) | 5 proof-only |
| Stdlib | 0% (0/0) | 0 proof-only |

**Status**: 92% coverage (255/277), 22 remaining exclusions all proof-only

- **Total Properties**: 277
- **Covered**: 255
- **Excluded**: 22 (all proof-only)

**Proof-Only Properties (22 exclusions)**: Internal proof machinery that cannot be tested in Foundry.

0 `sorry` remaining across `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules.

1 documented Lean axiom remains. The Layer 2 body-simulation axiom has been eliminated, and the Layer 3 dispatch bridge is tracked as an explicit theorem hypothesis rather than a Lean axiom.

## Differential Testing

**Status**: CI runs large sharded randomized differential suites against the current contract set, comparing EDSL interpreter output against Solidity-compiled EVM execution.

## Feature Support Matrix

This matrix tracks EDSL language features and their status across the compilation and verification stack. The key distinction is between features that **compile and execute correctly** (Spec/Codegen/Interpreter) and features **covered by the generic proof** (`SupportedSpec`).

| Feature | Spec/EDSL | Codegen | Interpreter | Generic Proof | Issue |
|---|---|---|---|---|---|
| **Core arithmetic** (add, sub, mul, div, mod, comparisons) | supported | supported | supported | supported | |
| **Boolean logic** (and, or, not) | supported | supported | supported | supported | |
| **Local variables** (let, assign) | supported | supported | supported | supported | |
| **Require + revert** (simple condition) | supported | supported | supported | supported | |
| **Return** (single scalar) | supported | supported | supported | supported | |
| **Stop** | supported | supported | supported | supported | |
| **Storage read/write** (uint256 fields) | supported | supported | supported | supported | |
| **Selector dispatch + ABI parameter loading** | supported | supported | supported | supported (uint256, uint8, address, bytes32) | |
| **Payable modifier** | supported | supported | supported | supported (dispatch guard) | |
| **Event ABI parity** (indexed dynamic/tuple) | supported | supported | supported | supported | |
| **If/else branching** | supported | supported | supported | partial (in SupportedStmtFragment patterns) | [#1618](https://github.com/Th0rgal/verity/issues/1618) |
| **Storage read/write** (address fields) | supported | supported | supported | excluded from SupportedSpec | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Mappings / multi-mappings** | supported | supported | supported | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Packed storage fields** | supported | supported | partial | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Dynamic storage arrays** | supported | supported | supported | not in generic proof | [#1571](https://github.com/Th0rgal/verity/issues/1571), [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Struct-valued storage** | supported | supported | supported | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Internal helper calls** | supported | supported | supported | not compositional | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **forEach loops** | supported | supported | supported | known proof gap | [#1623](https://github.com/Th0rgal/verity/issues/1623) |
| **Constructor** | supported | supported | supported | excluded from SupportedSpec | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **fallback / receive** | supported | supported | supported | excluded from SupportedSpec | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Events (emit)** | supported | supported | supported | not in proof model | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Raw log (rawLog)** | supported | supported | n/a | not in proof model | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Custom errors (revertError)** | supported | supported | supported | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **returnValues** (multi-return, arrays, bytes) | supported | supported | supported | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Linked externals (ExternalFunction)** | supported | supported | axiom-tracked | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **ECM (external call modules)** | supported | supported | supported | not in proof model | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Low-level calls** (call / staticcall) | supported | supported | not modeled | not in proof model | [#1627](https://github.com/Th0rgal/verity/issues/1627), [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **delegatecall** (proxy/upgradeability) | supported | supported | not modeled | not in proof model | [#1627](https://github.com/Th0rgal/verity/issues/1627), [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **returndata** (returndataCopy, returndataSize) | supported | supported | not modeled | not in proof model | [#1627](https://github.com/Th0rgal/verity/issues/1627), [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Linear memory** (mstore, mload, calldatacopy) | supported | supported | partial | partially modeled | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Bitwise ops** (and, or, xor, not, shl, shr) | supported | supported | supported | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Signed arithmetic** (sdiv, smod, sar, sgt, slt, signextend) | supported | supported | supported | not in generic proof | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **Fixed-point math** (mulDivDown, mulDivUp, wMulDown, wDivUp) | supported | supported | supported | not in generic proof | [#1622](https://github.com/Th0rgal/verity/issues/1622), [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **keccak256** | supported | supported | axiomatized | axiomatized primitive | |
| **ABI JSON artifact generation** | supported | supported | n/a | n/a | |
| **Local obligations** | supported | supported | n/a | excluded from SupportedSpec | [#1630](https://github.com/Th0rgal/verity/issues/1630) |
| **ETH balance tracking** | not supported | not supported | not supported | n/a | [#1628](https://github.com/Th0rgal/verity/issues/1628) |
| **create / create2** | not supported | not supported | not supported | n/a | [#1626](https://github.com/Th0rgal/verity/issues/1626) |
| **Contract composition (mixins)** | not supported | not supported | not supported | n/a | [#1572](https://github.com/Th0rgal/verity/issues/1572) |

### Legend

- **supported**: works end-to-end, proven where applicable
- **partial**: works with known limitations
- **not in generic proof**: compiles and executes correctly, but `SupportedSpec` excludes it from the generic whole-contract Layer 2 theorem
- **not in proof model**: the proof interpreter does not have semantics for this feature
- **not compositional**: works per-contract but helper-level proof reuse across callers is not verified
- **axiomatized**: assumed correct via named axiom (`keccak256_first_4_bytes`)
- **not supported**: not implemented

Diagnostics policy for unsupported constructs:
1. Report the exact unsupported construct at compile time.
2. Suggest the nearest supported migration pattern.
3. Link to the owning tracking issue.
4. When low-level mechanics, raw `rawLog` event emission, axiomatized primitives (for example `keccak256`), local unsafe/refinement obligations, or external assumptions are in play, emit a machine-readable trust report via `verity-compiler --trust-report <path>`. The report groups foreign trust surfaces into explicit `proofStatus.proved`, `proofStatus.assumed`, and `proofStatus.unchecked` buckets, localizes them to constructor/function `usageSites`, surfaces localized `localObligations`, and now separately lists `notModeledEventEmission`, `notModeledProxyUpgradeability`, `partiallyModeledLinearMemoryMechanics`, and `partiallyModeledRuntimeIntrospection` so the current event, proxy/upgradeability, memory/ABI, and runtime-context proof gaps are explicit in both contract-level and per-site audit output. In human-readable mode, `--verbose` now emits matching usage-site and contract-level summaries. For fail-closed verification runs, add `--deny-unchecked-dependencies`, which now reports the exact usage site that introduced each unchecked dependency. For proof-strict runs that reject any unproved foreign surface, use `--deny-assumed-dependencies`, which fails on both `assumed` and `unchecked` linked externals / ECM modules and reports the exact usage site. For primitive-proof-strict runs, add `--deny-axiomatized-primitives`, which fails on any remaining axiomatized primitive and reports the exact usage site. For local-obligation-proof-strict runs, add `--deny-local-obligations`, which fails on any remaining `assumed` or `unchecked` localized unsafe/refinement obligation and reports the exact usage site. For memory-proof-strict runs, add `--deny-linear-memory-mechanics`, which fails on any remaining partially modeled linear-memory mechanic and reports the exact usage site. For event-proof-strict runs, add `--deny-event-emission`, which fails on any remaining raw `rawLog` event emission and reports the exact usage site. For low-level-proof-strict runs, add `--deny-low-level-mechanics`, which fails on any remaining first-class low-level call / returndata mechanic and reports the exact usage site. For proxy-proof-strict runs, add `--deny-proxy-upgradeability`, which fails on any remaining `delegatecall`-based proxy / upgradeability mechanic and reports the exact usage site; the dedicated proxy semantics gap is tracked under issue `#1420`. For runtime-proof-strict runs, add `--deny-runtime-introspection`, which fails on any remaining partially modeled runtime-introspection primitive and reports the exact usage site.

## Trust Assumptions

See [`TRUST_ASSUMPTIONS.md`](../TRUST_ASSUMPTIONS.md) for the full trust model and [`AXIOMS.md`](../AXIOMS.md) for axiom documentation.

---

**Last Updated**: 2026-03-11
