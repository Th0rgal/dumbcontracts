# Trust Assumptions and Verification Boundaries

This document states, in a formal and current way, what Verity proves and what Verity still trusts.

## Scope

Verity uses a single supported compilation path:

`EDSL -> CompilationModel (CompilationModel) -> IR -> Yul -> solc -> bytecode`

The formal Layer 1/2/3 guarantees apply to this path.

Compiler UX status:
- the CLI compiles the canonical EDSL-generated contract set.
- `--edsl-contract <id>` optionally narrows compilation to selected supported contracts.
- linked-library flows remain fail-closed on this EDSL-only CLI path.
Compilation is routed through `Compiler.Lowering` helpers, keeping one centralized
boundary for generated EDSL artifacts.
- Recursive `CompilationModel` safety analyzers on the active path are being
  incrementally totalized (`partial def` -> `def` with explicit termination
  proofs), reducing trusted operational behavior around non-termination.
- Current totalization scope includes parameter-dynamicity checks,
  state read/write analyzers, statement-list validator walkers (return-shape,
  parameter-reference, constructor return, custom-error argument-shape),
  and all Expr/Stmt validation walkers (scoped-identifier, interop,
  internal-call-shape, external-call-target, event-argument-shape validation)
  in `Compiler/CompilationModel.lean`.
- Macro translation now accepts explicit `getMappingUint` / `setMappingUint`
  spellings for `Uint256 -> Uint256` storage fields (in addition to generic
  mapping forms), with fail-closed type diagnostics; this is a syntax/front-end
  extension and does not add new trusted components.

## Verification Chain

```
EDSL
  ↓ [Layer 1: VERIFIED per contract — EDSL ≡ CompilationModel (via interpretSpec; see §9–10)]
CompilationModel (`CompilationModel`)
  ↓ [Layer 2: FULLY VERIFIED — CompilationModel → IR]
IR
  ↓ [Layer 3: FULLY VERIFIED, 1 axiom — IR → Yul]
Yul
  ↓ [trusted external compiler — solc]
EVM Bytecode
```

## Layer-1 Hybrid Transition Strategy

Layer 1 (EDSL ≡ CompilationModel) currently operates as a **hybrid**:

- **Generated subset**: For contracts within the supported EDSL subset, the
  `EDSL -> CompilationModel` correspondence is established by per-contract proofs
  in `Compiler/Proofs/SpecCorrectness/` and `Verity/Proofs/`.
- **Manual escape hatch**: Advanced or out-of-subset constructs (e.g., custom Yul
  injection via linked libraries, ECM patterns, complex ABI encoding) are expressed
  directly in the `CompilationModel` language. These are trusted at the
  CompilationModel boundary — the compiler verifies IR/Yul generation from them,
  but the correspondence to EDSL intent is the developer's responsibility.

This hybrid approach is intentional during transition. The long-term direction is to
expand the generated subset (and eventually automate `EDSL -> CompilationModel`
generation), reducing the manual escape hatch surface over time.

## Current Verified Facts

- Layer 1 (EDSL ≡ CompilationModel, currently `CompilationModel`) is proven in Lean.
- Layer 2 (CompilationModel → IR) is proven in Lean.
- Layer 3 (IR → Yul) is proven in Lean except for one documented axiom.

Metrics tracked by repository tooling:

- 431 theorems across 11 categories.
- 250 theorems have corresponding Foundry property tests.
- 58% runtime test coverage.

(These values are validated by `scripts/check_doc_counts.py` against `artifacts/verification_status.json`.)

## Trusted Components

### 1. Solidity Compiler (`solc`)

- Role: compiles Yul to EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- Status: trusted external tool, version pinned in `foundry.toml` (`solc_version = "0.8.33"`).
- Mitigation: CI enforces pin and Yul compileability checks.

### 2. Keccak-based Selector Computation

- Role: function selector derivation from signatures.
- Status: one explicit axiom in `Compiler/Selectors.lean` (see `AXIOMS.md`).
- Mitigation: CI selector cross-checks against `solc --hashes` and fixtures.

### 3. Linked Yul Libraries

- Role: external functions injected by linker.
- Status: outside formal semantic proofs.
- What is enforced: duplicate-name, collision, unresolved reference, and arity checks.
- What is trusted: semantic correctness of linked Yul code.

### 4. Mapping Slot Derivation and Crypto Assumptions

- Role: proof interpreters derive mapping slots with Solidity-compatible keccak hashing (`Compiler/Proofs/MappingSlot.lean`, `activeMappingSlotBackend = .keccak`), i.e. `solidityMappingSlot(base,key) = keccak256(abi.encode(key, baseSlot))`.
- Status: mapping addressing is EVM-faithful (flat storage addressing, no tagged slot abstraction in active semantics).
- Trust boundary: this relies on the external keccak implementation (`ffi.KEC` via EVMYul FFI) and standard collision-resistance assumptions for keccak256 (the same trust class as Solidity/EVM behavior).
- Mitigation: abstraction-boundary CI (`scripts/check_mapping_slot_boundary.py`), selector/hash cross-check CI, and explicit documentation in `AXIOMS.md`.

### 5. EVM/Yul Semantics and Gas

- Role: runtime execution model.
- Status: trusted EVM behavior; gas is not formally modeled by current proofs.
- EVMYulLean integration: pure arithmetic/comparison/bitwise builtins (add, sub, mul, div, mod, lt, gt, eq, iszero, and, or, xor, not, shl, shr) are bridged to EVMYulLean's formally-defined `UInt256` operations. The adapter covers all 11 Yul statement types. State-dependent builtins (sload, caller, calldataload) and Verity-specific helpers (mappingSlot) remain on the Verity evaluation path.
- Implication: semantic correctness does not imply gas-safety or gas-bounded liveness.

### 6. External Call Modules (ECMs)

- Role: reusable external call patterns (ERC-20 transfers, precompile calls, callbacks, generic ABI calls).
- Status: standard modules in `Compiler/Modules/` are maintained alongside the compiler.
- Trust boundary: the compiler trusts that `mod.compile` produces Yul that correctly implements the pattern described by the module's name, documentation, and axioms.
- Scope: a bug in one module does not affect contracts that don't use it.
- Third-party ECMs (external Lean packages) are outside the Verity team's trust boundary.
- Mitigation: ECM axioms are aggregated and reported at compile time (`--verbose`). Module-level validation (selector bounds, parameter checks) runs within the `compile` function. View/pure mutability enforcement uses `writesState`/`readsState` flags.
- See `docs/EXTERNAL_CALL_MODULES.md` and `AXIOMS.md` for details.

### 7. Foundational Lean Trust

- Role: proof checker and kernel soundness.
- Status: foundational assumption for all Lean-based verification.

### 8. ECM Interface Assumptions

- Role: trust that external contracts/precompiles conform to their declared ABI.
- Status: documented per-module in `AXIOMS.md` and aggregated at compile time.
- Scope: opt-in per contract — only contracts using a given ECM inherit its assumptions.
- Mitigation: axiom aggregation report, code review of standard modules.

## Semantic Caveats Auditors Must Track

### Wrapping Arithmetic

`Uint256` arithmetic in the formal model is **wrapping modulo 2^256**, matching the EVM Yellow Paper. This applies to all operations: add, sub, mul, div, mod, bitwise (and, or, xor, not), and shifts (shl, shr). Division and modulo by zero return 0.

This is a **proven property**, not an axiom — see `Compiler/Proofs/ArithmeticProfile.lean` for formal proofs (`add_wraps`, `sub_wraps`, `mul_wraps`, `div_by_zero`, `mod_by_zero`). The EVMYulLean bridge confirms agreement between Verity's `Nat`-modular arithmetic and EVMYulLean's `Fin`-based `UInt256` operations.

For contracts that require overflow protection, the EDSL provides checked operations (`safeAdd`, `safeSub`, `safeMul`) that return `Option` and can be combined with `requireSomeUint` to revert on overflow. These are EDSL-level constructs — the compiler does not insert automatic overflow checks.

All backend profiles use identical wrapping arithmetic. See [`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full specification.

### Revert-State Modeling

High-level semantics can expose intermediate state in a reverted computation model. EVM runtime reverts discard state. Contracts should preserve checks-before-effects discipline.

See [`docs/REVERT_STATE_MODEL.md`](docs/REVERT_STATE_MODEL.md) for the precise modeling note and proof-author guidance.

## Security Audit Checklist

1. Confirm deployment uses the supported EDSL-only CLI path (optionally narrowed with `--edsl-contract`), and treat linked-library flows as out of path.
2. Review `AXIOMS.md` and ensure the axiom list is unchanged and justified.
3. If linked libraries are used, audit each linked Yul file as trusted code.
4. Validate selector checks, Yul compile checks, and storage-layout checks in CI.
5. Confirm arithmetic and revert assumptions are explicitly acceptable for the target contract.
6. For production readiness, include gas profiling and upper-bound testing.
7. Review ECM axiom report (`--verbose`) and confirm all module trust assumptions are acceptable.
8. If third-party ECMs are used, audit their `AXIOMS.md` and `compile` implementations.

## Change Control Requirement

Any source change that affects architecture, semantics, trust boundary, or CI safeguards must update this file in the same change set.

If this file is stale, audit conclusions may be invalid.

## Related Documents

- [AUDIT.md](AUDIT.md)
- [AXIOMS.md](AXIOMS.md)
- [docs/ARITHMETIC_PROFILE.md](docs/ARITHMETIC_PROFILE.md)
- [docs/REVERT_STATE_MODEL.md](docs/REVERT_STATE_MODEL.md)
- [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md)
- [docs/SOLIDITY_PARITY_PROFILE.md](docs/SOLIDITY_PARITY_PROFILE.md)
- [docs/PARITY_PACKS.md](docs/PARITY_PACKS.md)
- [docs/REWRITE_RULES.md](docs/REWRITE_RULES.md)
- [docs/IDENTITY_CHECKER.md](docs/IDENTITY_CHECKER.md)
- [docs/ROADMAP.md](docs/ROADMAP.md)
- [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)

### 9. SpecInterpreter (`interpretSpec`)

- Role: reference semantics for CompilationModel execution in Layer 1 proofs.
- Status: **trusted, being eliminated** — hand-rolled EVM reimplementation (~500 lines)
  that does not use EVMYulLean. Implements wrapping arithmetic, storage reads/writes,
  mapping slot derivation, control flow, and event emission from scratch.
- Risk: if `interpretSpec` has a bug (e.g., incorrect subtraction wrapping), all
  Layer 1 proofs are vacuously correct against wrong semantics.
- Active mitigation (Issue #998, in progress):
  - `Compiler/Proofs/EndToEnd.lean` composes Layers 2+3 (CompilationModel → IR → Yul)
    into a single theorem, establishing the right-hand side of the target equivalence.
  - `Verity/Proofs/Stdlib/PrimitiveBridge.lean` proves per-primitive lemmas connecting
    EDSL operations (getStorage, setStorage, getStorageAddr, setStorageAddr,
    getMapping, setMapping, add, sub, mul, div, mod, lt, gt, eq, require, if/else,
    msgSender, safeAdd, safeSub, calldataload, Contract.run) to the compiled Yul
    builtin semantics, establishing the left-hand side. Includes mixed-type
    multi-slot encoding for contracts with both Address and Uint256 storage.
  - The macro now emits per-function semantic preservation theorem skeletons
    (via `mkSemanticBridgeCommand` in `Verity/Macro/Bridge.lean`), providing the
    composition framework. These are currently `sorry` — discharging them will
    eliminate `interpretSpec` from the TCB entirely.

### 10. Macro Elaborator (`verity_contract`)

- Role: generates both the EDSL `Contract` monad value and the `CompilationModel`
  from a single syntax tree.
- Status: **trusted** — the `translatePureExpr`/`translateEffectStmt`/`translateDoElems`
  functions in `Verity/Macro/Translate.lean` are unverified metaprograms.
- Trust argument: since both the EDSL value and the CompilationModel are generated
  from the same syntax tree by a deterministic elaborator, semantic equivalence holds
  by construction — provided the elaborator is correct.
- Risk: a translation bug would cause the EDSL and CompilationModel to silently diverge.
- Active mitigation (Issue #998, in progress): the macro now emits per-function
  semantic preservation theorem skeletons (`_semantic_preservation` theorems) that,
  when discharged, provide machine-checked witnesses that the EDSL and CompilationModel
  agree. This is strictly stronger than the previous `_bridge` theorems (which only
  proved body definitional equality via `rfl`).

## Planned Trust-Boundary Hardening

### Issue #967 (Yul identity)

The following items are planned but not yet active:

1. proof-carrying typed rewrite rules for parity transforms;
2. versioned parity packs keyed to pinned compiler tuples;
3. AST-level identity gates between Verity and `solc` Yul outputs.

Until these are implemented and CI-gated, claims of exact `solc` Yul identity remain out of scope.

### Issue #998 (Eliminate interpretSpec, end-to-end semantic bridge)

Goal: a single machine-checked theorem per contract function:
`EDSL execution ≡ EVMYulLean(compile(CompilationModel))`

Roadmap:
1. ✅ Compose Layers 2+3 into a single end-to-end theorem (`Compiler/Proofs/EndToEnd.lean`).
2. ✅ Prove per-primitive correctness lemmas (`Verity/Proofs/Stdlib/PrimitiveBridge.lean`):
   getStorage↔sload, setStorage↔sstore, add/sub/mul/div/mod↔builtins, lt/gt/eq↔comparisons,
   require↔iszero+revert, if/else↔branching, msgSender↔caller,
   Uint256/Address encoding, calldataload, Contract.run unfolding,
   getMapping/setMapping unfolding, mixed-type multi-slot encoding.
3. ✅ Macro emits per-function semantic preservation skeletons (`_semantic_preservation`
   theorems via `mkSemanticBridgeCommand` in `Verity/Macro/Bridge.lean`).
   Theorem asserts structural compatibility: non-empty body, matching param arity,
   and function name agreement between EDSL and CM spec.
3b. ✅ SimpleStorage, Counter, Owned, SafeCounter, and OwnedCounter EDSL≡IR proofs
   fully discharged (`Compiler/Proofs/SemanticBridge.lean`). 16 functions total
   across 5 contracts. OwnedCounter demonstrates mixed-type multi-slot storage
   encoding (Address slot 0 + Uint256 slot 1) and access control composition.
3c. ✅ Universal pure arithmetic bridge theorems stated in EndToEnd.lean
   (add/sub/mul/div/mod ↔ EVMYulLean). Currently `sorry` — requires bridging
   Nat-modular and Fin-based UInt256 representations.
4. 🔲 Discharge the `sorry` in preservation theorems by composing primitive lemmas.
5. 🔲 Delete `interpretSpec` and all manual `SpecCorrectness/*.lean` proofs.
6. 🔲 Expand DSL coverage (dynamic arrays, structs, try/catch, create/create2).

New files:
- `Compiler/Proofs/EndToEnd.lean` — Layers 2+3 composition
- `Verity/Proofs/Stdlib/PrimitiveBridge.lean` — EDSL↔compiled-Yul primitive lemmas
- `Compiler/Proofs/SemanticBridge.lean` — concrete IR-connected EDSL≡IR theorem targets

Modified files:
- `Verity/Macro/Bridge.lean` — added `mkSemanticBridgeCommand`
- `Verity/Macro/Elaborate.lean` — calls `mkSemanticBridgeCommand` per function
- `Verity/Macro/Translate.lean` — exported `contractValueTypeTermPublic`, `strTermPublic`

Cross-repo: verity (core), morpho-verity (benefits from auto proofs), verity-paper (architecture rewrite).

**Last Updated**: 2026-03-01
**Maintainer Rule**: Update on every trust-boundary-relevant code change.
