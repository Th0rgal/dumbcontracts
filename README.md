<p align="center">
  <img src="verity.svg" alt="Verity" width="200" />
</p>

<h1 align="center">Verity</h1>

<p align="center">
  <strong>Formally verified smart contracts. From spec to bytecode.</strong><br>
  <em>Write simple rules. Let agents implement. Math proves the rest.</em>
</p>

<p align="center">
  <a href="https://github.com/Th0rgal/verity/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT License"></a>
  <a href="https://github.com/Th0rgal/verity"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/Th0rgal/verity"><img src="https://img.shields.io/badge/theorems-431-brightgreen.svg" alt="431 Theorems"></a>
  <a href="https://github.com/Th0rgal/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/Th0rgal/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

---

## 5-Minute Quick Start

```bash
# 1. Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env

# 2. Clone and build
git clone https://github.com/Th0rgal/verity.git
cd verity
lake build                                    # Verifies all 431 theorems

# 3. Generate a new contract
python3 scripts/generate_contract.py MyContract

# 4. Compile to Yul/EVM
lake build verity-compiler
lake exe verity-compiler                      # Output in compiler/yul/
lake exe verity-compiler --input model        # Explicit manual CompilationModel path
```

`--input edsl` is reserved for the verified automatic EDSL-lowering path and currently fails closed with a diagnostic until that wiring lands.

**With external libraries (e.g., Poseidon hash):**
```bash
# Link your Yul library at compile time
lake exe verity-compiler --link examples/external-libs/MyLib.yul -o compiler/yul
```

**With deterministic Yul patch pass + coverage report:**
```bash
lake exe verity-compiler \
  --enable-patches \
  --patch-max-iterations 2 \
  --patch-report compiler/patch-report.tsv \
  --mapping-slot-scratch-base 128 \
  -o compiler/yul-patched
```

`--mapping-slot-scratch-base` controls where compiler-generated `mappingSlot` helpers write temporary words before `keccak256`.

**With backend profile (issue #802, opt-in):**
```bash
# Default semantic profile
lake exe verity-compiler --backend-profile semantic

# Solidity-parity ordering only: sort dispatch `case` blocks by selector
lake exe verity-compiler --backend-profile solidity-parity-ordering

# Full Solidity-parity profile (current MVP):
# - sort dispatch `case` blocks by selector
# - enable deterministic patch pass
lake exe verity-compiler --backend-profile solidity-parity

# Versioned parity-pack selection (pinned tuple)
lake exe verity-compiler --parity-pack solc-0.8.28-o200-viair-false-evm-shanghai
lake exe verity-compiler --parity-pack solc-0.8.28-o999999-viair-true-evm-paris
```

Normalization rules, scope levels, and reproducibility guarantees are versioned in [`docs/SOLIDITY_PARITY_PROFILE.md`](docs/SOLIDITY_PARITY_PROFILE.md).
Groundwork docs for parity packs, rewrite rules, and identity checking are tracked in
[`docs/PARITY_PACKS.md`](docs/PARITY_PACKS.md),
[`docs/REWRITE_RULES.md`](docs/REWRITE_RULES.md), and
[`docs/IDENTITY_CHECKER.md`](docs/IDENTITY_CHECKER.md).

For mapping-backed struct layouts, `CompilationModel` supports:
- `Expr.mappingWord field key wordOffset`
- `Stmt.setMappingWord field key wordOffset value`
- `Expr.mappingPackedWord field key wordOffset { offset, width }`
- `Stmt.setMappingPackedWord field key wordOffset { offset, width } value`

The `mappingPackedWord` forms perform masked/shifted packed read-modify-write at `mappingSlot(base,key) + wordOffset`.

**Run tests:**
```bash
FOUNDRY_PROFILE=difftest forge test           # 404 tests across 35 suites
```

---

## Verification Guarantees

Every claim below is enforced by CI on every commit. Each one can be independently reproduced with a single command.

| Claim | Value | Verify locally |
|-------|-------|----------------|
| Proven theorems | 431 | `make verify` |
| Incomplete proofs (`sorry`) | 0 | `make verify` (Lean rejects sorry) |
| Project-specific axioms | 1 ([documented](AXIOMS.md)) | `make axiom-report` |
| Axiom dependency audit | 613 theorems checked | `make axiom-report` |
| Foundry runtime tests | 404 across 35 suites | `make test-foundry` |
| Property test coverage | 250/431 (58%) | `python3 scripts/check_property_coverage.py` |
| CI validation scripts | 30 | `make check` |
| Proof length enforcement | 92% under 30 lines | `python3 scripts/check_proof_length.py` |

See [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) for the full trust model and [CONTRIBUTING.md](CONTRIBUTING.md) for the proof hygiene requirements enforced on every PR.

---

Verity is a Lean 4 framework that lets you write smart contracts in a domain specific language, prove key properties, and compile to EVM bytecode.

The project has three contract artifacts. Keep them separate:
1. `EDSL implementation` (`Verity/Examples/*`): executable Lean code in the `Contract` monad.
2. `Logical spec` (`Verity/Specs/*/Spec.lean`): `Prop` statements that describe intended behavior.
3. `CompilationModel` (`Compiler/CompilationModel.lean`): declarative compiler-facing model with function bodies (`Expr`/`Stmt`), used for IR and Yul generation.

## How It Works

```lean
-- 1) Logical spec (property, not compiler input)
def store_spec (value : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 0 = value ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

-- 2) EDSL implementation (executable)
def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

-- 3) Prove implementation satisfies the logical spec
theorem store_meets_spec (s : ContractState) (value : Uint256) :
  store_spec value s (((store value).run s).snd) := by
  simp [store, store_spec, storedData, setStorage, storageUnchangedExcept, sameAddrMapContext]
```

Then separately, the compilation model (`CompilationModel`/`CompilationModel`) drives compilation. It is more than an ABI: it includes storage layout plus function bodies.

```lean
def simpleStorageSpec : CompilationModel := {
  name := "SimpleStorage"
  fields := [{ name := "storedData", ty := .uint256 }]
  constructor := none
  functions := [
    { name := "store"
      params := [{ name := "value", ty := .uint256 }]
      returnType := none
      body := [Stmt.setStorage "storedData" (Expr.param "value"), Stmt.stop]
    }
  ]
}
```

One logical spec can have many implementations, and one implementation can have multiple compiler backends, as long as the proof obligations hold.

## Verified Contracts

| Contract | Theorems | Description |
|----------|----------|-------------|
| SimpleStorage | 20 | Store/retrieve with roundtrip proof |
| Counter | 28 | Increment/decrement with wrapping, composition proofs |
| SafeCounter | 25 | Overflow/underflow revert proofs |
| Owned | 23 | Access control and ownership transfer |
| OwnedCounter | 48 | Cross-pattern composition, lockout proofs |
| Ledger | 33 | Deposit/withdraw/transfer with balance conservation |
| SimpleToken | 61 | Mint/transfer, supply conservation, storage isolation |
| ERC20 | 19 | Foundation scaffold with initial spec/read-state proofs |
| ERC721 | 11 | Foundation scaffold with token ownership/approval proof baseline |
| ReentrancyExample | 4 | Reentrancy vulnerability vs safe withdrawal |

**Unverified examples**:
- [CryptoHash](Verity/Examples/CryptoHash.lean) demonstrates external library linking via the [Linker](Compiler/Linker.lean) but has no specs or proofs.
- [ERC20](Verity/Examples/ERC20.lean) is a new foundation scaffold with executable logic plus formal spec/invariant modules in `Verity/Specs/ERC20/`, with proof development tracked in [#69](https://github.com/Th0rgal/verity/issues/69).
- [ERC721](Verity/Examples/ERC721.lean) is a new foundation scaffold with executable logic plus formal spec/invariant modules in `Verity/Specs/ERC721/`, with proof development tracked in [#73](https://github.com/Th0rgal/verity/issues/73).

### Using External Libraries (Linker)

Verity supports linking external Yul libraries (e.g., cryptographic libraries) to your verified contracts. Prove your contract logic with simple placeholders, then swap in production implementations at compile time.

**The pattern:**
1. Write a simple Lean placeholder (e.g., `add a b` for a hash function)
2. Add an `externalCall` in your compilation model (`CompilationModel`/`CompilationModel`)
3. Link your production Yul library at compile time

```bash
# Compile with external libraries
lake exe verity-compiler \
    --link examples/external-libs/PoseidonT3.yul \
    --link examples/external-libs/PoseidonT4.yul \
    -o compiler/yul
```

**Minimal example:**

```lean
-- 1. Lean placeholder (for proofs)
def myHash (a b : Uint256) : Contract Uint256 := do
  return (a + b)  -- simple placeholder

-- 2. CompilationModel/CompilationModel calls the real library
Stmt.letVar "h" (Expr.externalCall "myHash" [Expr.param "a", Expr.param "b"])

-- 3. Compile with: lake exe verity-compiler --link examples/external-libs/MyHash.yul
```

See [`examples/external-libs/README.md`](examples/external-libs/README.md) for a step-by-step guide and [`docs-site/content/guides/linking-libraries.mdx`](docs-site/content/guides/linking-libraries.mdx) for the full documentation.

### External Call Modules

Verity's restricted DSL prevents raw external calls for safety. Instead, call patterns are packaged as **External Call Modules (ECMs)** — reusable, typed, auditable Lean structures that the compiler can plug in without modification. Standard modules for ERC-20, EVM precompiles, and callbacks ship in [`Compiler/Modules/`](Compiler/Modules/README.md). Third parties can publish their own as separate Lean packages. See [`docs/EXTERNAL_CALL_MODULES.md`](docs/EXTERNAL_CALL_MODULES.md) for the full guide.

431 theorems across 11 categories, all fully proven. 404 Foundry tests across 35 test suites. 250 covered by property tests (58% coverage, 181 proof-only exclusions). 1 documented axiom. 0 `sorry` — Ledger sum proofs completed in Conservation.lean ([#65](https://github.com/Th0rgal/verity/issues/65)).

## What's Verified

- **Layer 1 (per contract)**: EDSL behavior matches its compilation model (`CompilationModel`/`CompilationModel`).
- **Layer 2 (framework)**: compilation model → `IR` preserves behavior.
- **Layer 3 (framework)**: `IR -> Yul` preserves behavior.
- **Proof-chain note**: the `EDSL -> CompilationModel (CompilationModel) -> IR -> Yul` chain is verified with 1 axiom.
- **Trusted boundary**: `solc` compiles Yul to bytecode correctly.

**Layer-1 hybrid note**: Layer 1 currently uses a hybrid strategy — generated `EDSL -> CompilationModel` proofs for the supported subset, plus a manual escape hatch for advanced constructs. See [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) for details.

See [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) for trust boundaries, [`AXIOMS.md`](AXIOMS.md) for axiom documentation, and [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) for full status.

## How Verity Compares

Smart contract verification is an active field with already strong tooling today. Verity uses Lean 4 as an interactive theorem prover across the full compilation pipeline. This gives unbounded proofs with no loop-depth limits at the cost of more effort per property.

| | Certora | Halmos | Runtime Monitoring | Verity |
|---|---|---|---|---|
| **Approach** | Bounded model checking via custom prover | Symbolic execution via Z3 | Runtime assertions | Interactive theorem proving (Lean 4) |
| **Strengths** | Excellent automation, large ecosystem, battle-tested on production protocols | Free and open-source, integrates with Foundry, good for finding concrete bugs | Zero overhead at deploy time (checks only in testing), catches real transactions | Unbounded proofs (no loop depth limits), verified compiler, machine-checked by Lean kernel |
| **Trade-offs** | Bounded (may miss bugs beyond loop unrolling depth), closed-source prover | Bounded (path explosion on complex contracts), depends on Z3 solver completeness | Cannot prove absence of bugs, only detects them at runtime | Higher effort per property today, smaller ecosystem, requires Lean expertise |
| **Compiler trust** | Trusts Solidity compiler entirely | Trusts Solidity compiler entirely | N/A | Verifies 3 compilation layers; trusts only `solc` Yul-to-bytecode |
| **Best for** | Production protocol audits at scale | Bug-finding in Foundry-based workflows | Monitoring deployed contracts | High-assurance contracts where unbounded correctness guarantees matter |

Verity is not a replacement for any of these tools. For most teams, Certora or Halmos will be the practical choice because their automation is far ahead. Verity is for cases where you need mathematical certainty that a property holds for all possible inputs and all possible execution paths, and you are willing to invest the proof engineering effort to get there.

The effort gap is narrowing. Much of this repository was built with heavy AI assistance, with every proof machine-checked by Lean regardless of origin. As agents improve at interactive theorem proving, the cost of writing unbounded proofs will continue to drop, potentially making full formal verification practical for a much wider range of contracts.

## Getting Started

<details>
<summary><strong>Building</strong></summary>

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env

# Build the project
lake build

# Build and run the compiler
lake build verity-compiler
lake exe verity-compiler

# Run Foundry tests (requires difftest profile for FFI access)
FOUNDRY_PROFILE=difftest forge test
```

</details>

<details>
<summary><strong>Testing</strong></summary>

**Foundry tests** (404 tests) validate EDSL = Yul = EVM execution:

```bash
FOUNDRY_PROFILE=difftest forge test                                          # run all
FOUNDRY_PROFILE=difftest forge test -vvv                                     # verbose
FOUNDRY_PROFILE=difftest forge test --match-path test/PropertyCounter.t.sol  # specific file
```

> **Note**: Tests require `FOUNDRY_PROFILE=difftest` because they compile Yul via `solc` using `vm.ffi()`. The default profile has FFI disabled for security. See [foundry.toml](foundry.toml).

**Differential tests** compare EDSL interpreter output against Solidity-compiled EVM to catch compiler bugs. See [`test/README.md`](test/README.md).

</details>

<details>
<summary><strong>Adding a contract</strong></summary>

```bash
python3 scripts/generate_contract.py MyContract
python3 scripts/generate_contract.py MyToken --fields "balances:mapping,totalSupply:uint256,owner:address"
```

This scaffolds the full file layout:

1. **Implementation** - `Verity/Examples/<Name>.lean`
2. **Spec** - `Verity/Specs/<Name>/Spec.lean`
3. **Invariants** - `Verity/Specs/<Name>/Invariants.lean`
4. **Layer 2 Proof Re-export** - `Verity/Specs/<Name>/Proofs.lean`
5. **Basic Proofs** - `Verity/Proofs/<Name>/Basic.lean`
6. **Correctness Proofs** - `Verity/Proofs/<Name>/Correctness.lean`
7. **Tests** - `test/Property<Name>.t.sol`

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for conventions and workflow.

</details>

<details>
<summary><strong>Linking external libraries</strong></summary>

Use the Linker to integrate production cryptographic libraries (Poseidon, Groth16, etc.) with formally verified contract logic:

1. **Write a placeholder** in your Lean contract:
```lean
-- Placeholder: simple addition for proofs
def hash (a b : Uint256) : Contract Uint256 := do
  return add a b
```

2. **Add external call** in `Compiler/Specs.lean`:
```lean
Stmt.letVar "h" (Expr.externalCall "poseidonHash" [Expr.param "a", Expr.param "b"])
```

3. **Compile with linking**:
```bash
lake exe verity-compiler --link examples/external-libs/MyHash.yul -o compiler/yul
```

The compiler validates function names, arities, and prevents name collisions. See [`examples/external-libs/README.md`](examples/external-libs/README.md) for detailed guidance.

</details>

## Documentation

**Full documentation**: [verity.thomas.md](https://verity.thomas.md/) — guides, DSL reference, examples, and verification details.

| | |
|---|---|
| [Docs Site](https://verity.thomas.md/) | Full documentation site with guides and DSL reference |
| [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) | What's verified, what's trusted, trust reduction roadmap |
| [`AXIOMS.md`](AXIOMS.md) | All axioms with soundness justifications (1 remaining) |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Coding conventions, workflow, PR guidelines |
| [`docs/EXTERNAL_CALL_MODULES.md`](docs/EXTERNAL_CALL_MODULES.md) | ECM framework: writing and using external call modules |
| [`docs/SOLIDITY_PARITY_PROFILE.md`](docs/SOLIDITY_PARITY_PROFILE.md) | Backend profile levels and parity scope |
| [`docs/PARITY_PACKS.md`](docs/PARITY_PACKS.md) | Planned parity-pack format, lifecycle, and CI contract |
| [`docs/REWRITE_RULES.md`](docs/REWRITE_RULES.md) | Planned proof-carrying subtree rewrite model |
| [`docs/IDENTITY_CHECKER.md`](docs/IDENTITY_CHECKER.md) | Planned AST identity checker workflow and report schema |
| [`docs/ROADMAP.md`](docs/ROADMAP.md) | Verification progress, planned features |
| [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) | Per-theorem status |

## License

MIT - See [LICENSE.md](LICENSE.md) for details.
