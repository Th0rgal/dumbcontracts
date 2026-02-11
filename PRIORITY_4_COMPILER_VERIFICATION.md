# Priority 4: Compiler Verification — Proving Compiler Correctness

**Status**: 🚧 IN PROGRESS (infrastructure planning phase)
**Goal**: Formally prove that compiled EVM bytecode behaves exactly like the EDSL specification.

---

## Overview

With priorities 0-3 complete (EVM compatibility, generic compilation, differential testing, property extraction), we now have:

✅ **High empirical confidence**:
- 70,000+ differential tests (zero mismatches)
- 264/264 Foundry tests passing
- 252 property tests from theorems

🎯 **Next step**: Formal proof that the compiler is correct

---

## Verification Strategy: Layered Approach

We prove correctness in **3 layers**, each building on the previous:

```
EDSL (verified)
  ↓ [Layer 1: Spec Correctness]
ContractSpec (declarative DSL)
  ↓ [Layer 2: IR Generation]
IR (intermediate representation)
  ↓ [Layer 3: Yul Generation]
Yul
  ↓ [Trust solc]
EVM Bytecode
```

**End-to-end theorem**: `compiled_bytecode ≡ EDSL_semantics` (modulo solc trust)

---

## Layer 1: EDSL ≡ ContractSpec (Specification Correctness)

### Current State
- EDSL contracts in `DumbContracts/Examples/*.lean` (7 contracts, all verified)
- ContractSpec DSL in `Compiler/ContractSpec.lean` (declarative language)
- Specs in `Compiler/Specs.lean` (manually written for each contract)

### What to Prove
Each `ContractSpec` in `Compiler/Specs.lean` accurately represents its corresponding EDSL contract.

**Example theorem** (SimpleStorage):
```lean
-- In Compiler/Proofs/SpecCorrectness/SimpleStorage.lean

theorem simpleStorageSpec_correct :
  ∀ (initialState : State) (tx : Transaction),
    interpretEDSL SimpleStorage initialState tx =
    interpretSpec simpleStorageSpec initialState tx := by
  intro initialState tx
  cases tx.function
  case store =>
    -- Prove store function equivalence
    simp [interpretEDSL, interpretSpec]
    -- Use existing SimpleStorage.store_correct theorem
    sorry
  case retrieve =>
    -- Prove retrieve function equivalence
    simp [interpretEDSL, interpretSpec]
    -- Use existing SimpleStorage.retrieve_correct theorem
    sorry
```

### Tasks

**1. Define `interpretSpec` function** (`Compiler/Proofs/SpecInterpreter.lean`):
```lean
def interpretSpec (spec : ContractSpec) (state : State) (tx : Transaction) : Result :=
  match findFunction spec tx.functionName with
  | none => Result.error "function not found"
  | some func =>
      -- Execute function body using spec semantics
      executeSpecFunction func state tx.sender tx.args
```

**2. Write 7 specification correctness proofs**:
- [ ] `Compiler/Proofs/SpecCorrectness/SimpleStorage.lean` (easiest, start here)
- [ ] `Compiler/Proofs/SpecCorrectness/Counter.lean`
- [ ] `Compiler/Proofs/SpecCorrectness/Owned.lean`
- [ ] `Compiler/Proofs/SpecCorrectness/SafeCounter.lean`
- [ ] `Compiler/Proofs/SpecCorrectness/OwnedCounter.lean`
- [ ] `Compiler/Proofs/SpecCorrectness/Ledger.lean`
- [ ] `Compiler/Proofs/SpecCorrectness/SimpleToken.lean` (hardest)

**3. Leverage existing proofs**:
- We already have 252 EDSL correctness theorems
- Reuse these in spec correctness proofs
- Example: `SimpleStorage.store_correct` can be used in `simpleStorageSpec_correct`

### Estimated Effort
- **SpecInterpreter.lean**: 100-200 lines (1-2 days)
- **SimpleStorage proof**: 50-100 lines (1 day, template for others)
- **Other 6 proofs**: 300-600 lines total (3-5 days)
- **Total**: ~1 week

---

## Layer 2: ContractSpec → IR (Code Generation Correctness)

### Current State
- IR definition in `Compiler/IR.lean`
- Code generation in `Compiler/ContractSpec.lean` (toIR functions)
- Automatic translation from specs to IR

### What to Prove
The `toIR` function preserves semantics: running IR gives same results as running the spec.

**Theorem**:
```lean
-- In Compiler/Proofs/IRGeneration/Preservation.lean

theorem toIR_preserves_semantics (spec : ContractSpec) :
  ∀ (state : State) (tx : Transaction),
    interpretIR (spec.toIR) state tx =
    interpretSpec spec state tx := by
  sorry
```

### Approach

**1. Define IR semantics** (`Compiler/Proofs/IRSemantics.lean`):
```lean
def interpretIR (ir : IRContract) (state : State) (tx : Transaction) : Result :=
  match findIRFunction ir tx.functionName with
  | none => Result.error "function not found"
  | some irFunc =>
      executeIRFunction irFunc state tx.sender tx.args
```

**2. Prove translation correctness for each construct**:

a) **Expressions** (`Compiler/Proofs/IRGeneration/Expr.lean`):
```lean
theorem exprToIR_correct (e : Expr) (env : Env) :
  evalIR (exprToIR e) env = evalSpec e env
```

Examples:
- `Expr.literal n` → `IRExpr.lit n`
- `Expr.param "x"` → `IRExpr.param 0` (name → index)
- `Expr.storage "count"` → `IRExpr.sload 0` (name → slot)
- `Expr.add a b` → `IRExpr.add (toIR a) (toIR b)`

b) **Statements** (`Compiler/Proofs/IRGeneration/Stmt.lean`):
```lean
theorem stmtToIR_correct (s : Stmt) (state : State) :
  execIR (stmtToIR s) state = execSpec s state
```

Examples:
- `Stmt.setStorage "count" e` → `IRStmt.sstore 0 (toIR e)`
- `Stmt.require cond msg` → `IRStmt.require (toIR cond) msg`
- `Stmt.return e` → `IRStmt.return (toIR e)`

c) **Functions** (`Compiler/Proofs/IRGeneration/Function.lean`):
```lean
theorem functionToIR_correct (f : Function) :
  runIR (functionToIR f) = runSpec f
```

**3. Compose into full preservation theorem**:
Use structural induction on contract spec to prove full equivalence.

### Challenges

- **Storage slot inference**: Prove slot assignment matches spec names
- **Parameter indexing**: Prove name→index mapping is correct
- **Constructor args**: Prove bytecode arg loading works
- **Mapping access**: Prove keccak256 slot computation is correct

### Estimated Effort
- **IR semantics**: 200-300 lines (2-3 days)
- **Expression proofs**: 200-400 lines (2-3 days)
- **Statement proofs**: 200-400 lines (2-3 days)
- **Function proofs**: 100-200 lines (1-2 days)
- **Full theorem**: 100-200 lines (1-2 days)
- **Total**: ~2 weeks

---

## Layer 3: IR → Yul (Lowering Correctness)

### Current State
- Yul generation in `Compiler/Codegen.lean`
- Generates Yul code from IR
- Works for all 7 contracts (264 tests passing)

### What to Prove
Yul codegen preserves IR semantics.

**Theorem**:
```lean
-- In Compiler/Proofs/YulGeneration/Preservation.lean

theorem yulCodegen_preserves_semantics (ir : IRContract) :
  ∀ (state : State) (tx : Transaction),
    interpretYul (generateYul ir) state tx =
    interpretIR ir state tx := by
  sorry
```

### Approach

**1. Define Yul semantics** (or import from existing work):

**Option A**: Use existing verified Yul semantics
- Check if Yul has been formalized (e.g., in Coq/Lean EVM verifiers)
- Import and adapt for our needs

**Option B**: Define simplified Yul subset
```lean
-- In Compiler/Proofs/YulSemantics.lean

inductive YulStmt
  | let_ : String → YulExpr → YulStmt
  | assign : String → YulExpr → YulStmt
  | if_ : YulExpr → List YulStmt → YulStmt
  | sstore : YulExpr → YulExpr → YulStmt
  | return_ : YulExpr → YulExpr → YulStmt
  | revert_ : YulExpr → YulExpr → YulStmt
  -- etc.

def interpretYul (code : YulCode) (state : State) (tx : Transaction) : Result :=
  -- Execute Yul statements
  sorry
```

**2. Prove codegen correctness**:

a) **Expression codegen** (`Compiler/Proofs/YulGeneration/Expr.lean`):
```lean
theorem exprCodegen_correct (e : IRExpr) (env : YulEnv) :
  evalYul (codegenExpr e) env = evalIR e env
```

b) **Statement codegen** (`Compiler/Proofs/YulGeneration/Stmt.lean`):
```lean
theorem stmtCodegen_correct (s : IRStmt) (state : YulState) :
  execYul (codegenStmt s) state = execIR s state
```

c) **Function codegen** (`Compiler/Proofs/YulGeneration/Function.lean`):
```lean
theorem functionCodegen_correct (f : IRFunction) :
  runYul (codegenFunction f) = runIR f
```

**3. Prove dispatch correctness**:
```lean
theorem selectorDispatch_correct (functions : List IRFunction) :
  -- Prove selector-based dispatch matches function calls
  sorry
```

### Challenges

- **Yul semantics complexity**: Yul is low-level (stack machine model)
- **Memory layout**: Prove memory allocation doesn't collide
- **Calldata layout**: Prove ABI encoding/decoding is correct
- **Selector dispatch**: Prove switch statement matches selectors

### Estimated Effort
- **Yul semantics** (if defining): 400-600 lines (3-5 days)
- **Expression codegen proofs**: 200-300 lines (2-3 days)
- **Statement codegen proofs**: 300-500 lines (3-4 days)
- **Function/dispatch proofs**: 200-400 lines (2-3 days)
- **Full theorem**: 100-200 lines (1-2 days)
- **Total**: ~2-3 weeks

**Alternative**: If we find existing Yul semantics, could save 1-2 weeks.

---

## Layer 4: Yul → EVM Bytecode (Trust Assumption)

### Approach
We **do NOT verify solc**. Instead:

1. **Document trust assumption**:
```lean
-- In Compiler/Proofs/TrustAssumptions.lean

axiom solc_correct :
  ∀ (yul : YulCode) (state : EVMState) (tx : EVMTransaction),
    executeEVM (solc.compile yul) state tx =
    interpretYul yul state tx
```

2. **Justify with empirical evidence**:
- 70,000+ differential tests (EVM execution vs EDSL)
- Zero mismatches
- High confidence that solc is correct for our Yul subset

3. **Document in paper/docs**:
- Solc is mature, widely used, heavily tested
- Our Yul is simple (no complex features)
- Differential testing validates this assumption

---

## End-to-End Theorem

**Final result** (combine all layers):

```lean
-- In Compiler/Proofs/EndToEnd.lean

theorem compiler_correct (contract : EDSLContract) (spec : ContractSpec) :
  spec_represents contract spec →
  ∀ (state : State) (tx : Transaction),
    interpretEDSL contract state tx =
    interpretYul (generateYul (spec.toIR)) state tx := by
  intro h_spec state tx
  calc interpretEDSL contract state tx
      = interpretSpec spec state tx := by apply specCorrectness h_spec
    _ = interpretIR (spec.toIR) state tx := by apply toIR_preserves_semantics
    _ = interpretYul (generateYul (spec.toIR)) state tx := by apply yulCodegen_preserves_semantics
```

**With solc trust assumption**, this gives:
```lean
theorem compiler_correct_with_solc (contract : EDSLContract) (spec : ContractSpec) :
  spec_represents contract spec →
  ∀ (state : State) (tx : Transaction),
    interpretEDSL contract state tx =
    executeEVM (solc.compile (generateYul (spec.toIR))) state tx := by
  intro h_spec state tx
  rw [← solc_correct]  -- Use trust assumption
  apply compiler_correct h_spec
```

**Interpretation**: Compiled bytecode behaves exactly like verified EDSL spec (modulo solc trust).

---

## Timeline Estimate

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| **Phase 1**: Infrastructure | 1 week | SpecInterpreter, IRSemantics, directory setup |
| **Phase 2**: Layer 1 proofs | 1-2 weeks | 7 spec correctness theorems |
| **Phase 3**: Layer 2 proofs | 2-3 weeks | IR generation preservation |
| **Phase 4**: Layer 3 proofs | 2-3 weeks | Yul codegen preservation |
| **Phase 5**: End-to-end | 1 week | Composed theorem, documentation |
| **Phase 6**: CI integration | 1 week | Automated verification in CI |
| **Total** | **8-11 weeks** | Fully verified compiler |

---

## How to Start

### Step 1: Create Directory Structure
```bash
mkdir -p Compiler/Proofs/SpecCorrectness
mkdir -p Compiler/Proofs/IRGeneration
mkdir -p Compiler/Proofs/YulGeneration
```

### Step 2: Define Interpreters
Create `Compiler/Proofs/SpecInterpreter.lean`:
```lean
import Compiler.ContractSpec
import DumbContracts.Core

namespace Compiler.Proofs

def interpretSpec (spec : ContractSpec) (state : State) (tx : Transaction) : Result :=
  sorry  -- To be implemented

end Compiler.Proofs
```

Create `Compiler/Proofs/IRSemantics.lean`:
```lean
import Compiler.IR
import DumbContracts.Core

namespace Compiler.Proofs

def interpretIR (ir : IRContract) (state : State) (tx : Transaction) : Result :=
  sorry  -- To be implemented

end Compiler.Proofs
```

### Step 3: Start with SimpleStorage
Create `Compiler/Proofs/SpecCorrectness/SimpleStorage.lean`:
```lean
import Compiler.Specs
import Compiler.Proofs.SpecInterpreter
import DumbContracts.Examples.SimpleStorage
import DumbContracts.Proofs.SimpleStorage.Correctness

namespace Compiler.Proofs.SpecCorrectness

theorem simpleStorageSpec_correct :
  ∀ (initialState : State) (tx : Transaction),
    DumbContracts.Examples.SimpleStorage.run initialState tx =
    Compiler.Proofs.interpretSpec Compiler.Specs.simpleStorageSpec initialState tx := by
  sorry  -- Start proving!

end Compiler.Proofs.SpecCorrectness
```

### Step 4: Build incrementally
- Get SimpleStorage proof working first
- Use it as template for other 6 contracts
- Then move to Layer 2 (IR generation)

---

## Success Criteria

✅ **Layer 1 complete** when:
- `interpretSpec` implemented and tested
- All 7 spec correctness theorems proven
- `lake build Compiler/Proofs/SpecCorrectness` has zero `sorry`

✅ **Layer 2 complete** when:
- `interpretIR` implemented
- Expression, statement, function translation proofs done
- `toIR_preserves_semantics` theorem proven
- `lake build Compiler/Proofs/IRGeneration` has zero `sorry`

✅ **Layer 3 complete** when:
- Yul semantics defined (or imported)
- Codegen correctness proofs done
- `yulCodegen_preserves_semantics` theorem proven
- `lake build Compiler/Proofs/YulGeneration` has zero `sorry`

✅ **Compiler verification complete** when:
- All 3 layers proven
- End-to-end theorem composed
- Trust assumptions documented
- `lake build Compiler/Proofs` has zero `sorry`
- Verification integrated into CI

---

## References

- **EDSL Proofs**: `DumbContracts/Proofs/` - 252 theorems to leverage
- **ContractSpec DSL**: `Compiler/ContractSpec.lean` - What we're proving correct
- **Specs**: `Compiler/Specs.lean` - 7 specs to verify
- **IR Definition**: `Compiler/IR.lean` - IR semantics needed
- **Codegen**: `Compiler/Codegen.lean` - Yul generation to verify

---

## Next Steps (This Week)

1. ✅ Update ROADMAP.md with verification plan (DONE)
2. 🔲 Create `Compiler/Proofs/` directory structure
3. 🔲 Implement `interpretSpec` function
4. 🔲 Start SimpleStorage spec correctness proof
5. 🔲 Get feedback on proof approach

**Goal**: Have Layer 1 infrastructure ready and first proof started by end of week.
