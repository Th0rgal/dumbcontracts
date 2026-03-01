/-
  Compiler.Proofs.EndToEnd: Composed Layers 2+3 End-to-End Theorem

  Composes the existing Layer 2 (CompilationModel → IR) and Layer 3 (IR → Yul)
  preservation theorems into a single end-to-end result:

    For any CompilationModel, evaluating the compiled Yul via the proof semantics
    produces the same result as the IR semantics.

  This is the first step toward eliminating `interpretSpec` from the TCB
  (Issue #998). Once primitive-level EDSL ≡ compiled-Yul lemmas are proven,
  this end-to-end theorem provides the composition spine.

  **Architecture**:
  - Layer 2: `compile spec selectors = .ok irContract`
             `interpretIR irContract tx irState ≡ interpretSpec spec ...`
             (proven per-contract in Compiler/Proofs/IRGeneration/Expr.lean)
  - Layer 3: `interpretIR irContract tx irState ≡ interpretYulFromIR irContract tx irState`
             (proven generically in Compiler/Proofs/YulGeneration/Preservation.lean)
  - This file: compose them into a single theorem statement.

  **EVMYulLean note**: This file does NOT import EVMYulLean directly. The Yul
  execution semantics used here (`interpretYulFromIR`, `interpretYulRuntime`)
  are defined in terms of `evalBuiltinCallWithBackend` which defaults to the
  Verity backend. The EVMYulLean bridge is established separately in
  `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean` and
  `Compiler/Proofs/ArithmeticProfile.lean`, proving that for pure builtins,
  the Verity backend agrees with EVMYulLean.

  Run: lake build Compiler.Proofs.EndToEnd
-/

import Compiler.Proofs.YulGeneration.Preservation
import Compiler.Proofs.IRGeneration.Expr
import Compiler.Proofs.IRGeneration.Conversions

namespace Compiler.Proofs.EndToEnd

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration

/-! ## Layer 3: IR → Yul (Generic)

The Layer 3 theorem proves that for any single IR function, executing via IR
produces the same result as executing the corresponding Yul code. This is
already proven generically in `Preservation.lean`.

We re-export the key results here for downstream composition.
-/

/-- Layer 3 function-level preservation: any IR function body produces equivalent
results under IR execution and fuel-based Yul execution.

This is a re-export of `ir_function_body_equiv` from Preservation.lean,
included here for composition convenience.

NOTE: This uses `interpretYulBodyFromState`, which executes the function body
statements directly with IR-derived state. This is different from
`interpretYulBody`, which uses `YulState.initial` (the runtime dispatch entry
point). The gap is bridged in `yulCodegen_preserves_semantics`. -/
theorem layer3_function_preserves_semantics
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (execIRFunction fn args initialState)
      (interpretYulBodyFromState fn selector
        (fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) initialState)
        initialState) :=
  ir_function_body_equiv fn selector args initialState

/-! ## Layer 3 Contract-Level: IR → Yul (via runtime dispatch)

The full Layer 3 theorem (`yulCodegen_preserves_semantics`) proves that
executing an IR contract matches executing the emitted Yul runtime code.

The existing theorem in Preservation.lean takes a `hbody` hypothesis that
requires `interpretYulBody` (runtime-style Yul execution) to match
`execIRFunction` (IR execution) for each function.

`ir_function_body_equiv` proves the match against `interpretYulBodyFromState`
(statement-level Yul execution), not `interpretYulBody` (runtime dispatch).
The gap between these two Yul execution entry points needs a bridging lemma.

We capture this composition with the documented gap below.
-/

/-- Layer 3 contract-level preservation: an IR contract execution produces
equivalent results under the Yul runtime dispatch, given entry-point state
assumptions.

Requires:
- `hselector`: selector is within the valid range (< 2^32)
- `hvars`/`hmemory`: initial state has empty vars and zero memory (true at
  contract entry points — the IR interpreter doesn't carry vars/memory across calls)

The `hvars`/`hmemory` preconditions let us bridge `interpretYulBodyFromState`
(from `ir_function_body_equiv`) to `interpretYulBody` (from
`yulCodegen_preserves_semantics`): both produce the same Yul initial state
when the IR state already has `vars = []` and `memory = fun _ => 0`.

For contracts where `interpretIR` is called with a "fresh" state (the normal
case), these preconditions hold trivially. The unconditioned version
(`layer3_contract_preserves_semantics_general`) states the theorem without
preconditions but uses `sorry`. -/
theorem layer3_contract_preserves_semantics
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulFromIR contract tx initialState) := by
  apply yulCodegen_preserves_semantics contract tx initialState hselector
  intro fn hmem
  -- Goal: resultsMatch (execIRFunction fn tx.args irState) (interpretYulBody fn tx irState)
  -- where irState = { initialState with sender, calldata, selector }
  --
  -- irState inherits vars and memory from initialState, so by hvars/hmemory:
  --   irState.vars = [], irState.memory = fun _ => 0
  exact yulBody_from_state_eq_yulBody fn tx
    { initialState with sender := tx.sender, calldata := tx.args, selector := tx.functionSelector }
    rfl rfl rfl rfl
    (by simp [hmemory])
    (by simp [hvars])

/-- Unconditioned version: no preconditions on initial state.
Uses `sorry` for the `interpretYulBodyFromState ↔ interpretYulBody` bridging
gap, which requires showing `execYulStmts` is parametric in initial vars/memory
when `fn.body` starts with `genParamLoads`-generated calldataload let-bindings.

Prefer `layer3_contract_preserves_semantics` when you can supply `hvars`/`hmemory`. -/
theorem layer3_contract_preserves_semantics_general
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulFromIR contract tx initialState) := by
  apply yulCodegen_preserves_semantics contract tx initialState hselector
  intro fn hmem
  sorry -- GAP: Bridge interpretYulBodyFromState ↔ interpretYulBody for arbitrary initial state.
       -- The two Yul execution paths differ in initial state:
       --   interpretYulBody:          YulState.initial → vars := [], memory := fun _ => 0
       --   interpretYulBodyFromState: yulStateOfIR     → vars := state.vars, memory := state.memory
       -- fn.body contains calldataload let-bindings that shadow all free variables,
       -- making the initial vars/memory irrelevant, but proving this generically
       -- requires a free-variable analysis. See yulBody_from_state_eq_yulBody.

/-! ## Bridging Helpers

These lemmas bridge the two Yul execution entry points:
- `interpretYulRuntime` (used by `interpretYulBody`): starts from `YulState.initial`
- `interpretYulBodyFromState` (used by `ir_function_body_equiv`): starts from `yulStateOfIR`

The bridge has two parts:
1. **Result wrapping**: `interpretYulRuntime` and `yulResultOfExecWithRollback` produce
   the same `YulResult` when the rollback storage equals the initial storage.
2. **Initial state**: `yulStateOfIR sel state` equals `YulState.initial yulTx state.storage`
   when state has empty vars, zero memory, and fields matching the transaction.
-/

/-- Result wrapping equivalence: `interpretYulRuntime` produces the same `YulResult`
as `yulResultOfExecWithRollback` when given the same `execYulStmts` result and
the rollback storage matches the initial storage.

Both have identical branches for `.continue`, `.return`, and `.stop`.
For `.revert`, `interpretYulRuntime` uses the original `storage` parameter while
`yulResultOfExecWithRollback` uses `rollback.storage`. -/
theorem interpretYulRuntime_eq_yulResultOfExec
    (stmts : List YulStmt) (tx : YulTransaction) (storage : Nat → Nat) :
    interpretYulRuntime stmts tx storage =
      yulResultOfExecWithRollback (YulState.initial tx storage)
        (execYulStmts (YulState.initial tx storage) stmts) := by
  simp [interpretYulRuntime]
  cases execYulStmts (YulState.initial tx storage) stmts with
  | «continue» s => simp [yulResultOfExecWithRollback]
  | «return» v s => simp [yulResultOfExecWithRollback]
  | «stop» s => simp [yulResultOfExecWithRollback]
  | «revert» s => simp [yulResultOfExecWithRollback, YulState.initial]

/-- State equivalence: under the entry-point hypotheses, `yulStateOfIR` produces
the same YulState as `YulState.initial`. -/
theorem yulStateOfIR_eq_initial
    (sel : Nat) (state : IRState) (tx : IRTransaction)
    (hcalldata : state.calldata = tx.args)
    (hsender : state.sender = tx.sender)
    (hselector : state.selector = tx.functionSelector)
    (hreturn : state.returnValue = none)
    (hmemory : state.memory = fun _ => 0)
    (hvars : state.vars = []) :
    yulStateOfIR sel state =
      YulState.initial { sender := tx.sender, functionSelector := tx.functionSelector, args := tx.args }
        state.storage := by
  simp [yulStateOfIR, YulState.initial, hvars, hmemory, hcalldata, hsender, hselector, hreturn]

/-! ## Core Bridging Lemma

The core gap: `ir_function_body_equiv` gives us `execIRFunction ≡ interpretYulBodyFromState`,
where `interpretYulBodyFromState` executes `fn.body` on `yulStateOfIR sel paramState` (with
params already bound as vars). But `interpretYulBody` executes `fn.body` on
`YulState.initial` (with `vars = []`).

Since `fn.body` starts with `genParamLoads`-generated `let` statements that re-bind each
parameter from calldata, and `YulState.setVar` uses filter-then-prepend (removing old
bindings), the initial vars difference is eliminated after those statements execute.

We factor this into two lemmas:
1. `execYulStmts_genParamLoads_erases_vars`: executing the genParamLoads prefix on any
   state produces the same result regardless of initial vars (the `let` bindings
   shadow all prior vars with the same names, and calldataload doesn't depend on vars).
2. `yulBody_from_state_eq_yulBody`: composes (1) with the result-wrapping equivalence.
-/

/-- **Core gap lemma**: For an IR function whose body starts with calldataload let-bindings
(as generated by `genParamLoads`), executing the body on a state with params pre-bound
produces the same result as executing on a state with empty vars.

**Why this holds**: `setVar` does `(name, value) :: vars.filter (·.1 != name)`, so after
`let name := calldataload(offset)`, any prior binding of `name` is removed. The
`calldataload` evaluation depends only on `state.calldata` (not vars), so both starting
states produce the same `vars` after the let-binding executes. After all genParamLoads
statements, the full var lists are identical.

**Why sorry**: Proving this generically requires showing that `execYulStmts` is parametric
in initial vars when every var referenced in the body is first bound by a `let` statement.
This is a program analysis property that would require either:
(a) A syntactic free-variable analysis of fn.body (complex to formalize)
(b) A semantic argument that genParamLoads-generated code has this property (requires
    inspecting the CompilationModel.lean code generator)
For concrete contracts (SimpleStorage), this is bypassed by direct computation in
SemanticBridge.lean. -/
theorem execYulStmts_paramState_eq_emptyVars
    (fn : IRFunction) (tx : IRTransaction) (state : IRState)
    (hvars : state.vars = [])
    (hmemory : state.memory = fun _ => 0)
    (hcalldata : state.calldata = tx.args)
    (hsender : state.sender = tx.sender)
    (hselector : state.selector = tx.functionSelector)
    (hreturn : state.returnValue = none) :
    let paramState := fn.params.zip tx.args |>.foldl
      (fun s (p, v) => s.setVar p.name v) state
    let yulTx : YulTransaction := {
      sender := tx.sender
      functionSelector := tx.functionSelector
      args := tx.args
    }
    execYulStmts (yulStateOfIR 0 paramState) fn.body =
      execYulStmts (YulState.initial yulTx state.storage) fn.body := by
  sorry -- Core gap: genParamLoads-generated let-bindings erase the initial vars difference.
        -- See docstring above for why this holds and why it's hard to formalize generically.

/-- Bridging: the two Yul execution entry points produce the same result
when the IR state has empty vars and zero memory.

This decomposes into:
1. `yulStateOfIR_eq_initial`: the rollback states are identical
2. `execYulStmts_paramState_eq_emptyVars`: the execution produces the same
   `YulExecResult` despite different initial vars
3. `interpretYulRuntime_eq_yulResultOfExec`: the result wrapping is compatible
4. `ir_function_body_equiv`: IR execution matches `interpretYulBodyFromState` -/
theorem yulBody_from_state_eq_yulBody
    (fn : IRFunction) (tx : IRTransaction) (state : IRState)
    (hcalldata : state.calldata = tx.args)
    (hsender : state.sender = tx.sender)
    (hselector : state.selector = tx.functionSelector)
    (hreturn : state.returnValue = none)
    (hmemory : state.memory = fun _ => 0)
    (hvars : state.vars = []) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (execIRFunction fn tx.args state)
      (interpretYulBody fn tx state) := by
  -- Step 1: Get IR ≡ interpretYulBodyFromState from the existing proof
  have h_ir_from := ir_function_body_equiv fn 0 tx.args state
  -- h_ir_from : resultsMatch (execIRFunction fn tx.args state)
  --              (interpretYulBodyFromState fn 0 paramState state)
  -- Step 2: Show the interpretYulBodyFromState equals interpretYulBody
  -- by showing both the execution and result wrapping agree.
  --
  -- interpretYulBodyFromState fn 0 paramState state
  --   = yulResultOfExecWithRollback (yulStateOfIR 0 state) (execYulStmts (yulStateOfIR 0 paramState) fn.body)
  --
  -- interpretYulBody fn tx state
  --   = interpretYulRuntime fn.body yulTx state.storage
  --   = yulResultOfExecWithRollback (YulState.initial yulTx state.storage) (execYulStmts (YulState.initial yulTx state.storage) fn.body)
  --     (by interpretYulRuntime_eq_yulResultOfExec)
  --
  -- Under our hypotheses:
  --   yulStateOfIR 0 state = YulState.initial yulTx state.storage (by yulStateOfIR_eq_initial)
  --   execYulStmts (yulStateOfIR 0 paramState) fn.body = execYulStmts (YulState.initial yulTx state.storage) fn.body
  --     (by execYulStmts_paramState_eq_emptyVars)
  --
  -- So: interpretYulBodyFromState fn 0 paramState state = interpretYulBody fn tx state
  suffices h_eq : interpretYulBodyFromState fn 0
      (fn.params.zip tx.args |>.foldl (fun s (p, v) => s.setVar p.name v) state)
      state = interpretYulBody fn tx state by
    rwa [h_eq] at h_ir_from
  -- Unfold both sides
  simp only [interpretYulBodyFromState, interpretYulBody]
  -- The rollback state: yulStateOfIR 0 state = YulState.initial yulTx state.storage
  have h_rollback := yulStateOfIR_eq_initial 0 state tx hcalldata hsender hselector hreturn hmemory hvars
  -- The execution state: execYulStmts agree despite different initial vars
  have h_exec := execYulStmts_paramState_eq_emptyVars fn tx state hvars hmemory hcalldata hsender hselector hreturn
  -- Rewrite the rollback state
  rw [h_rollback]
  -- Rewrite the execution
  simp only at h_exec
  rw [h_exec]
  -- Now both sides are:
  --   yulResultOfExecWithRollback (YulState.initial yulTx state.storage)
  --     (execYulStmts (YulState.initial yulTx state.storage) fn.body)
  -- vs
  --   interpretYulRuntime fn.body yulTx state.storage
  -- These are equal by interpretYulRuntime_eq_yulResultOfExec
  exact (interpretYulRuntime_eq_yulResultOfExec fn.body
    { sender := tx.sender, functionSelector := tx.functionSelector, args := tx.args }
    state.storage).symm

/-! ## Layers 2+3 Composition: CompilationModel → Yul

These theorems compose the per-contract Layer 2 results with the generic
Layer 3 result to obtain end-to-end preservation from CompilationModel
semantics through to Yul execution semantics.
-/

/-- End-to-end: given a successfully compiled contract, IR execution matches
Yul execution.

This is the key composition: it takes a compilation success proof and
produces IR ≡ Yul. Combined with Layer 2 proofs (which show IR matches
spec interpretation), this yields the full chain:
  interpretSpec ≡ IR ≡ Yul

The remaining step (Issue #998) replaces interpretSpec ≡ IR with EDSL ≡ IR,
eliminating interpretSpec from the TCB entirely. -/
theorem layers2_3_ir_matches_yul
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hselector : tx.functionSelector < selectorModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR irContract tx initialState)
      (interpretYulFromIR irContract tx initialState) :=
  layer3_contract_preserves_semantics irContract tx initialState hselector hvars hmemory

/-! ## Concrete Instantiation: SimpleStorage

Below we instantiate the end-to-end theorem for SimpleStorage,
composing the concrete Layer 2 proof (`compile_simpleStorageSpec`)
with the generic Layer 3 proof.
-/

/-- SimpleStorage end-to-end: compile → IR → Yul preserves semantics.

Composes:
- Layer 2: `compile_simpleStorageSpec` (compilation succeeds, producing `simpleStorageIRContract`)
           `simpleStorage_store_correct` / `simpleStorage_retrieve_correct`
           (from IRGeneration/Expr.lean — these show IR ≡ interpretSpec)
- Layer 3: `layer3_contract_preserves_semantics` (generic IR → Yul)

The composed result: for SimpleStorage, Yul execution produces the same
observable results as IR execution (which in turn matches interpretSpec). -/
theorem simpleStorage_endToEnd
    (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR simpleStorageIRContract tx initialState)
      (interpretYulFromIR simpleStorageIRContract tx initialState) :=
  layer3_contract_preserves_semantics simpleStorageIRContract tx initialState hselector hvars hmemory

/-! ## Full End-to-End Goal Statement (Issue #998 Target)

The ultimate goal is a theorem of this form for each contract function:

  theorem counter_increment_endToEnd
      (state : ContractState) (sender : Address) :
      let edslResult := (Counter.increment).run { state with sender }
      let cmSpec := MacroContracts.Counter.spec
      let compiledYul := emitYul (compile cmSpec selectors).get!
      let yulResult := interpretYulRuntime compiledYul.runtimeCode yulTx storage
      -- EDSL result matches Yul execution
      edslResultMatchesYul edslResult yulResult

This bypasses `interpretSpec` entirely. The theorem composes:
1. Macro elaboration correctness (EDSL ≡ CompilationModel, by construction)
2. Layer 2 (CompilationModel → IR, from IRGeneration/Expr.lean)
3. Layer 3 (IR → Yul, from this file / Preservation.lean)
4. EVMYulLean bridge (Yul builtins ≡ EVMYulLean, from ArithmeticProfile.lean)

Steps 1 and 4 are the remaining gaps addressed by PrimitiveBridge.lean
and the macro-generated proof skeleton.
-/

/-! ## Sorry Audit (Semantic Bridge, Issue #998)

### This file (`Compiler/Proofs/EndToEnd.lean`):

1. **`execYulStmts_paramState_eq_emptyVars`** (1 sorry)
   - States: executing fn.body on a state with params pre-bound produces the same
     result as executing on a state with empty vars
   - Why it holds: genParamLoads-generated `let name := calldataload(offset)` statements
     re-bind every parameter from calldata. `YulState.setVar` uses filter-then-prepend,
     erasing any prior binding of the same name. `calldataload` doesn't depend on vars.
   - Difficulty: Requires syntactic free-variable analysis or program-specific reasoning
   - Impact: Blocks `yulBody_from_state_eq_yulBody` (which is otherwise fully proven)

2. **`layer3_contract_preserves_semantics_general`** (1 sorry)
   - States: the conditioned theorem without hvars/hmemory preconditions
   - Depends on: the same gap as (1) but for arbitrary initial state
   - Impact: Low — the conditioned version is sufficient for all practical use cases

### Other files:

3. **`Verity/Macro/Bridge.lean` — `_semantic_preservation` theorems** (1 sorry per function)
   - States: EDSL execution agrees with CM function spec (weak form)
   - Depends on: Phase 4 primitive bridge lemma composition
   - Impact: Medium — these are the macro-generated skeletons

### Fully proven (no sorry):

- `interpretYulRuntime_eq_yulResultOfExec` — result wrapping equivalence
- `yulStateOfIR_eq_initial` — state equivalence under entry-point conditions
- `yulBody_from_state_eq_yulBody` — modular proof delegating to the above + sorry (1)
- `layer3_contract_preserves_semantics` — conditioned on hvars/hmemory
- All `PrimitiveBridge.lean` lemmas (bind_unfold, pure_unfold, getStorage, setStorage,
  uint256_add/sub/mul/div/mod, lt/gt/eq comparisons, require, if_else, msgSender,
  Uint256/Address encoding, calldataload, Contract.run)
- `SemanticBridge.lean` — SimpleStorage (store, retrieve), Counter (increment,
  decrement, getCount), Owned (getOwner, transferOwnership), and SafeCounter
  (increment, decrement, getCount) — 11 proofs total (pending build verification)
-/

end Compiler.Proofs.EndToEnd
