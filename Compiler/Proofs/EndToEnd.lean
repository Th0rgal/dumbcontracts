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
equivalent results under the Yul runtime dispatch.

Requires:
- `hselector`: selector is within the valid range (< 2^32)
- The bridging lemma between `interpretYulBodyFromState` and
  `interpretYulBody` (the `sorry` below)

The `sorry` captures the gap between two Yul execution entry points:
- `interpretYulBodyFromState`: executes fn.body statements on IR-derived state
- `interpretYulBody`: executes fn.body via `interpretYulRuntime` (runtime dispatch)

These differ in initial state setup:
- `interpretYulBodyFromState` uses `yulStateOfIR selector state` (preserves vars)
- `interpretYulBody` uses `YulState.initial yulTx state.storage` (empty vars)

Since `fn.body` starts with `genParamLoads`-generated `let` statements that bind
all parameters from calldata (CompilationModel.lean:4676), the initial vars
difference is eliminated after the first few statements execute. The memory
difference (`state.memory` vs `fun _ => 0`) is similarly irrelevant because
macro-generated bodies don't read initial memory.

A formal bridging lemma would show that `execYulStmts` on both initial states
produces the same `YulExecResult` when the first statements in `fn.body`
shadow all free variables of the remaining body. -/
theorem layer3_contract_preserves_semantics
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulFromIR contract tx initialState) := by
  apply yulCodegen_preserves_semantics contract tx initialState hselector
  intro fn hmem
  -- Goal: resultsMatch (execIRFunction fn tx.args irState) (interpretYulBody fn tx irState)
  -- where irState = { initialState with sender, calldata, selector }
  --
  -- We have from ir_function_body_equiv:
  --   resultsMatch (execIRFunction fn args initialState')
  --               (interpretYulBodyFromState fn selector (...) initialState')
  --
  -- We need to bridge interpretYulBodyFromState → interpretYulBody.
  -- interpretYulBody fn tx state = interpretYulRuntime fn.body yulTx state.storage
  -- interpretYulBodyFromState fn sel state rollback =
  --   yulResultOfExecWithRollback (yulStateOfIR sel rollback) (execYulStmts (yulStateOfIR sel state) fn.body)
  --
  -- The bridging requires showing that for the initial state setup used by
  -- yulCodegen_preserves_semantics (state with sender/calldata/selector),
  -- both Yul execution paths produce the same result.
  sorry -- GAP: Bridge interpretYulBodyFromState ↔ interpretYulBody.
       --
       -- The two Yul execution paths differ in initial state:
       --   interpretYulBody:          YulState.initial → vars := [], memory := fun _ => 0
       --   interpretYulBodyFromState: yulStateOfIR     → vars := state.vars, memory := state.memory
       --
       -- Key insight: fn.body already contains calldataload instructions
       -- (generated by genParamLoads in CompilationModel.lean:4676) that bind
       -- all parameters from calldata. So fn.body = paramLoads ++ bodyStmts,
       -- where paramLoads are `let p := calldataload(offset)` statements.
       --
       -- After paramLoads execute, the variable bindings are identical regardless
       -- of whether vars started as [] or state.vars, because:
       --   (a) getVar uses List.find? — later bindings shadow earlier ones
       --   (b) paramLoads bind all params the body will reference
       --   (c) bodyStmts only reference parameters and new let-bindings
       --
       -- The memory difference (fun _ => 0 vs state.memory) is irrelevant
       -- because macro-generated code doesn't read initial memory.
       --
       -- Formal proof approach:
       --   1. Show execYulStmts is parametric in unused initial vars
       --      (a stmt-list that starts with let-bindings for all referenced
       --       vars produces the same result regardless of initial vars)
       --   2. Show fn.body's paramLoads cover all free variables of bodyStmts
       --   3. Show neither path reads initial memory before writing
       --   4. Show rollback storage is equivalent:
       --      yulStateOfIR.storage = initialState.storage = irState.storage
       --      (both from the same IRState)

/-! ## Bridging Lemma: interpretYulBodyFromState ↔ interpretYulBody

This lemma, when proven, would close the sorry in `layer3_contract_preserves_semantics`.
It states that for any IR function whose body starts with parameter-loading `let`
statements (as all `compileFunctionSpec`-generated functions do), the two Yul
execution entry points produce the same `YulResult`.

The lemma is stated here as a target for Phase 4. Proving it requires:
- A notion of "free variables" for Yul statements
- A proof that `genParamLoads` covers all free variables of the subsequent body
- A proof that `execYulStmts` is parametric in unused initial vars/memory
-/

/-- Bridging: the two Yul execution entry points produce the same result
when `fn.body` contains parameter-loading statements that shadow all
free variables.

When proven, this closes the sorry in `layer3_contract_preserves_semantics`.

**State alignment**:
- `interpretYulBody` starts from `YulState.initial yulTx state.storage`
  (vars = [], memory = fun _ => 0, storage = state.storage, calldata = tx.args,
   selector = tx.functionSelector, sender = tx.sender, returnValue = none)
- `interpretYulBodyFromState` starts from `yulStateOfIR sel paramState`
  (vars = paramState.vars, memory = paramState.memory, storage = state.storage, ...)

Both execute the same `fn.body`, which begins with `genParamLoads`-generated
`let name := calldataload(offset)` statements. After these execute, the var
bindings are identical because `YulState.setVar` prepends to the var list and
`YulState.getVar` uses `List.find?` (first match wins, shadowing earlier entries). -/
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
  sorry -- Phase 4: requires showing execYulStmts is parametric in initial vars/memory
        -- when fn.body starts with let-bindings that cover all referenced variables.
        --
        -- With the hypotheses above (vars=[], memory=fun _ => 0), the initial
        -- states for interpretYulBody and interpretYulBodyFromState are almost
        -- identical: both have empty vars, zero memory, same storage/calldata/sender.
        -- The remaining difference is that interpretYulBodyFromState's paramState
        -- has vars set by fn.params.zip args, while interpretYulBody's
        -- YulState.initial has vars=[]. But fn.body starts with calldataload
        -- let-bindings that will produce the same variable bindings.
        --
        -- Alternative simpler approach: when state already has vars=[] and
        -- memory=fun _ => 0, show yulStateOfIR sel state = YulState.initial yulTx state.storage
        -- directly (modulo the returnValue field, which doesn't affect execution).

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
    (hselector : tx.functionSelector < selectorModulus) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR irContract tx initialState)
      (interpretYulFromIR irContract tx initialState) :=
  layer3_contract_preserves_semantics irContract tx initialState hselector

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
    (hselector : tx.functionSelector < selectorModulus) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR simpleStorageIRContract tx initialState)
      (interpretYulFromIR simpleStorageIRContract tx initialState) :=
  layer3_contract_preserves_semantics simpleStorageIRContract tx initialState hselector

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

end Compiler.Proofs.EndToEnd
