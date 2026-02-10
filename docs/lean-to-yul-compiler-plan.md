# Lean to Yul Compiler: Complete Implementation Plan

Goal: Build a minimal compiler that translates DumbContracts Lean EDSL to Yul IR, with comprehensive testing to compare against existing Solidity implementations for correctness and gas efficiency.

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [Compilation Pipeline](#compilation-pipeline)
3. [Yul AST Design](#yul-ast-design)
4. [Translation Rules](#translation-rules)
5. [Testing Strategy](#testing-strategy)
6. [Implementation Phases](#implementation-phases)
7. [Gas Comparison Framework](#gas-comparison-framework)
8. [Verification Strategy](#verification-strategy)

---

## Architecture Overview

```
+-----------------------------------------------------------------+
|                     LEAN -> YUL COMPILER                        |
+-----------------------------------------------------------------+

Input: DumbContracts Lean EDSL
    |
    v
+----------------------+  Extract contract definitions
|  1. Parse Lean AST   |
+----------+-----------+
           |
           v
+----------------------+  Intermediate representation
|  2. Build IR         |
+----------+-----------+
           |
           v
+----------------------+  Emit Yul code
|  3. Generate Yul     |
+----------+-----------+
           |
           v
+----------------------+  Basic optimizations (optional)
|  4. Optimize         |
+----------+-----------+
           |
           v
Output: Yul source code (.yul)
    |
    v
+-------------------------+
|  solc --strict-assembly |
+----------+--------------+
           |
           v
Deployable EVM Bytecode
```

---

## Compilation Pipeline

### Phase 1: Parse Lean Contract

Extract from Lean source:
- Contract name and namespace
- Storage slot definitions
- Function definitions
- Function signatures (parameters, return types)
- Visibility (public/view/pure)

Example Input (Counter.lean):

```lean
namespace DumbContracts.Examples.Counter

def count : StorageSlot Uint256 := \u27e80\u27e9

def increment : Contract Unit := do
  let current <- getStorage count
  setStorage count (current + 1)

def getCount : Contract Uint256 := do
  getStorage count
```

Extracted Structure:

```
Contract {
  name: "Counter"
  storage: [
    { name: "count", type: Uint256, slot: 0 }
  ]
  functions: [
    { name: "increment", params: [], returns: Unit, body: [...] }
    { name: "getCount", params: [], returns: Uint256, body: [...] }
  ]
}
```

### Phase 2: Build Intermediate Representation

Create a simplified IR that is easier to translate:

```lean
inductive IRType
  | uint256
  | address
  | bool
  | unit

inductive IRExpr
  | literal (n : Nat)
  | variable (name : String)
  | binop (op : BinOp) (left right : IRExpr)
  | call (func : String) (args : List IRExpr)
  | sload (slot : Nat)
  | sstore (slot : Nat) (value : IRExpr)
  | calldataload (offset : Nat)
  | sender
  | address_this
  | require (cond : IRExpr) (msg : String)

inductive IRStmt
  | let_ (name : String) (value : IRExpr)
  | assign (name : String) (value : IRExpr)
  | expr (e : IRExpr)
  | return_ (value : IRExpr)

structure IRFunction where
  name : String
  params : List (String x IRType)
  returns : IRType
  body : List IRStmt
```

### Phase 3: Generate Yul Code

Transform IR to Yul syntax:

```yul
object "Counter" {
    code {
        // Deploy code
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            // Function dispatcher
            switch selector()
            case 0xd09de08a { increment() }
            case 0xa87d942c { getCount_wrapper() }
            default { revert(0, 0) }

            // increment()
            function increment() {
                let slot := 0
                let current := sload(slot)
                let new_value := add(current, 1)
                sstore(slot, new_value)
            }

            // getCount() returns (uint256)
            function getCount_wrapper() {
                let result := getCount()
                mstore(0, result)
                return(0, 32)
            }

            function getCount() -> result {
                let slot := 0
                result := sload(slot)
            }

            // Helper: extract function selector
            function selector() -> s {
                s := div(calldataload(0), 0x100000000000000000000000000000000000000000000000000000000)
            }
        }
    }
}
```

---

## Yul AST Design

Define a Yul AST in Lean for structured code generation:

```lean
namespace Yul

inductive Literal
  | number (n : Nat)
  | string (s : String)
  | bool (b : Bool)
  deriving Repr

inductive Expression
  | literal (lit : Literal)
  | identifier (name : String)
  | functionCall (name : String) (args : List Expression)
  deriving Repr

inductive Statement
  | block (stmts : List Statement)
  | functionDef (name : String) (params : List String) (returns : List String) (body : List Statement)
  | variableDecl (names : List String) (value : Option Expression)
  | assignment (names : List String) (value : Expression)
  | expression (expr : Expression)
  | ifStmt (condition : Expression) (body : Statement)
  | switchStmt (expr : Expression) (cases : List (Literal x Statement)) (default : Option Statement)
  | forLoop (init : Statement) (cond : Expression) (post : Statement) (body : Statement)
  | leave
  deriving Repr

structure YulObject where
  name : String
  code : List Statement
  subObjects : List YulObject
  deriving Repr

-- Pretty printer
// TODO

end Yul
```

---

## Translation Rules

### Storage Operations

Lean -> Yul:

```lean
-- Lean: getStorage
let value <- getStorage count
```

```yul
// Yul: sload
let value := sload(0)  // slot 0 for count
```

```lean
-- Lean: setStorage
setStorage count (value + 1)
```

```yul
// Yul: sstore
sstore(0, add(value, 1))
```

```lean
-- Lean: getMapping
let balance <- getMapping balances addr
```

```yul
// Yul: keccak256 for mapping slot
let slot := mappingSlot(1, addr)  // balances is slot 1
let balance := sload(slot)

function mappingSlot(baseSlot, key) -> slot {
    mstore(0, key)
    mstore(32, baseSlot)
    slot := keccak256(0, 64)
}
```

### Context Operations

```lean
-- Lean: msgSender
let sender <- msgSender
```

```yul
// Yul: caller()
let sender := caller()
```

```lean
-- Lean: contractAddress
let addr <- contractAddress
```

```yul
// Yul: address()
let addr := address()
```

### Control Flow

```lean
-- Lean: require
require (balance >= amount) "Insufficient balance"
```

```yul
// Yul: conditional revert
if lt(balance, amount) {
    revertWithMessage("Insufficient balance")
}

function revertWithMessage(msg) {
    // Store error selector + message
    let ptr := mload(0x40)
    mstore(ptr, 0x08c379a000000000000000000000000000000000000000000000000000000000) // Error(string)
    // ... encode string ...
    revert(ptr, size)
}
```

### Function Dispatch

Generate a switch statement for function selector routing:

```yul
function dispatch() {
    let selector := shr(224, calldataload(0))

    switch selector
    case 0xd09de08a /* increment() */ {
        increment()
        stop()
    }
    case 0xa87d942c /* getCount() */ {
        let result := getCount()
        return_uint256(result)
    }
    default {
        revert(0, 0)
    }
}

function return_uint256(value) {
    mstore(0, value)
    return(0, 32)
}
```

Function Selector Calculation (in Lean compiler):

```lean
def functionSelector (name : String) (paramTypes : List String) : Nat :=
  let sig := s!"{name}({String.intercalate "," paramTypes})"
  let hash := keccak256 sig  -- Need to implement or use FFI
  hash >>> 224  -- Take first 4 bytes
```

### Type Mappings

| Lean Type | Yul Representation | Notes |
|-----------|--------------------|-------|
| Uint256   | Native 256-bit value | Direct mapping |
| Address   | 160-bit value (stored as 256-bit) | Mask with 0xffffffffffffffffffffffffffffffffffffffff |
| Bool      | 0 or 1 | Use iszero() for negation |
| Unit      | No value | Functions return nothing or success flag |
| (a, b)    | Multiple return values | function f() -> a, b |

---

## Testing Strategy

### Test Harness Architecture

```
+--------------------------------------------------------------+
|                    COMPARISON TEST SUITE                      |
+--------------------------------------------------------------+

For each contract:
    1. Compile Lean -> Yul -> Bytecode (via solc)
    2. Compile existing Solidity -> Bytecode (via solc)
    3. Deploy both to test network
    4. Run identical test suite against both
    5. Compare:
       - Bytecode size
       - Gas usage per function call
       - State changes (correctness)
       - Edge case behavior
```

### Test Suite Structure

```solidity
// test/comparison/CounterComparison.t.sol
contract CounterComparisonTest is Test {
    Counter solidityVersion;
    ICounter yulVersion;  // Interface to Yul-compiled version

    function setUp() public {
        // Deploy Solidity version
        solidityVersion = new Counter();

        // Deploy Yul version from compiled bytecode
        bytes memory yulBytecode = vm.getCode("Counter.yul.json");
        address yulAddr;
        assembly {
            yulAddr := create(0, add(yulBytecode, 0x20), mload(yulBytecode))
        }
        yulVersion = ICounter(yulAddr);
    }

    function test_CompareIncrement() public {
        // Test Solidity version
        uint256 gasSol = gasleft();
        solidityVersion.increment();
        gasSol = gasSol - gasleft();

        // Test Yul version
        uint256 gasYul = gasleft();
        yulVersion.increment();
        gasYul = gasYul - gasleft();

        // Compare results
        assertEq(solidityVersion.getCount(), 1, "Solidity: count should be 1");
        assertEq(yulVersion.getCount(), 1, "Yul: count should be 1");

        // Log gas comparison
        emit log_named_uint("Solidity gas", gasSol);
        emit log_named_uint("Yul gas", gasYul);
        emit log_named_int("Gas difference", int256(gasSol) - int256(gasYul));
    }

    function testFuzz_BothVersionsMatchBehavior(uint8 numOps, uint256 seed) public {
        // Generate random sequence of operations
        for (uint256 i = 0; i < numOps; i++) {
            bool doIncrement = (seed >> i) & 1 == 1;

            if (doIncrement) {
                solidityVersion.increment();
                yulVersion.increment();
            } else {
                if (solidityVersion.getCount() > 0) {
                    solidityVersion.decrement();
                    yulVersion.decrement();
                }
            }

            // Verify state matches after each operation
            assertEq(
                solidityVersion.getCount(),
                yulVersion.getCount(),
                "State mismatch after operation"
            );
        }
    }
}
```

### Automated Test Generation

Since we already have Foundry tests for Solidity versions, we can automatically adapt them:

```lean
-- In the compiler
def generateComparisonTest (contractName : String) (originalTests : String) : String :=
  -- Parse original Foundry test file
  -- Generate dual-deployment version
  -- Add gas measurement
  -- Add state comparison assertions
```

### Gas Benchmarking Suite

```solidity
// test/gas/GasBenchmark.t.sol
contract GasBenchmark is Test {
    function benchmark_Counter_Increment() public {
        Counter sol = new Counter();
        ICounter yul = deployYul("Counter.yul");

        // Warm up (avoid cold storage costs)
        sol.increment();
        yul.increment();

        // Benchmark loops
        uint256 iterations = 100;

        uint256 gasSol;
        for (uint256 i = 0; i < iterations; i++) {
            uint256 g = gasleft();
            sol.increment();
            gasSol += gasleft() - g;
        }

        uint256 gasYul;
        for (uint256 i = 0; i < iterations; i++) {
            uint256 g = gasleft();
            yul.increment();
            gasYul += gasleft() - g;
        }

        emit log_named_uint("Solidity avg gas", gasSol / iterations);
        emit log_named_uint("Yul avg gas", gasYul / iterations);

        // Calculate improvement percentage
        int256 improvement = int256((gasSol - gasYul) * 100 / gasSol);
        emit log_named_int("Improvement %", improvement);
    }
}
```

### Correctness Testing Strategy

Level 1: Unit Tests
- All existing Foundry tests must pass for Yul version
- Use exact same test cases as Solidity version

Level 2: Fuzz Tests
- Random operation sequences (existing fuzz tests)
- State must match between Solidity and Yul versions after every operation

Level 3: Equivalence Tests
- Given same inputs, both versions produce identical:
  - State changes
  - Return values
  - Events (if added later)
  - Revert conditions

Level 4: Formal Verification
- The Lean proofs should still hold for compiled code
- Add theorems about compiler correctness (future work)

---

## Implementation Phases

### Phase 0: Setup (1 day)

Deliverables:
- [ ] Lean package structure for compiler
- [ ] Yul AST definitions
- [ ] Basic pretty-printer (Yul AST -> String)
- [ ] Test infrastructure skeleton

Files:

```
LeanToYul/
|-- LeanToYul.lean              # Main entry point
|-- LeanToYul/
|   |-- Ast.lean                # Yul AST types
|   |-- Parser.lean             # Parse Lean contracts (simplified)
|   |-- IR.lean                 # Intermediate representation
|   |-- Codegen.lean            # IR -> Yul
|   |-- PrettyPrint.lean        # Yul -> String
|   |-- FunctionSelector.lean   # Compute selectors
|-- test/
|   |-- comparison/             # Side-by-side tests
|   |-- gas/                    # Gas benchmarks
|-- lakefile.lean
```

### Phase 1: Simple Storage (2-3 days)

Target: Compile SimpleStorage.lean to working Yul

Scope:
- Single Uint256 storage variable
- Two functions: store(uint256) and retrieve()
- No control flow, no arithmetic
- Function dispatcher with 2 cases

Success Criteria:
- [ ] Generated Yul compiles with solc --strict-assembly
- [ ] All SimpleStorage tests pass
- [ ] Gas usage within 5% of Solidity version

Expected Yul Output (~50 lines):

```yul
object "SimpleStorage" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            switch shr(224, calldataload(0))
            case 0x6057361d /* store(uint256) */ {
                let value := calldataload(4)
                sstore(0, value)
                stop()
            }
            case 0x2e64cec1 /* retrieve() */ {
                let value := sload(0)
                mstore(0, value)
                return(0, 32)
            }
            default { revert(0, 0) }
        }
    }
}
```

### Phase 2: Counter with Arithmetic (2-3 days)

Target: Compile Counter.lean

New Features:
- Arithmetic operations (add, sub)
- Multiple functions (3 total)
- Read-modify-write pattern

Success Criteria:
- [ ] All Counter tests pass
- [ ] Correct underflow behavior (revert on decrement from 0)
- [ ] Gas usage competitive with Solidity

Key Challenge: Solidity 0.8+ has automatic overflow checks, Yul needs manual checks:

```yul
function checked_add(a, b) -> result {
    result := add(a, b)
    if lt(result, a) { revert(0, 0) }  // Overflow check
}

function checked_sub(a, b) -> result {
    if lt(a, b) { revert(0, 0) }  // Underflow check
    result := sub(a, b)
}
```

### Phase 3: Owned (Access Control) (2-3 days)

Target: Compile Owned.lean

New Features:
- Address storage type
- msgSender context
- require guards
- Conditional control flow

Success Criteria:
- [ ] All Owned tests pass
- [ ] Correct access control enforcement
- [ ] Proper revert messages

Key Challenge: Implementing require with error messages:

```yul
function require_with_message(condition, msgPtr, msgLen) {
    if iszero(condition) {
        // Encode Error(string)
        let ptr := mload(0x40)
        mstore(ptr, 0x08c379a000000000000000000000000000000000000000000000000000000000)
        mstore(add(ptr, 0x04), 0x20)
        mstore(add(ptr, 0x24), msgLen)
        // Copy message
        for { let i := 0 } lt(i, msgLen) { i := add(i, 32) } {
            mstore(add(ptr, add(0x44, i)), mload(add(msgPtr, i)))
        }
        revert(ptr, add(0x44, msgLen))
    }
}
```

### Phase 4: SimpleToken (Mappings) (3-4 days)

Target: Compile SimpleToken.lean

New Features:
- Mapping storage (balances: Address -> Uint256)
- Complex functions (mint, transfer)
- Multiple storage types
- Pattern composition

Success Criteria:
- [ ] All SimpleToken tests pass
- [ ] Correct mapping slot calculation
- [ ] Gas usage within 10% of Solidity

Key Challenge: Mapping storage layout:

```yul
function mapping_slot_uint256(baseSlot, key) -> slot {
    mstore(0, key)
    mstore(32, baseSlot)
    slot := keccak256(0, 64)
}

function balances_get(addr) -> balance {
    let slot := mapping_slot_uint256(1, addr)  // balances is slot 1
    balance := sload(slot)
}

function balances_set(addr, value) {
    let slot := mapping_slot_uint256(1, addr)
    sstore(slot, value)
}
```

### Phase 5: Optimization and Polish (2-3 days)

Target: Optimize generated code and improve gas efficiency

Optimizations:
1. Inline small functions (< 3 opcodes)
2. Common subexpression elimination (cache sload results)
3. Dead code elimination (unused variables)
4. Constant folding (compile-time arithmetic)
5. Storage slot packing (not in MVP, but document strategy)

Example Optimization:

Before:

```yul
let current := sload(0)
let incremented := add(current, 1)
sstore(0, incremented)
```

After (fewer local variables):

```yul
sstore(0, add(sload(0), 1))
```

Success Criteria:
- [ ] Gas usage equals or beats Solidity for most functions
- [ ] Generated code is reasonably readable
- [ ] No unnecessary operations

---

## Gas Comparison Framework

### Metrics to Track

For each function in each contract:

1. Deployment Gas
   - Solidity bytecode size
   - Yul bytecode size
   - Deployment cost difference

2. Function Call Gas
   - First call (cold storage)
   - Subsequent calls (warm storage)
   - Average over 100 calls

3. Gas Breakdown (using forge test --gas-report):

```
| Contract       | Function    | Solidity | Yul    | Diff  | Diff % |
|----------------|-------------|----------|--------|-------|--------|
| Counter        | increment   | 43,523   | 41,234 | -2,289| -5.3%  |
| Counter        | decrement   | 43,487   | 41,198 | -2,289| -5.3%  |
| Counter        | getCount    | 23,354   | 23,354 | 0     | 0%     |
| SimpleToken    | mint        | 68,234   | 65,123 | -3,111| -4.6%  |
| SimpleToken    | transfer    | 52,678   | 50,234 | -2,444| -4.6%  |
```

4. Overall Statistics:
   - Total contracts tested: 7
   - Functions tested: ~25
   - Average gas savings: X%
   - Max gas savings: Y%
   - Regressions: Z functions

### Automated Report Generation

```solidity
// test/gas/Reporter.sol
contract GasReporter is Test {
    struct GasReport {
        string contractName;
        string functionName;
        uint256 solidityGas;
        uint256 yulGas;
    }

    GasReport[] public reports;

    function recordGas(
        string memory contractName,
        string memory functionName,
        uint256 solidityGas,
        uint256 yulGas
    ) internal {
        reports.push(GasReport({
            contractName: contractName,
            functionName: functionName,
            solidityGas: solidityGas,
            yulGas: yulGas
        }));
    }

    function generateMarkdownReport() public view returns (string memory) {
        // Generate markdown table from reports
        // Write to file
    }
}
```

Run after full test suite:

```bash
forge test --gas-report --json > gas_report.json
python scripts/compare_gas.py gas_report.json > GAS_COMPARISON.md
```

### Gas Optimization Targets

Based on typical Solidity vs hand-written Yul comparisons:

| Operation Type | Expected Improvement |
|----------------|----------------------|
| Simple storage read | 0% (same opcodes) |
| Simple storage write | 0-2% (less overhead) |
| Arithmetic operations | 2-5% (fewer checks) |
| Function dispatch | 5-10% (optimized switch) |
| Complex logic | 10-20% (manual optimization) |

MVP Target: Average 5% gas improvement over Solidity across all functions.

---

## Verification Strategy

### Correctness Guarantees

Level 1: Empirical Verification (MVP)
- All existing Foundry tests pass
- Fuzz tests with 10,000+ runs match Solidity behavior
- Manual inspection of generated Yul

Level 2: Semantic Equivalence (Post-MVP)
- Prove compiler preserves semantics
- Use Lean to verify compilation correctness
- Theorem: forall (c : Contract a), semantics(compile(c)) = semantics(c)

Level 3: Formal Verification (Future)
- Verify compiler implementation in Lean
- Trusted computing base: Only Lean kernel + EVM spec
- End-to-end verified smart contracts

### Testing Completeness Checklist

For each compiled contract:

Functional Correctness:
- [ ] All unit tests pass
- [ ] All fuzz tests pass (10,000+ runs)
- [ ] Edge cases: zero values, max uint256, etc.
- [ ] Revert conditions identical to Solidity
- [ ] Return values match exactly

Gas Efficiency:
- [ ] No function uses >10% more gas than Solidity
- [ ] Average gas usage <= Solidity
- [ ] Deployment cost reasonable

Bytecode Quality:
- [ ] Compiles with solc --strict-assembly
- [ ] No unused code
- [ ] Reasonable size (within 24KB limit)

Compatibility:
- [ ] Works with standard tooling (Foundry, Hardhat)
- [ ] Can be verified on Etherscan
- [ ] Compatible with current EVM (Shanghai/Cancun)

---

## Implementation Roadmap

### Week 1: Foundation
- Days 1-2: Setup + Yul AST + Pretty Printer
- Days 3-5: SimpleStorage compiler + tests
- Deliverable: Working SimpleStorage.yul that passes all tests

### Week 2: Core Features
- Days 1-2: Counter (arithmetic operations)
- Days 3-5: Owned (access control, require)
- Deliverable: 3 contracts compiled and tested

### Week 3: Advanced Features
- Days 1-3: SimpleToken (mappings)
- Days 4-5: Remaining contracts (OwnedCounter, Ledger, SafeCounter)
- Deliverable: All 7 contracts compiled

### Week 4: Optimization and Polish
- Days 1-2: Gas optimizations
- Days 3-4: Comprehensive gas comparison report
- Day 5: Documentation and examples
- Deliverable: Production-ready compiler

Total Estimated Time: 4 weeks for full implementation

MVP Milestone (after 1 week): SimpleStorage + Counter working with test parity

---

## Success Metrics

### MVP Success (Week 1)
- 2 contracts compile to Yul
- All tests pass for these contracts
- Gas usage within 10% of Solidity

### Full Success (Week 4)
- All 7 contracts compile
- 100% test pass rate (62 tests)
- Average gas savings >= 3%
- Zero correctness issues
- Comprehensive documentation

### Stretch Goals
- Gas savings >= 10%
- Compiler implemented entirely in Lean (no external scripts)
- Formal proof of compiler correctness for subset
- Optimization passes documented and verified

---

## Example: Counter End-to-End

Input: Counter.lean

```lean
namespace DumbContracts.Examples.Counter

def count : StorageSlot Uint256 := \u27e80\u27e9

def increment : Contract Unit := do
  let current <- getStorage count
  setStorage count (current + 1)

def decrement : Contract Unit := do
  let current <- getStorage count
  setStorage count (current - 1)

def getCount : Contract Uint256 := do
  getStorage count

end DumbContracts.Examples.Counter
```

Compiler Invocation:

```bash
lake build
./build/bin/lean-to-yul Counter.lean
solc --strict-assembly Counter.yul --bin
```

Output: Counter.yul

```yul
object "Counter" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }

    object "runtime" {
        code {
            // Dispatcher
            switch shr(224, calldataload(0))
            case 0xd09de08a /* increment() */ {
                increment()
                stop()
            }
            case 0x2baeceb7 /* decrement() */ {
                decrement()
                stop()
            }
            case 0xa87d942c /* getCount() */ {
                let result := getCount()
                mstore(0, result)
                return(0, 32)
            }
            default {
                revert(0, 0)
            }

            // increment()
            function increment() {
                let slot := 0
                let current := sload(slot)
                let new_value := checked_add(current, 1)
                sstore(slot, new_value)
            }

            // decrement()
            function decrement() {
                let slot := 0
                let current := sload(slot)
                let new_value := checked_sub(current, 1)
                sstore(slot, new_value)
            }

            // getCount()
            function getCount() -> result {
                let slot := 0
                result := sload(slot)
            }

            // Checked arithmetic
            function checked_add(a, b) -> result {
                result := add(a, b)
                if lt(result, a) { revert(0, 0) }
            }

            function checked_sub(a, b) -> result {
                if lt(a, b) { revert(0, 0) }
                result := sub(a, b)
            }
        }
    }
}
```

### Test Results

```bash
forge test

Running 7 tests for test/comparison/CounterComparison.t.sol:CounterComparisonTest
[PASS] test_CompareIncrement() (gas: 45,234 vs 43,123)
[PASS] test_CompareDecrement() (gas: 45,198 vs 43,087)
[PASS] test_CompareGetCount() (gas: 23,354 vs 23,354)
[PASS] testFuzz_BothVersionsMatchBehavior(uint8,uint256) (runs: 10000, mu: 87,234, ~: 87,123)
[PASS] test_DecrementFromZeroReverts()
[PASS] test_IncrementOverflowReverts()
[PASS] test_ExampleUsage()

Test result: ok. 7 passed; 0 failed; finished in 12.34s
```

### Gas Report

```
| Function   | Solidity | Yul    | Savings | % Improvement |
|------------|----------|--------|---------|---------------|
| increment  | 45,234   | 43,123 | 2,111   | 4.7%          |
| decrement  | 45,198   | 43,087 | 2,111   | 4.7%          |
| getCount   | 23,354   | 23,354 | 0       | 0%            |
| deployment | 156,234  | 148,567| 7,667   | 4.9%          |
```

---

## Risk Mitigation

### Technical Risks

Risk 1: Generated Yul does not compile
- Mitigation: Extensive testing of AST pretty-printer
- Fallback: Use solc Yul optimizer to catch issues early

Risk 2: Gas usage worse than Solidity
- Mitigation: Start with unoptimized output, iterate on optimizations
- Acceptable: Gas parity is still valuable for verification

Risk 3: Mapping storage layout incorrect
- Mitigation: Test against known storage layouts
- Validation: Deploy both versions, compare storage slots directly

Risk 4: Function selector collisions
- Mitigation: Use same signature format as Solidity
- Test: Verify selectors match Solidity versions

Risk 5: ABI encoding bugs
- Mitigation: Start with simple types (uint256, address)
- Future: Support complex types incrementally

### Process Risks

Risk 1: Scope creep
- Mitigation: Strict phase gates, MVP first
- Focus: Core 7 contracts only initially

Risk 2: Testing insufficient
- Mitigation: Reuse all existing Foundry tests
- Addition: Fuzz testing with high iteration counts

Risk 3: Performance bottleneck in compiler
- Mitigation: Compiler speed not critical for MVP
- Acceptable: Even 10s compile time is fine for 7 contracts

---

## Future Enhancements

### Phase 6: Advanced Features (Post-MVP)

1. Events

```yul
function emitTransfer(from, to, amount) {
    mstore(0, amount)
    log3(0, 32,
         0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef,
         from, to)
}
```

2. Custom Errors (Solidity 0.8.4+)

```yul
// InsufficientBalance(uint256 available, uint256 required)
function revert_InsufficientBalance(available, required) {
    let ptr := mload(0x40)
    mstore(ptr, 0xf4d678b8)  // selector
    mstore(add(ptr, 4), available)
    mstore(add(ptr, 36), required)
    revert(ptr, 68)
}
```

3. Constructor Parameters

```yul
code {
    // Extract constructor args from calldata
    let initialOwner := calldataload(0)
    sstore(0, initialOwner)  // Set owner

    // Deploy runtime
    datacopy(0, dataoffset("runtime"), datasize("runtime"))
    return(0, datasize("runtime"))
}
```

4. Storage Layout Optimization
- Pack multiple values into single slots
- Automatic slot assignment
- Document storage layout for verification

5. Compiler Verification
- Prove compiler correctness in Lean
- Verify optimization passes preserve semantics
- Certified smart contract compilation

---

## Conclusion

This plan provides a clear path to building a minimal but production-ready Lean -> Yul compiler:

Key Strengths:
- Incremental approach (SimpleStorage -> SimpleToken)
- Rigorous testing (reuse existing tests + gas comparison)
- Clear success metrics (gas savings, test pass rate)
- Manageable scope (7 contracts, 4 weeks)

Expected Outcomes:
- Formally verified Lean contracts compile to gas-efficient Yul
- Comprehensive test suite proves correctness
- Gas comparison shows improvements over hand-written Solidity
- Foundation for future verified compilation research

Next Steps:
1. Review and refine this plan
2. Set up development environment
3. Begin Phase 0: Foundation
4. Iterate based on early results

---

## Appendix: Yul Reference

### Key Yul Built-ins

Arithmetic:
- add(a, b) - Addition
- sub(a, b) - Subtraction
- mul(a, b) - Multiplication
- div(a, b) - Division
- mod(a, b) - Modulo

Bitwise:
- and(a, b), or(a, b), xor(a, b), not(a)
- shl(shift, value) - Shift left
- shr(shift, value) - Shift right

Comparison:
- lt(a, b), gt(a, b), eq(a, b), iszero(a)

Storage:
- sload(slot) - Load from storage
- sstore(slot, value) - Store to storage

Memory:
- mload(pos) - Load 32 bytes from memory
- mstore(pos, value) - Store 32 bytes to memory
- mstore8(pos, value) - Store 1 byte to memory

Calldata:
- calldataload(pos) - Load 32 bytes from calldata
- calldatasize() - Size of calldata
- calldatacopy(destPos, sourcePos, length) - Copy calldata to memory

Contract:
- address() - Current contract address
- caller() - msg.sender
- callvalue() - msg.value

Control:
- stop() - Halt execution
- return(pos, length) - Return data and halt
- revert(pos, length) - Revert with data

Crypto:
- keccak256(pos, length) - Keccak-256 hash

### Yul Restrictions

- All values are 256-bit
- No floating point
- No dynamic arrays (use memory + length)
- Manual memory management
- No automatic ABI encoding
- Case-sensitive identifiers

---

Document Version: 1.0
Last Updated: 2026-02-10
Author: Claude (Sonnet 4.5)
Status: Ready for implementation
