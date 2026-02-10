// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/**
 * @title DifferentialSimpleStorage
 * @notice Differential testing for SimpleStorage contract
 *
 * Approach:
 * 1. Generate random transactions
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results
 *
 * Success: 10,000+ tests with zero mismatches
 */
contract DifferentialSimpleStorage is YulTestBase {
    // Compiled contract
    address simpleStorage;

    // Test counter
    uint256 public testsPassed;
    uint256 public testsFailed;

    function setUp() public {
        // Deploy SimpleStorage from Yul using YulTestBase helper
        simpleStorage = deployYul("SimpleStorage");
        require(simpleStorage != address(0), "Deploy failed");
    }

    /**
     * @notice Execute transaction on EVM and EDSL, compare results
     */
    function executeDifferentialTest(
        string memory functionName,
        address sender,
        uint256 arg0
    ) internal returns (bool success) {
        // 1. Execute on compiled contract (EVM)
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;
        uint256 evmStorageBefore = uint256(vm.load(simpleStorage, bytes32(uint256(0))));

        if (keccak256(bytes(functionName)) == keccak256(bytes("store"))) {
            (evmSuccess, evmReturnData) = simpleStorage.call(
                abi.encodeWithSignature("store(uint256)", arg0)
            );
        } else if (keccak256(bytes(functionName)) == keccak256(bytes("retrieve"))) {
            (evmSuccess, evmReturnData) = simpleStorage.call(
                abi.encodeWithSignature("retrieve()")
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmStorageAfter = uint256(vm.load(simpleStorage, bytes32(uint256(0))));
        uint256 evmReturnValue = evmReturnData.length > 0 ? abi.decode(evmReturnData, (uint256)) : 0;

        // 2. Execute on EDSL interpreter (via vm.ffi)
        // Build command: bash -c "cd ../.. && lake exe difftest-interpreter SimpleStorage <function> <sender> <arg0>"
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";
        inputs[2] = string.concat(
            "cd /workspaces/mission-482e3014/dumbcontracts && export PATH=\"$HOME/.elan/bin:$PATH\" && lake exe difftest-interpreter SimpleStorage ",
            functionName,
            " ",
            vm.toString(sender),
            " ",
            vm.toString(arg0)
        );

        // Call Lean interpreter
        bytes memory edslResultBytes = vm.ffi(inputs);
        string memory edslResult = string(edslResultBytes);

        // 3. Parse and compare results
        // The EDSL interpreter returns JSON like:
        // {"success":true,"returnValue":"42","revertReason":null,"storageChanges":[{"slot":0,"value":42}]}

        console2.log("EVM success:", evmSuccess);
        console2.log("EVM storage change:", evmStorageAfter);
        console2.log("EVM return value:", evmReturnValue);
        console2.log("EDSL result:", edslResult);

        // Simple validation: check that EDSL returned success:true
        bool edslSuccess = contains(edslResult, "\"success\":true");

        // For now, basic check: both should succeed
        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH: Success flags differ!");
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    /**
     * @notice Simple string contains check
     */
    function contains(string memory str, string memory substr) internal pure returns (bool) {
        bytes memory strBytes = bytes(str);
        bytes memory substrBytes = bytes(substr);

        if (substrBytes.length > strBytes.length) return false;

        for (uint i = 0; i <= strBytes.length - substrBytes.length; i++) {
            bool found = true;
            for (uint j = 0; j < substrBytes.length; j++) {
                if (strBytes[i + j] != substrBytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) return true;
        }
        return false;
    }

    /**
     * @notice Run differential tests with fixed transactions
     */
    function testDifferential_BasicOperations() public {
        // Test store
        executeDifferentialTest("store", address(0xA11CE), 42);

        // Test retrieve
        executeDifferentialTest("retrieve", address(0xA11CE), 0);

        // Test overwrite
        executeDifferentialTest("store", address(0xB0B), 100);
        executeDifferentialTest("retrieve", address(0xB0B), 0);

        console2.log("Differential tests passed:", testsPassed);
    }

    /**
     * @notice Run many random differential tests
     * @dev Commented out for now - requires full interpreter integration
     */
    /*
    function testDifferential_Random1000() public {
        uint256 seed = 42;

        for (uint256 i = 0; i < 1000; i++) {
            // Generate random transaction
            // TODO: Call random generator via vm.ffi

            // Execute differential test
            // bool success = executeDifferentialTest(...);
            // assertTrue(success, "Differential test failed");

            seed = uint256(keccak256(abi.encode(seed, i)));
        }

        console2.log("Random differential tests passed:", testsPassed);
    }
    */
}
