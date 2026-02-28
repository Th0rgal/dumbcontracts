// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";
import "./DifferentialTestBase.sol";

/**
 * @title DifferentialERC20
 * @notice Differential testing for ERC20 contract
 *
 * Approach:
 * 1. Generate random transactions (mint, transfer, approve, transferFrom, balanceOf, allowance, totalSupply, owner)
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results (including balances, allowances, owner, and totalSupply)
 *
 * ERC20 storage layout (from Verity/Examples/ERC20.lean):
 *   slot 0: owner (address)
 *   slot 1: totalSupply (uint256)
 *   slot 2: balances mapping (address => uint256)
 *   slot 3: allowances double-mapping (address => address => uint256)
 */
contract DifferentialERC20 is YulTestBase, DiffTestConfig, DifferentialTestBase {
    // Compiled contract
    address erc20;

    // Storage state tracking for EDSL interpreter
    mapping(address => uint256) edslBalances;                     // Mapping slot 2: balances
    mapping(address => mapping(address => uint256)) edslAllowances; // Double-mapping slot 3: allowances
    mapping(uint256 => address) edslStorageAddr;                  // Slot 0: owner address
    mapping(uint256 => uint256) edslStorage;                      // Slot 1: totalSupply

    // Track known addresses for building storage strings
    address[] knownAddresses;
    mapping(address => bool) knownAddressSet;

    function setUp() public {
        // Deploy ERC20 from Yul with constructor arg (initialOwner)
        address initialOwner = address(this);
        erc20 = deployYulWithArgs("ERC20", abi.encode(initialOwner));
        require(erc20 != address(0), "Deploy failed");

        // Set EDSL state
        edslStorageAddr[0] = initialOwner;
        edslStorage[1] = 0; // Initial totalSupply
        _trackAddress(initialOwner);
    }

    function _trackAddress(address addr) internal {
        if (!knownAddressSet[addr] && addr != address(0)) {
            knownAddresses.push(addr);
            knownAddressSet[addr] = true;
        }
    }

    /**
     * @notice Execute transaction on EVM and EDSL, compare results
     */
    function executeDifferentialTest(
        string memory functionName,
        address sender,
        address arg0Addr,
        address arg1Addr,
        uint256 arg2
    ) internal returns (bool success) {
        _trackAddress(sender);
        _trackAddress(arg0Addr);
        _trackAddress(arg1Addr);

        // 1. Execute on compiled contract (EVM)
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("mint"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("mint(address,uint256)", arg0Addr, arg2)
            );
        } else if (functionSig == keccak256(bytes("transfer"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("transfer(address,uint256)", arg0Addr, arg2)
            );
        } else if (functionSig == keccak256(bytes("approve"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("approve(address,uint256)", arg0Addr, arg2)
            );
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("transferFrom(address,address,uint256)", arg0Addr, arg1Addr, arg2)
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("balanceOf(address)", arg0Addr)
            );
        } else if (functionSig == keccak256(bytes("allowance"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("allowance(address,address)", arg0Addr, arg1Addr)
            );
        } else if (functionSig == keccak256(bytes("totalSupply"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("totalSupply()")
            );
        } else if (functionSig == keccak256(bytes("owner"))) {
            (evmSuccess, evmReturnData) = erc20.call(
                abi.encodeWithSignature("owner()")
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmReturnValue = 0;
        address evmReturnAddress = address(0);

        if (evmSuccess && evmReturnData.length > 0) {
            if (functionSig == keccak256(bytes("owner"))) {
                evmReturnAddress = abi.decode(evmReturnData, (address));
            } else {
                evmReturnValue = abi.decode(evmReturnData, (uint256));
            }
        }

        // Get EVM state after transaction
        uint256 evmTotalSupply = uint256(vm.load(erc20, bytes32(uint256(1))));
        address evmOwner = address(uint160(uint256(vm.load(erc20, bytes32(uint256(0))))));

        // 2. Execute on EDSL interpreter (via vm.ffi)
        string memory storageState = _buildStorageString(sender, arg0Addr, arg1Addr);
        string memory edslResult = _runInterpreter(functionName, sender, arg0Addr, arg1Addr, arg2, storageState);

        // 3. Parse and compare results
        bool verbose = _diffVerbose();
        if (verbose) {
            console2.log("Function:", functionName);
            console2.log("EVM success:", evmSuccess);
            console2.log("EVM totalSupply:", evmTotalSupply);
            console2.log("EDSL result:", edslResult);
        }

        // Parse EDSL result
        bool edslSuccess = contains(edslResult, "\"success\":true");

        // Validate JSON structure
        if (!contains(edslResult, "\"returnValue\":")) {
            console2.log("ERROR: Malformed JSON - missing returnValue field");
            console2.log("  JSON:", edslResult);
            testsFailed++;
            return false;
        }

        uint256 edslReturnValue = _extractReturnValue(edslResult);

        // Validate: Success flags must match
        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH: Success flags differ!");
            console2.log("  Function:", functionName);
            console2.log("  EVM:", evmSuccess);
            console2.log("  EDSL:", edslSuccess);
            testsFailed++;
            return false;
        }

        // Validate: Return values must match
        if (functionSig == keccak256(bytes("balanceOf")) ||
            functionSig == keccak256(bytes("totalSupply")) ||
            functionSig == keccak256(bytes("allowance"))) {
            if (evmReturnValue != edslReturnValue) {
                console2.log("MISMATCH: Return values differ!");
                console2.log("  Function:", functionName);
                console2.log("  EVM:", evmReturnValue);
                console2.log("  EDSL:", edslReturnValue);
                testsFailed++;
                return false;
            }
        } else if (functionSig == keccak256(bytes("owner"))) {
            if (uint256(uint160(evmReturnAddress)) != edslReturnValue) {
                console2.log("MISMATCH: Owner addresses differ!");
                console2.log("  EVM:", evmReturnAddress);
                console2.log("  EDSL:", address(uint160(edslReturnValue)));
                testsFailed++;
                return false;
            }
        }

        // Validate: Storage changes must match
        (bool hasTotalSupplyChange, uint256 edslTotalSupplyChange) = _extractStorageChange(edslResult, 1);
        if (hasTotalSupplyChange) {
            edslStorage[1] = edslTotalSupplyChange;
        }

        (bool hasOwnerChange, uint256 edslOwnerChangeNat) = _extractStorageAddrChange(edslResult, 0);
        if (hasOwnerChange) {
            edslStorageAddr[0] = address(uint160(edslOwnerChangeNat));
        }

        // Update balance mapping changes
        _updateEDSLMappingStorage(edslResult, sender, arg0Addr, arg1Addr);

        // Update allowance double-mapping changes
        _updateEDSLMapping2Storage(edslResult);

        // Validate: EVM final storage must match EDSL final storage
        if (evmTotalSupply != edslStorage[1]) {
            console2.log("MISMATCH: TotalSupply differs!");
            console2.log("  EVM totalSupply:", evmTotalSupply);
            console2.log("  EDSL totalSupply:", edslStorage[1]);
            testsFailed++;
            return false;
        }

        if (evmOwner != edslStorageAddr[0]) {
            console2.log("MISMATCH: Owner differs!");
            console2.log("  EVM owner:", evmOwner);
            console2.log("  EDSL owner:", edslStorageAddr[0]);
            testsFailed++;
            return false;
        }

        // Validate balances for all known addresses
        for (uint256 i = 0; i < knownAddresses.length; i++) {
            address addr = knownAddresses[i];
            bytes32 balanceSlot = keccak256(abi.encode(addr, uint256(2)));
            uint256 evmBalance = uint256(vm.load(erc20, balanceSlot));
            if (evmBalance != edslBalances[addr]) {
                console2.log("MISMATCH: Balance differs for address!");
                console2.log("  EVM balance:", evmBalance);
                console2.log("  EDSL balance:", edslBalances[addr]);
                testsFailed++;
                return false;
            }
        }

        // Validate allowances for relevant address pairs
        if (functionSig == keccak256(bytes("approve")) ||
            functionSig == keccak256(bytes("transferFrom"))) {
            address allowanceOwner;
            address allowanceSpender;
            if (functionSig == keccak256(bytes("approve"))) {
                allowanceOwner = sender;
                allowanceSpender = arg0Addr;
            } else {
                // transferFrom: arg0=from, sender=spender
                allowanceOwner = arg0Addr;
                allowanceSpender = sender;
            }
            bytes32 innerSlot = keccak256(abi.encode(allowanceOwner, uint256(3)));
            bytes32 allowanceSlot = keccak256(abi.encode(allowanceSpender, uint256(innerSlot)));
            uint256 evmAllowance = uint256(vm.load(erc20, allowanceSlot));
            if (evmAllowance != edslAllowances[allowanceOwner][allowanceSpender]) {
                console2.log("MISMATCH: Allowance differs!");
                console2.log("  EVM allowance:", evmAllowance);
                console2.log("  EDSL allowance:", edslAllowances[allowanceOwner][allowanceSpender]);
                testsFailed++;
                return false;
            }
        }

        testsPassed++;
        return true;
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        address arg0Addr,
        address arg1Addr,
        uint256 arg2,
        string memory storageState
    ) internal returns (string memory) {
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        // Build args string based on function
        string memory argsStr;
        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("mint")) ||
            functionSig == keccak256(bytes("transfer")) ||
            functionSig == keccak256(bytes("approve"))) {
            // Two args: address, uint256
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                " ",
                vm.toString(arg2)
            );
        } else if (functionSig == keccak256(bytes("transferFrom"))) {
            // Three args: address, address, uint256
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                " ",
                vm.toString(uint256(uint160(arg1Addr))),
                " ",
                vm.toString(arg2)
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            // One address arg
            argsStr = vm.toString(uint256(uint160(arg0Addr)));
        } else if (functionSig == keccak256(bytes("allowance"))) {
            // Two address args
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                " ",
                vm.toString(uint256(uint160(arg1Addr)))
            );
        } else {
            // No args (totalSupply, owner)
            argsStr = "";
        }

        string memory storageAppend = bytes(storageState).length > 0
            ? string.concat(" ", storageState)
            : "";

        inputs[2] = string.concat(
            _interpreterPreamble(),
            " ERC20 ",
            functionName,
            " ",
            vm.toString(sender),
            bytes(argsStr).length > 0 ? string.concat(" ", argsStr) : "",
            storageAppend,
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        bytes memory result = vm.ffi(inputs);
        return string(result);
    }

    function _buildStorageString(
        address sender,
        address arg0Addr,
        address arg1Addr
    ) internal view returns (string memory) {
        string memory result = "";

        // Add owner address storage (slot 0)
        address owner = edslStorageAddr[0];
        if (owner != address(0)) {
            result = string.concat(
                "addr=\"0:",
                _toLowerCase(vm.toString(owner)),
                "\""
            );
        }

        // Add totalSupply storage (slot 1)
        uint256 supply = edslStorage[1];
        if (bytes(result).length > 0) {
            result = string.concat(result, " ");
        }
        result = string.concat(
            result,
            "\"1:",
            vm.toString(supply),
            "\""
        );

        // Add balances mapping storage (slot 2)
        string memory mappingStr = _buildMappingStorageString();
        if (bytes(mappingStr).length > 0) {
            result = string.concat(
                result,
                " map=\"",
                mappingStr,
                "\""
            );
        }

        // Add allowances double-mapping storage (slot 3)
        string memory mapping2Str = _buildMapping2StorageString();
        if (bytes(mapping2Str).length > 0) {
            result = string.concat(
                result,
                " map2=\"",
                mapping2Str,
                "\""
            );
        }

        return result;
    }

    function _buildMappingStorageString() internal view returns (string memory) {
        string memory result = "";
        bool first = true;

        for (uint256 i = 0; i < knownAddresses.length; i++) {
            address addr = knownAddresses[i];
            if (edslBalances[addr] > 0) {
                if (!first) {
                    result = string.concat(result, ",");
                }
                result = string.concat(
                    result,
                    "2:",
                    _toLowerCase(vm.toString(addr)),
                    ":",
                    vm.toString(edslBalances[addr])
                );
                first = false;
            }
        }

        return result;
    }

    function _buildMapping2StorageString() internal view returns (string memory) {
        // Build double-mapping storage in format: "slot:key1:key2:value,..."
        string memory result = "";
        bool first = true;

        for (uint256 i = 0; i < knownAddresses.length; i++) {
            for (uint256 j = 0; j < knownAddresses.length; j++) {
                address owner = knownAddresses[i];
                address spender = knownAddresses[j];
                uint256 allowance = edslAllowances[owner][spender];
                if (allowance > 0) {
                    if (!first) {
                        result = string.concat(result, ",");
                    }
                    result = string.concat(
                        result,
                        "3:",
                        _toLowerCase(vm.toString(owner)),
                        ":",
                        _toLowerCase(vm.toString(spender)),
                        ":",
                        vm.toString(allowance)
                    );
                    first = false;
                }
            }
        }

        return result;
    }

    function _updateEDSLMappingStorage(
        string memory edslResult,
        address sender,
        address arg0Addr,
        address arg1Addr
    ) internal {
        if (!contains(edslResult, "\"mappingChanges\":")) {
            return;
        }

        // Check all relevant addresses for balance changes
        address[3] memory addrs = [sender, arg0Addr, arg1Addr];
        for (uint256 i = 0; i < 3; i++) {
            address addr = addrs[i];
            if (addr == address(0)) continue;
            string memory addrStr = _toLowerCase(vm.toString(addr));
            if (contains(edslResult, addrStr) || contains(edslResult, vm.toString(addr))) {
                uint256 value = _extractMappingValue(edslResult, vm.toString(addr));
                edslBalances[addr] = value;
            }
        }
    }

    function _updateEDSLMapping2Storage(string memory edslResult) internal {
        if (!contains(edslResult, "\"mapping2Changes\":")) {
            return;
        }

        // Parse mapping2Changes: [{"slot":3,"key1":"0x...","key2":"0x...","value":N},...]
        bytes memory jsonBytes = bytes(edslResult);
        bytes memory marker = bytes("\"mapping2Changes\":");

        // Find the start of mapping2Changes array
        uint256 arrayStart = 0;
        for (uint256 i = 0; i <= jsonBytes.length - marker.length; i++) {
            bool found = true;
            for (uint256 j = 0; j < marker.length; j++) {
                if (jsonBytes[i + j] != marker[j]) {
                    found = false;
                    break;
                }
            }
            if (found) {
                arrayStart = i + marker.length;
                break;
            }
        }

        if (arrayStart == 0) return;

        // Parse each entry in the array
        bytes memory key1Marker = bytes("\"key1\":\"");
        bytes memory key2Marker = bytes("\"key2\":\"");
        bytes memory valueMarker = bytes("\"value\":");

        uint256 pos = arrayStart;
        while (pos < jsonBytes.length) {
            // Find next key1
            uint256 key1Start = _findPattern(jsonBytes, key1Marker, pos);
            if (key1Start == 0) break;
            key1Start += key1Marker.length;

            // Extract key1 hex string
            uint256 key1End = key1Start;
            while (key1End < jsonBytes.length && jsonBytes[key1End] != '"') key1End++;
            string memory key1Hex = _extractSubstring(jsonBytes, key1Start, key1End);

            // Find key2
            uint256 key2Start = _findPattern(jsonBytes, key2Marker, key1End);
            if (key2Start == 0) break;
            key2Start += key2Marker.length;

            uint256 key2End = key2Start;
            while (key2End < jsonBytes.length && jsonBytes[key2End] != '"') key2End++;
            string memory key2Hex = _extractSubstring(jsonBytes, key2Start, key2End);

            // Find value
            uint256 valueStart = _findPattern(jsonBytes, valueMarker, key2End);
            if (valueStart == 0) break;
            valueStart += valueMarker.length;

            uint256 valueEnd = valueStart;
            while (valueEnd < jsonBytes.length && jsonBytes[valueEnd] >= '0' && jsonBytes[valueEnd] <= '9') valueEnd++;

            uint256 value = _extractNumber(edslResult, valueStart);

            // Parse addresses and update
            address key1Addr = address(uint160(_parseHexAddress(key1Hex)));
            address key2Addr = address(uint160(_parseHexAddress(key2Hex)));
            edslAllowances[key1Addr][key2Addr] = value;

            pos = valueEnd;
        }
    }

    function _findPattern(bytes memory data, bytes memory pattern, uint256 start)
        internal
        pure
        returns (uint256)
    {
        if (data.length < pattern.length + start) return 0;
        for (uint256 i = start; i <= data.length - pattern.length; i++) {
            bool found = true;
            for (uint256 j = 0; j < pattern.length; j++) {
                if (data[i + j] != pattern[j]) {
                    found = false;
                    break;
                }
            }
            if (found) return i;
        }
        return 0;
    }

    function _extractSubstring(bytes memory data, uint256 start, uint256 end)
        internal
        pure
        returns (string memory)
    {
        bytes memory result = new bytes(end - start);
        for (uint256 i = 0; i < end - start; i++) {
            result[i] = data[start + i];
        }
        return string(result);
    }

    // ============ Test Cases ============

    function testDifferential_Mint() public {
        address owner = address(this);
        address alice = address(0xA11CE);

        bool success = executeDifferentialTest("mint", owner, alice, address(0), 1000);
        assertTrue(success, "Mint test failed");
    }

    function testDifferential_Transfer() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Mint to Alice
        bool success1 = executeDifferentialTest("mint", owner, alice, address(0), 1000);
        assertTrue(success1, "Mint failed");

        // Alice transfers to Bob
        bool success2 = executeDifferentialTest("transfer", alice, bob, address(0), 300);
        assertTrue(success2, "Transfer failed");
    }

    function testDifferential_Approve() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Alice approves Bob
        bool success = executeDifferentialTest("approve", alice, bob, address(0), 500);
        assertTrue(success, "Approve test failed");
    }

    function testDifferential_TransferFrom() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address charlie = address(0xCA401);

        // Mint to Alice
        executeDifferentialTest("mint", owner, alice, address(0), 1000);

        // Alice approves Bob for 500
        executeDifferentialTest("approve", alice, bob, address(0), 500);

        // Bob transfers 300 from Alice to Charlie
        bool success = executeDifferentialTest("transferFrom", bob, alice, charlie, 300);
        assertTrue(success, "TransferFrom test failed");
    }

    function testDifferential_AccessControl() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Owner can mint
        bool success1 = executeDifferentialTest("mint", owner, alice, address(0), 1000);
        assertTrue(success1, "Owner mint failed");

        // Non-owner cannot mint (should revert)
        bool success2 = executeDifferentialTest("mint", bob, alice, address(0), 500);
        assertTrue(success2, "Access control test failed");
    }

    function testDifferential_GetOperations() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Mint some tokens
        executeDifferentialTest("mint", owner, alice, address(0), 1000);
        executeDifferentialTest("approve", alice, bob, address(0), 300);

        // Get balance
        bool success1 = executeDifferentialTest("balanceOf", owner, alice, address(0), 0);
        assertTrue(success1, "BalanceOf failed");

        // Get allowance
        bool success2 = executeDifferentialTest("allowance", owner, alice, bob, 0);
        assertTrue(success2, "Allowance failed");

        // Get total supply
        bool success3 = executeDifferentialTest("totalSupply", owner, address(0), address(0), 0);
        assertTrue(success3, "GetTotalSupply failed");

        // Get owner
        bool success4 = executeDifferentialTest("owner", owner, address(0), address(0), 0);
        assertTrue(success4, "GetOwner failed");
    }

    function testDifferential_InsufficientBalance() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Try to transfer with zero balance (should revert)
        bool success = executeDifferentialTest("transfer", alice, bob, address(0), 100);
        assertTrue(success, "Insufficient balance test failed");
    }

    function testDifferential_InsufficientAllowance() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address charlie = address(0xCA401);

        // Mint to Alice
        executeDifferentialTest("mint", owner, alice, address(0), 1000);

        // Alice approves Bob for 100
        executeDifferentialTest("approve", alice, bob, address(0), 100);

        // Bob tries to transferFrom 200 (should revert - insufficient allowance)
        bool success = executeDifferentialTest("transferFrom", bob, alice, charlie, 200);
        assertTrue(success, "Insufficient allowance test failed");
    }

    function testDifferential_InfiniteAllowance() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address charlie = address(0xCA401);

        // Mint to Alice
        executeDifferentialTest("mint", owner, alice, address(0), 1000);

        // Alice approves Bob for MAX_UINT256 (infinite allowance)
        executeDifferentialTest("approve", alice, bob, address(0), type(uint256).max);

        // Bob transfers from Alice - allowance should NOT decrease
        bool success = executeDifferentialTest("transferFrom", bob, alice, charlie, 500);
        assertTrue(success, "Infinite allowance test failed");
    }

    function testDifferential_SelfTransfer() public {
        address owner = address(this);
        address alice = address(0xA11CE);

        // Mint to Alice
        executeDifferentialTest("mint", owner, alice, address(0), 500);

        // Self-transfer should be a no-op
        bool success = executeDifferentialTest("transfer", alice, alice, address(0), 200);
        assertTrue(success, "Self-transfer failed");
    }

    function testDifferential_Random100() public {
        address[] memory actors = new address[](5);
        actors[0] = address(this); // Owner
        actors[1] = address(0xA11CE);
        actors[2] = address(0xB0B);
        actors[3] = address(0xCA401);
        actors[4] = address(0xDABE);

        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        uint256 seed = _diffRandomSeed("ERC20");

        for (uint256 i = 0; i < count; i++) {
            (string memory funcName, address sender, address addr0, address addr1, uint256 amount) =
                _randomERC20Transaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, addr0, addr1, amount);
            _assertRandomSuccess(success, startIndex + i);
        }

        if (_diffVerbose()) console2.log("Random tests passed:", testsPassed);
        if (_diffVerbose()) console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function testDifferential_Random10000() public {
        address[] memory actors = new address[](5);
        actors[0] = address(this); // Owner
        actors[1] = address(0xA11CE);
        actors[2] = address(0xB0B);
        actors[3] = address(0xCA401);
        actors[4] = address(0xDABE);

        (uint256 startIndex, uint256 count) = _diffRandomLargeRange();
        uint256 seed = _diffRandomSeed("ERC20");

        vm.pauseGasMetering();
        for (uint256 i = 0; i < count; i++) {
            (string memory funcName, address sender, address addr0, address addr1, uint256 amount) =
                _randomERC20Transaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, addr0, addr1, amount);
            _assertRandomSuccess(success, startIndex + i);
        }
        vm.resumeGasMetering();

        if (_diffVerbose()) console2.log("Random tests passed:", testsPassed);
        if (_diffVerbose()) console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function _randomERC20Transaction(uint256 seed, address[] memory actors)
        internal
        view
        returns (
            string memory funcName,
            address sender,
            address addr0,
            address addr1,
            uint256 amount
        )
    {
        uint256 rand1 = _lcg(seed);
        uint256 rand2 = _lcg(rand1);
        uint256 rand3 = _lcg(rand2);
        uint256 rand4 = _lcg(rand3);
        uint256 rand5 = _lcg(rand4);

        // Choose function:
        //   20% mint, 20% transfer, 15% approve, 15% transferFrom,
        //   10% balanceOf, 10% allowance, 5% totalSupply, 5% owner
        uint256 funcChoice = rand1 % 100;
        if (funcChoice < 20) {
            funcName = "mint";
        } else if (funcChoice < 40) {
            funcName = "transfer";
        } else if (funcChoice < 55) {
            funcName = "approve";
        } else if (funcChoice < 70) {
            funcName = "transferFrom";
        } else if (funcChoice < 80) {
            funcName = "balanceOf";
        } else if (funcChoice < 90) {
            funcName = "allowance";
        } else if (funcChoice < 95) {
            funcName = "totalSupply";
        } else {
            funcName = "owner";
        }

        // Choose sender (60% owner for mint success, 40% random)
        uint256 senderChoice = rand2 % 100;
        if (senderChoice < 60) {
            sender = edslStorageAddr[0]; // Current owner
        } else {
            sender = actors[rand2 % actors.length];
        }

        // Choose addresses
        addr0 = actors[rand3 % actors.length];
        addr1 = actors[rand4 % actors.length];

        // Choose amount
        amount = _coerceRandomUint256(rand5, 1000);
    }
}
