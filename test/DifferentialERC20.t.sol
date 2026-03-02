// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {Test, console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./DifferentialTestBase.sol";

contract ERC20DiffModel {
    uint256 private constant MAX_UINT256 = type(uint256).max;

    address private _owner;
    uint256 private _totalSupply;
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;

    constructor(address initialOwner) {
        _owner = initialOwner;
        _totalSupply = 0;
    }

    function mint(address to, uint256 amount) external {
        require(msg.sender == _owner, "Caller is not the owner");
        _balances[to] += amount;
        _totalSupply += amount;
    }

    function transfer(address to, uint256 amount) external {
        uint256 senderBal = _balances[msg.sender];
        require(senderBal >= amount, "Insufficient balance");

        if (msg.sender == to) {
            return;
        }

        _balances[msg.sender] = senderBal - amount;
        _balances[to] += amount;
    }

    function approve(address spender, uint256 amount) external {
        _allowances[msg.sender][spender] = amount;
    }

    function transferFrom(address fromAddr, address to, uint256 amount) external {
        uint256 currentAllowance = _allowances[fromAddr][msg.sender];
        require(currentAllowance >= amount, "Insufficient allowance");

        uint256 fromBalance = _balances[fromAddr];
        require(fromBalance >= amount, "Insufficient balance");

        if (fromAddr != to) {
            _balances[fromAddr] = fromBalance - amount;
            _balances[to] += amount;
        }

        if (currentAllowance != MAX_UINT256) {
            _allowances[fromAddr][msg.sender] = currentAllowance - amount;
        }
    }

    function balanceOf(address addr) external view returns (uint256) {
        return _balances[addr];
    }

    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    function owner() external view returns (address) {
        return _owner;
    }
}

/**
 * @title DifferentialERC20
 * @notice Differential parity checks between Solidity model and Lean interpreter.
 */
contract DifferentialERC20 is DiffTestConfig, DifferentialTestBase {
    ERC20DiffModel private token;

    mapping(address => uint256) private edslBalances; // slot 2
    mapping(uint256 => uint256) private edslStorage; // slot 1 => totalSupply
    mapping(uint256 => address) private edslStorageAddr; // slot 0 => owner

    function setUp() public {
        token = new ERC20DiffModel(address(this));
        edslStorage[1] = 0;
        edslStorageAddr[0] = address(this);
    }

    function executeDifferentialTest(
        string memory functionName,
        address sender,
        address arg0Addr,
        uint256 arg1
    ) internal returns (bool) {
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));
        if (functionSig == keccak256(bytes("mint"))) {
            (evmSuccess, evmReturnData) = address(token).call(
                abi.encodeWithSignature("mint(address,uint256)", arg0Addr, arg1)
            );
        } else if (functionSig == keccak256(bytes("transfer"))) {
            (evmSuccess, evmReturnData) = address(token).call(
                abi.encodeWithSignature("transfer(address,uint256)", arg0Addr, arg1)
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            (evmSuccess, evmReturnData) = address(token).call(
                abi.encodeWithSignature("balanceOf(address)", arg0Addr)
            );
        } else if (functionSig == keccak256(bytes("totalSupply"))) {
            (evmSuccess, evmReturnData) = address(token).call(
                abi.encodeWithSignature("totalSupply()")
            );
        } else if (functionSig == keccak256(bytes("owner"))) {
            (evmSuccess, evmReturnData) = address(token).call(
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

        uint256 evmTotalSupply = token.totalSupply();
        address evmOwner = token.owner();
        uint256 evmSenderBalance = token.balanceOf(sender);
        uint256 evmRecipientBalance = token.balanceOf(arg0Addr);

        string memory edslResult = _runInterpreter(functionName, sender, arg0Addr, arg1, _buildMapState(sender, arg0Addr));
        bool edslSuccess = contains(edslResult, "\"success\":true");

        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH success");
            console2.log("  EVM:", evmSuccess);
            console2.log("  EDSL:", edslSuccess);
            testsFailed++;
            return false;
        }

        if (!contains(edslResult, "\"returnValue\":")) {
            console2.log("MISMATCH malformed JSON");
            testsFailed++;
            return false;
        }

        uint256 edslReturnValue = _extractReturnValue(edslResult);
        if (functionSig == keccak256(bytes("owner"))) {
            if (uint256(uint160(evmReturnAddress)) != edslReturnValue) {
                console2.log("MISMATCH owner return");
                testsFailed++;
                return false;
            }
        } else if (
            functionSig == keccak256(bytes("balanceOf"))
                || functionSig == keccak256(bytes("totalSupply"))
        ) {
            if (evmReturnValue != edslReturnValue) {
                console2.log("MISMATCH uint return");
                testsFailed++;
                return false;
            }
        }

        (bool hasSupply, uint256 supplyVal) = _extractStorageChange(edslResult, 1);
        if (hasSupply) {
            edslStorage[1] = supplyVal;
        }

        (bool hasOwner, uint256 ownerNat) = _extractStorageAddrChange(edslResult, 0);
        if (hasOwner) {
            edslStorageAddr[0] = address(uint160(ownerNat));
        }

        _updateMappingState(edslResult, sender, arg0Addr);

        if (evmTotalSupply != edslStorage[1]) {
            console2.log("MISMATCH totalSupply state");
            testsFailed++;
            return false;
        }

        if (evmOwner != edslStorageAddr[0]) {
            console2.log("MISMATCH owner state");
            testsFailed++;
            return false;
        }

        if (evmSenderBalance != edslBalances[sender]) {
            console2.log("MISMATCH sender balance");
            testsFailed++;
            return false;
        }

        if (evmRecipientBalance != edslBalances[arg0Addr]) {
            console2.log("MISMATCH recipient balance");
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        address arg0Addr,
        uint256 arg1,
        string memory mapState
    ) internal returns (string memory) {
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        bytes32 functionSig = keccak256(bytes(functionName));
        string memory argsStr;
        if (functionSig == keccak256(bytes("mint")) || functionSig == keccak256(bytes("transfer"))) {
            argsStr = string.concat(vm.toString(uint256(uint160(arg0Addr))), " ", vm.toString(arg1));
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            argsStr = vm.toString(uint256(uint160(arg0Addr)));
        } else {
            argsStr = "";
        }

        string memory storageStr = string.concat("storage=1:", vm.toString(edslStorage[1]));
        string memory addrStr = string.concat("addr=0:", _addressToString(edslStorageAddr[0]));
        string memory mapStr = bytes(mapState).length > 0 ? string.concat(" map=\"", mapState, "\"") : "";

        inputs[2] = string.concat(
            _interpreterPreamble(),
            " ERC20 ",
            functionName,
            " ",
            _addressToString(sender),
            bytes(argsStr).length > 0 ? string.concat(" ", argsStr) : "",
            " ",
            storageStr,
            " ",
            addrStr,
            mapStr,
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        return string(vm.ffi(inputs));
    }

    function _buildMapState(address sender, address other) internal view returns (string memory) {
        string memory out = "";
        bool first = true;

        if (edslBalances[sender] > 0) {
            out = string.concat("2:", _toLowerCase(vm.toString(sender)), ":", vm.toString(edslBalances[sender]));
            first = false;
        }

        if (edslBalances[other] > 0 && other != sender) {
            if (!first) {
                out = string.concat(out, ",");
            }
            out = string.concat(out, "2:", _toLowerCase(vm.toString(other)), ":", vm.toString(edslBalances[other]));
        }

        return out;
    }

    function _updateMappingState(string memory edslResult, address sender, address other) internal {
        if (contains(edslResult, _toLowerCase(vm.toString(sender))) || contains(edslResult, vm.toString(sender))) {
            edslBalances[sender] = _extractMappingValue(edslResult, vm.toString(sender));
        }
        if (other != sender && (contains(edslResult, _toLowerCase(vm.toString(other))) || contains(edslResult, vm.toString(other)))) {
            edslBalances[other] = _extractMappingValue(edslResult, vm.toString(other));
        }
    }

    function testDifferential_MintTransferAndViews() public {
        assertTrue(executeDifferentialTest("owner", address(this), address(0), 0));
        assertTrue(executeDifferentialTest("totalSupply", address(this), address(0), 0));
        assertTrue(executeDifferentialTest("mint", address(this), address(0xA11CE), 100));
        assertTrue(executeDifferentialTest("transfer", address(0xA11CE), address(0xB0B), 40));
        assertTrue(executeDifferentialTest("balanceOf", address(this), address(0xA11CE), 0));
        assertTrue(executeDifferentialTest("balanceOf", address(this), address(0xB0B), 0));
        assertTrue(executeDifferentialTest("totalSupply", address(this), address(0), 0));
    }

    function testDifferential_OwnerOnlyMintRevertParity() public {
        assertTrue(executeDifferentialTest("mint", address(0xB0B), address(0xCA401), 7));
    }
}
