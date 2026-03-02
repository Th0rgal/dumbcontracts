// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {Test, console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./DifferentialTestBase.sol";

contract ERC721DiffModel {
    address private _owner;
    uint256 private _totalSupply;
    uint256 private _nextTokenId;
    mapping(address => uint256) private _balances;

    constructor(address initialOwner) {
        _owner = initialOwner;
        _totalSupply = 0;
        _nextTokenId = 0;
    }

    function owner() external view returns (address) {
        return _owner;
    }

    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    function nextTokenId() external view returns (uint256) {
        return _nextTokenId;
    }

    function balanceOf(address addr) external view returns (uint256) {
        return _balances[addr];
    }

    function mint(address to) external returns (uint256) {
        require(msg.sender == _owner, "Caller is not the owner");
        require(to != address(0), "Invalid recipient");

        uint256 tokenId = _nextTokenId;
        _balances[to] += 1;
        _totalSupply += 1;
        _nextTokenId = tokenId + 1;
        return tokenId;
    }
}

/**
 * @title DifferentialERC721
 * @notice Differential parity checks between Solidity model and Lean interpreter.
 */
contract DifferentialERC721 is DiffTestConfig, DifferentialTestBase {
    ERC721DiffModel private nft;

    mapping(address => uint256) private edslBalances; // slot 3
    mapping(uint256 => uint256) private edslStorage; // slot 1 => totalSupply, slot 2 => nextTokenId
    mapping(uint256 => address) private edslStorageAddr; // slot 0 => owner

    function setUp() public {
        nft = new ERC721DiffModel(address(this));
        edslStorage[1] = 0;
        edslStorage[2] = 0;
        edslStorageAddr[0] = address(this);
    }

    function executeDifferentialTest(
        string memory functionName,
        address sender,
        address arg0Addr
    ) internal returns (bool) {
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));
        if (functionSig == keccak256(bytes("mint"))) {
            (evmSuccess, evmReturnData) = address(nft).call(
                abi.encodeWithSignature("mint(address)", arg0Addr)
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            (evmSuccess, evmReturnData) = address(nft).call(
                abi.encodeWithSignature("balanceOf(address)", arg0Addr)
            );
        } else if (functionSig == keccak256(bytes("totalSupply"))) {
            (evmSuccess, evmReturnData) = address(nft).call(
                abi.encodeWithSignature("totalSupply()")
            );
        } else if (functionSig == keccak256(bytes("nextTokenId"))) {
            (evmSuccess, evmReturnData) = address(nft).call(
                abi.encodeWithSignature("nextTokenId()")
            );
        } else if (functionSig == keccak256(bytes("owner"))) {
            (evmSuccess, evmReturnData) = address(nft).call(
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

        uint256 evmTotalSupply = nft.totalSupply();
        uint256 evmNextTokenId = nft.nextTokenId();
        address evmOwner = nft.owner();
        uint256 evmSenderBalance = nft.balanceOf(sender);
        uint256 evmRecipientBalance = nft.balanceOf(arg0Addr);

        string memory edslResult = _runInterpreter(functionName, sender, arg0Addr, _buildMapState(sender, arg0Addr));
        bool edslSuccess = contains(edslResult, "\"success\":true");

        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH success");
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
        } else if (evmSuccess && evmReturnData.length > 0 && evmReturnValue != edslReturnValue) {
            console2.log("MISMATCH uint return");
            testsFailed++;
            return false;
        }

        (bool hasSupply, uint256 supplyVal) = _extractStorageChange(edslResult, 1);
        if (hasSupply) {
            edslStorage[1] = supplyVal;
        }
        (bool hasNextToken, uint256 nextTokenVal) = _extractStorageChange(edslResult, 2);
        if (hasNextToken) {
            edslStorage[2] = nextTokenVal;
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
        if (evmNextTokenId != edslStorage[2]) {
            console2.log("MISMATCH nextTokenId state");
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
        string memory mapState
    ) internal returns (string memory) {
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        bytes32 functionSig = keccak256(bytes(functionName));
        string memory argsStr = "";
        if (functionSig == keccak256(bytes("mint")) || functionSig == keccak256(bytes("balanceOf"))) {
            argsStr = vm.toString(uint256(uint160(arg0Addr)));
        }

        string memory storageStr = string.concat(
            "storage=1:",
            vm.toString(edslStorage[1]),
            ",2:",
            vm.toString(edslStorage[2])
        );
        string memory addrStr = string.concat("addr=0:", _addressToString(edslStorageAddr[0]));
        string memory mapStr = bytes(mapState).length > 0 ? string.concat(" map=\"", mapState, "\"") : "";

        inputs[2] = string.concat(
            _interpreterPreamble(),
            " ERC721 ",
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
            out = string.concat("3:", _toLowerCase(vm.toString(sender)), ":", vm.toString(edslBalances[sender]));
            first = false;
        }

        if (edslBalances[other] > 0 && other != sender) {
            if (!first) {
                out = string.concat(out, ",");
            }
            out = string.concat(out, "3:", _toLowerCase(vm.toString(other)), ":", vm.toString(edslBalances[other]));
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

    function testDifferential_MintAndViews() public {
        assertTrue(executeDifferentialTest("owner", address(this), address(0)));
        assertTrue(executeDifferentialTest("totalSupply", address(this), address(0)));
        assertTrue(executeDifferentialTest("nextTokenId", address(this), address(0)));

        assertTrue(executeDifferentialTest("mint", address(this), address(0xA11CE)));
        assertTrue(executeDifferentialTest("balanceOf", address(this), address(0xA11CE)));
        assertTrue(executeDifferentialTest("totalSupply", address(this), address(0)));
        assertTrue(executeDifferentialTest("nextTokenId", address(this), address(0)));

        assertTrue(executeDifferentialTest("mint", address(this), address(0xB0B)));
        assertTrue(executeDifferentialTest("balanceOf", address(this), address(0xB0B)));
    }

    function testDifferential_OwnerOnlyMintRevertParity() public {
        assertTrue(executeDifferentialTest("mint", address(0xB0B), address(0xCA401)));
    }
}
