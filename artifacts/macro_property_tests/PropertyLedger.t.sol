// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyLedgerTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Ledger/Ledger.lean
 */
contract PropertyLedgerTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("Ledger");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: deposit has no unexpected revert
    function testAuto_Deposit_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("deposit(uint256)", uint256(1)));
        require(ok, "deposit reverted unexpectedly");
    }
    // Property 2: withdraw has no unexpected revert
    function testAuto_Withdraw_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("withdraw(uint256)", uint256(1)));
        require(ok, "withdraw reverted unexpectedly");
    }
    // Property 3: transfer has no unexpected revert
    function testAuto_Transfer_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("transfer(address,uint256)", alice, uint256(1)));
        require(ok, "transfer reverted unexpectedly");
    }
    // Property 4: getBalance reads the configured mapping value
    function testAuto_GetBalance_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getBalance(address)", alice));
        require(ok, "getBalance reverted unexpectedly");
        assertEq(ret.length, 32, "getBalance ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getBalance should decode the configured mapping value");
    }
}
