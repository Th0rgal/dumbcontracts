// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyOwnedCounterTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Verity/Examples/MacroContracts.lean
 */
contract PropertyOwnedCounterTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: increment has no unexpected revert
    function testAuto_Increment_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("increment()"));
        require(ok, "increment reverted unexpectedly");
    }
    // Property 2: decrement has no unexpected revert
    function testAuto_Decrement_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("decrement()"));
        require(ok, "decrement reverted unexpectedly");
    }
    // Property 3: TODO decode and assert `getCount` result
    function testTODO_GetCount_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getCount()"));
        require(ok, "getCount reverted unexpectedly");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `getOwner` result
    function testTODO_GetOwner_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getOwner()"));
        require(ok, "getOwner reverted unexpectedly");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: transferOwnership has no unexpected revert
    function testAuto_TransferOwnership_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("transferOwnership(address)", alice));
        require(ok, "transferOwnership reverted unexpectedly");
    }
}
