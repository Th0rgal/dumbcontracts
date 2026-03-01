// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyUint8SmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Verity/Examples/MacroContracts.lean
 */
contract PropertyUint8SmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("Uint8Smoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: acceptSig has no unexpected revert
    function testAuto_AcceptSig_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("acceptSig((uint8,bytes32,bytes32))", abi.encode(uint8(27), bytes32(uint256(0xBEEF)), bytes32(uint256(0xBEEF)))));
        require(ok, "acceptSig reverted unexpectedly");
    }
    // Property 2: TODO decode and assert `sigV` result
    function testTODO_SigV_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("sigV()"));
        require(ok, "sigV reverted unexpectedly");
        assertEq(ret.length, 32, "sigV ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
