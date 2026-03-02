// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyERC721Test
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Verity/Examples/MacroContracts.lean
 */
contract PropertyERC721Test is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("ERC721", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `ownerOf` result
    function testTODO_OwnerOf_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("ownerOf(uint256)", uint256(1)));
        require(ok, "ownerOf reverted unexpectedly");
        assertEq(ret.length, 32, "ownerOf ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `getApproved` result
    function testTODO_GetApproved_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getApproved(uint256)", uint256(1)));
        require(ok, "getApproved reverted unexpectedly");
        assertEq(ret.length, 32, "getApproved ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: approve has no unexpected revert
    function testAuto_Approve_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("approve(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "approve reverted unexpectedly");
    }
    // Property 4: TODO decode and assert `mint` result
    function testTODO_Mint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("mint(uint256)", uint256(1)));
        require(ok, "mint reverted unexpectedly");
        assertEq(ret.length, 32, "mint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: transferFrom has no unexpected revert
    function testAuto_TransferFrom_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("transferFrom(uint256,uint256,uint256)", uint256(1), uint256(1), uint256(1)));
        require(ok, "transferFrom reverted unexpectedly");
    }
}
