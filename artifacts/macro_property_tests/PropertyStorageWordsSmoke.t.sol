// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageWordsSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Verity/Examples/MacroContracts.lean
 */
contract PropertyStorageWordsSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageWordsSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `extSloadsLike` result
    function testTODO_ExtSloadsLike_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("extSloadsLike(bytes32[])", _singletonBytes32Array(bytes32(uint256(0xBEEF)))));
        require(ok, "extSloadsLike reverted unexpectedly");
        require(ret.length >= 64, "extSloadsLike ABI dynamic return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }

    function _singletonBytes32Array(bytes32 x) internal pure returns (bytes32[] memory arr) {
        arr = new bytes32[](1);
        arr[0] = x;
    }
}
