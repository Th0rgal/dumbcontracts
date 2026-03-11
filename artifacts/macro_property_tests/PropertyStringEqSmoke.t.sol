// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStringEqSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/StringSmoke.lean
 */
contract PropertyStringEqSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StringEqSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: same matches the expected dynamic-parameter comparison result
    function testAuto_Same_ComparesDirectDynamicParamsEq() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("same(string,string)", "verity", "verity"));
        require(ok, "same reverted unexpectedly");
        assertEq(ret.length, 32, "same ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        bool expected = true;
        assertEq(actual, expected, "same should preserve the configured comparison result");
        assertTrue(actual, "same should return true for the configured string comparison");
    }
    // Property 2: different matches the expected dynamic-parameter comparison result
    function testAuto_Different_ComparesDirectDynamicParamsNeq() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("different(string,string)", "verity", "verity"));
        require(ok, "different reverted unexpectedly");
        assertEq(ret.length, 32, "different ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        bool expected = false;
        assertEq(actual, expected, "different should preserve the configured comparison result");
        assertFalse(actual, "different should return false for the configured string comparison");
    }
    // Property 3: choose selects the expected branch for the configured dynamic inputs
    function testAuto_Choose_SelectsDynamicComparisonBranch() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("choose(string,string)", "verity", "verity"));
        require(ok, "choose reverted unexpectedly");
        assertEq(ret.length, 32, "choose ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 1, "choose should return the configured branch value");
    }
}
