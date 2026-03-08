// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

contract PropertyLocalObligationMacroSmoke is YulTestBase {
    address macroSmoke;

    function setUp() public {
        macroSmoke = deployYul("LocalObligationMacroSmoke");
        require(macroSmoke != address(0), "Deploy failed");
    }

    /**
     * Property: unsafeEdge_preserves_state
     */
    function testProperty_UnsafeEdge_IsNoOp() public {
        uint256 slot0Before = readStorage(0);
        uint256 slot1Before = readStorage(1);

        (bool success,) = macroSmoke.call(
            abi.encodeWithSignature("unsafeEdge()")
        );
        require(success, "unsafeEdge failed");

        assertEq(readStorage(0), slot0Before, "unsafeEdge must preserve slot 0");
        assertEq(readStorage(1), slot1Before, "unsafeEdge must preserve slot 1");
    }

    /**
     * Property 1: dischargedEdge_meets_spec
     * Property 2: dischargedEdge_preserves_slot_zero
     * Property 3: dischargedEdge_roundtrip
     */
    function testProperty_DischargedEdge_WritesSlot1(uint256 value) public {
        (bool success, bytes memory data) = macroSmoke.call(
            abi.encodeWithSignature("dischargedEdge(uint256)", value)
        );
        require(success, "dischargedEdge failed");

        uint256 result = abi.decode(data, (uint256));
        assertEq(result, value, "dischargedEdge must return the input");
        assertEq(readStorage(1), value, "dischargedEdge must write slot 1");
    }
}
