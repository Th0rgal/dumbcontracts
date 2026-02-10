// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedClearIfEqTest is GeneratedBase {
    function testClearIfEq() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selGet = 0x7eba7ba6;
        bytes4 selSet = 0xf2c298be;
        bytes4 selClear = 0xb41535b4;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 22, 55));
        require(ok, "setSlot failed");

        (ok,) = deployed.call(abi.encodeWithSelector(selClear, 22, 55));
        require(ok, "clearIfEq should succeed");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 22));
        require(ok, "getSlot failed");
        uint256 val = abi.decode(data, (uint256));
        require(val == 0, "unexpected clearIfEq value");

        (ok,) = deployed.call(abi.encodeWithSelector(selClear, 22, 7));
        require(!ok, "clearIfEq should revert on mismatch");
    }
}
