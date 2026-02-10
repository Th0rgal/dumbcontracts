// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedRaiseSlotTest is GeneratedBase {
    function testRaiseSlot() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSetSlot = 0xf2c298be;
        bytes4 selRaiseSlot = 0x84c4b3e1;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSetSlot, 5, 10));
        require(ok, "setSlot failed");

        (ok,) = deployed.call(abi.encodeWithSelector(selRaiseSlot, 5, 20));
        require(ok, "raiseSlot failed (floor 20)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 5));
        require(ok, "getSlot failed (slot 5)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 20, "raiseSlot did not raise value");

        (ok,) = deployed.call(abi.encodeWithSelector(selRaiseSlot, 5, 5));
        require(ok, "raiseSlot failed (floor 5)");
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 5));
        require(ok, "getSlot failed (slot 5, after floor 5)");
        val = abi.decode(data, (uint256));
        require(val == 20, "raiseSlot should not lower value");
    }
}
