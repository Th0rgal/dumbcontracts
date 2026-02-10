// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedCapSlotTest is GeneratedBase {
    function testCapSlot() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSetSlot = 0xf2c298be;
        bytes4 selCapSlot = 0x7fdb8622;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSetSlot, 5, 20));
        require(ok, "setSlot failed");

        (ok,) = deployed.call(abi.encodeWithSelector(selCapSlot, 5, 15));
        require(ok, "capSlot failed (cap 15)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 5));
        require(ok, "getSlot failed (slot 5)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 15, "capSlot did not lower value");

        (ok,) = deployed.call(abi.encodeWithSelector(selCapSlot, 5, 30));
        require(ok, "capSlot failed (cap 30)");
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 5));
        require(ok, "getSlot failed (slot 5, after cap 30)");
        val = abi.decode(data, (uint256));
        require(val == 15, "capSlot should not raise value");
    }
}
