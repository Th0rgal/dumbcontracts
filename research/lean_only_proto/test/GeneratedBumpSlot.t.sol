// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedBumpSlotTest is GeneratedBase {
    function testBumpSlot() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selBump = 0xb8df0e12;
        bytes4 selSet = 0xf2c298be;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 5, 41));
        require(ok, "setSlot failed (slot 5)");

        (ok,) = deployed.call(abi.encodeWithSelector(selBump, 5));
        require(ok, "bumpSlot failed");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 5));
        require(ok, "getSlot failed (slot 5)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 42, "unexpected bumpSlot value");
    }
}
