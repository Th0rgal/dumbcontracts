// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedUpdateMinTest is GeneratedBase {
    function testUpdateMin() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selUpdateMin = 0x5c34a245;
        bytes4 selSet = 0xf2c298be;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 4, 10));
        require(ok, "setSlot failed (slot 4)");

        (ok,) = deployed.call(abi.encodeWithSelector(selUpdateMin, 4, 12));
        require(ok, "updateMin failed on larger value");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 4));
        require(ok, "getSlot failed (slot 4)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 10, "unexpected updateMin value after larger input");

        (ok,) = deployed.call(abi.encodeWithSelector(selUpdateMin, 4, 7));
        require(ok, "updateMin failed on smaller value");

        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 4));
        require(ok, "getSlot failed (slot 4) after update");
        val = abi.decode(data, (uint256));
        require(val == 7, "unexpected updateMin value after smaller input");
    }
}
