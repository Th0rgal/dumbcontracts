// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedUpdateMaxTest is GeneratedBase {
    function testUpdateMax() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selUpdateMax = 0xe9cc4edd;
        bytes4 selSet = 0xf2c298be;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 4, 10));
        require(ok, "setSlot failed (slot 4)");

        (ok,) = deployed.call(abi.encodeWithSelector(selUpdateMax, 4, 7));
        require(ok, "updateMax failed on smaller value");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 4));
        require(ok, "getSlot failed (slot 4)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 10, "unexpected updateMax value after smaller input");

        (ok,) = deployed.call(abi.encodeWithSelector(selUpdateMax, 4, 12));
        require(ok, "updateMax failed on larger value");

        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 4));
        require(ok, "getSlot failed (slot 4) after update");
        val = abi.decode(data, (uint256));
        require(val == 12, "unexpected updateMax value after larger input");
    }
}
