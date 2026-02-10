// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedSubIfEnoughTest is GeneratedBase {
    function testSubIfEnough() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSub = 0x9ee7809e;
        bytes4 selSet = 0xf2c298be;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 30, 20));
        require(ok, "setSlot failed (slot 30)");

        (ok,) = deployed.call(abi.encodeWithSelector(selSub, 30, 7));
        require(ok, "subIfEnough failed (20 - 7)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 30));
        require(ok, "getSlot failed (slot 30)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 13, "unexpected subIfEnough value");

        (ok,) = deployed.call(abi.encodeWithSelector(selSub, 30, 20));
        require(!ok, "subIfEnough should revert when delta too large");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 31, 5));
        require(ok, "setSlot failed (slot 31)");

        (ok,) = deployed.call(abi.encodeWithSelector(selSub, 31, 5));
        require(ok, "subIfEnough failed (5 - 5)");

        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 31));
        require(ok, "getSlot failed (slot 31)");
        val = abi.decode(data, (uint256));
        require(val == 0, "unexpected subIfEnough zero value");
    }
}
