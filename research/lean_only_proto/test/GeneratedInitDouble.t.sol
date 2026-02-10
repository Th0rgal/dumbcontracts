// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedInitDoubleTest is GeneratedBase {
    function testInitDouble() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selInitDouble = 0xa756818e;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selInitDouble, 12, 7));
        require(ok, "initDouble failed (first init)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 12));
        require(ok, "getSlot failed (slot 12)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 14, "unexpected initDouble value");

        (ok,) = deployed.call(abi.encodeWithSelector(selInitDouble, 12, 9));
        require(!ok, "initDouble should revert when slot already set");
    }
}
