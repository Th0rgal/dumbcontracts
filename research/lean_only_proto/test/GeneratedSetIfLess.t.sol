// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedSetIfLessTest is GeneratedBase {
    function testSetIfLess() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSet = 0x7e5acdb6;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 21, 7, 10));
        require(ok, "setIfLess failed (value < max)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 21));
        require(ok, "getSlot failed (slot 21)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 7, "unexpected setIfLess value");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 22, 9, 9));
        require(!ok, "setIfLess should revert when value >= max");
    }
}
