// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedAddIfNonZeroAndLessTest is GeneratedBase {
    function testAddIfNonZeroAndLess() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selAdd = 0x0db24e47;
        bytes4 selSet = 0xf2c298be;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 8, 10));
        require(ok, "setSlot failed (slot 8)");

        (ok,) = deployed.call(abi.encodeWithSelector(selAdd, 8, 3, 8));
        require(ok, "addIfNonZeroAndLess failed (delta < max, non-zero)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 8));
        require(ok, "getSlot failed (slot 8)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 13, "unexpected addIfNonZeroAndLess value");

        (ok,) = deployed.call(abi.encodeWithSelector(selAdd, 9, 0, 8));
        require(!ok, "addIfNonZeroAndLess should revert when delta == 0");

        (ok,) = deployed.call(abi.encodeWithSelector(selAdd, 10, 8, 8));
        require(!ok, "addIfNonZeroAndLess should revert when delta >= max");
    }
}
