// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedNonZeroStoreTest is GeneratedBase {
    function testSetNonZero() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSetNonZero = 0xac1f1f67;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSetNonZero, 9, 123));
        require(ok, "setNonZero failed");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 9));
        require(ok, "getSlot failed (slot 9)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 123, "unexpected setNonZero value");

        (ok,) = deployed.call(abi.encodeWithSelector(selSetNonZero, 10, 0));
        require(!ok, "setNonZero should revert on zero");
    }
}
