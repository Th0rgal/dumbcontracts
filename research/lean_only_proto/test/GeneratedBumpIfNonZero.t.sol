// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedBumpIfNonZeroTest is GeneratedBase {
    function testBumpIfNonZero() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selBumpIfNonZero = 0xc2311456;
        bytes4 selSet = 0xf2c298be;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 3, 9));
        require(ok, "setSlot failed (slot 3)");

        (ok,) = deployed.call(abi.encodeWithSelector(selBumpIfNonZero, 3));
        require(ok, "bumpIfNonZero failed");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 3));
        require(ok, "getSlot failed (slot 3)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 10, "unexpected bumpIfNonZero value");
    }

    function testBumpIfNonZeroRevertsOnZero() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selBumpIfNonZero = 0xc2311456;
        (bool ok,) = deployed.call(abi.encodeWithSelector(selBumpIfNonZero, 11));
        require(!ok, "expected bumpIfNonZero revert on zero slot");
    }
}
