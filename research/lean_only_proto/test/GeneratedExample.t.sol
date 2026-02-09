// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedExampleTest is GeneratedBase {
    function testExampleStorageOps() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selGet = 0x7eba7ba6;
        bytes4 selSet = 0xf2c298be;
        bytes4 selAdd = 0x02222aec;
        bytes4 selGuarded = 0x49f583e3;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 1, 41));
        require(ok, "setSlot failed");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 1));
        require(ok, "getSlot failed");
        uint256 val = abi.decode(data, (uint256));
        require(val == 41, "unexpected getSlot value");

        (ok,) = deployed.call(abi.encodeWithSelector(selAdd, 1, 1));
        require(ok, "addSlot failed");

        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 1));
        require(ok, "getSlot after add failed");
        val = abi.decode(data, (uint256));
        require(val == 42, "unexpected addSlot value");

        (ok,) = deployed.call(abi.encodeWithSelector(selGuarded, 1, 1));
        require(ok, "guardedAddSlot failed");
    }
}
