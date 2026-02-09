// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedHealthTest is GeneratedBase {
    function testHealthCheck() public {
        bytes memory creation = _readHexFile("out/health.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSet = 0xf978da39;
        bytes4 selCheck = 0x1753bbd7;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 100, 10, 2));
        require(ok, "setRisk ok failed");

        (ok,) = deployed.call(abi.encodeWithSelector(selCheck));
        require(ok, "checkHealth ok failed");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 10, 10, 2));
        require(ok, "setRisk bad failed");

        (ok,) = deployed.call(abi.encodeWithSelector(selCheck));
        require(!ok, "checkHealth expected revert");
    }
}
