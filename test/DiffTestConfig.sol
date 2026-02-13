// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

abstract contract DiffTestConfig is Test {
    function _diffRandomOverride() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_COUNT", uint256(0));
    }

    function _diffRandomSmallCount() internal view returns (uint256) {
        uint256 overrideCount = _diffRandomOverride();
        if (overrideCount != 0) {
            return overrideCount;
        }
        return vm.envOr("DIFFTEST_RANDOM_SMALL", uint256(100));
    }

    function _diffRandomLargeCount() internal view returns (uint256) {
        uint256 overrideCount = _diffRandomOverride();
        if (overrideCount != 0) {
            return overrideCount;
        }
        return vm.envOr("DIFFTEST_RANDOM_LARGE", uint256(10000));
    }

    function _diffRandomSeed() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_SEED", uint256(42));
    }

    function _assertRandomSuccess(bool success, uint256 iteration) internal {
        if (!success) {
            emit log_named_uint("Random test failed at", iteration);
            fail();
        }
    }
}
