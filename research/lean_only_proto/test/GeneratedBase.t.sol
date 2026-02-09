// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface Vm {
    function readFile(string calldata path) external returns (string memory);
}

abstract contract GeneratedBase {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function _readHexFile(string memory path) internal returns (bytes memory) {
        string memory hexStr = vm.readFile(path);
        return _fromHex(hexStr);
    }

    function _deploy(bytes memory creationCode) internal returns (address deployed) {
        assembly {
            deployed := create(0, add(creationCode, 0x20), mload(creationCode))
        }
        require(deployed != address(0), "create failed");
    }

    function _fromHex(string memory s) internal pure returns (bytes memory) {
        bytes memory str = bytes(s);
        bytes memory out = new bytes(str.length / 2);
        uint256 outLen = 0;
        uint256 hi = 0;
        bool haveHi = false;
        for (uint256 i = 0; i < str.length; i++) {
            uint8 c = uint8(str[i]);
            int8 v = _hexVal(c);
            if (v < 0) {
                continue;
            }
            if (!haveHi) {
                hi = uint8(v);
                haveHi = true;
            } else {
                out[outLen] = bytes1(uint8(hi * 16 + uint8(v)));
                outLen++;
                haveHi = false;
            }
        }
        require(!haveHi, "hex odd length");
        assembly {
            mstore(out, outLen)
        }
        return out;
    }

    function _hexVal(uint8 c) internal pure returns (int8) {
        if (c >= 48 && c <= 57) {
            return int8(int256(uint256(c - 48)));
        }
        if (c >= 65 && c <= 70) {
            return int8(int256(uint256(c - 65 + 10)));
        }
        if (c >= 97 && c <= 102) {
            return int8(int256(uint256(c - 97 + 10)));
        }
        return -1;
    }
}
