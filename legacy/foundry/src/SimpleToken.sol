// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Minimal token to validate the spec-compiler pipeline with pre/post constraints.
contract SimpleToken {
    error ZeroAddress();
    error InsufficientBalance();

    mapping(address => uint256) public balance;
    uint256 public totalSupply;

    constructor(address owner, uint256 supply) {
        if (owner == address(0)) revert ZeroAddress();
        totalSupply = supply;
        balance[owner] = supply;
    }

    function transfer(address to, uint256 amount) public {
        if (to == address(0)) revert ZeroAddress();
        uint256 fromBalance = balance[msg.sender];
        if (fromBalance < amount) revert InsufficientBalance();

        unchecked {
            balance[msg.sender] = fromBalance - amount;
            balance[to] += amount;
        }
    }
}
