// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice "Dumb" token that accepts state-diff proofs (old/new values) for a transfer.
contract DumbToken {
    error ZeroAddress();
    error StaleProof();
    error InsufficientBalance();
    error SupplyDrift();

    mapping(address => uint256) public balance;
    uint256 public totalSupply;

    constructor(address owner, uint256 supply) {
        if (owner == address(0)) revert ZeroAddress();
        totalSupply = supply;
        balance[owner] = supply;
    }

    /// @notice Apply a transfer given old/new values as a simple "proof".
    /// @dev This is intentionally minimal to model a state-diff validator pattern.
    function applyTransfer(
        address from,
        address to,
        uint256 amount,
        uint256 oldFrom,
        uint256 oldTo,
        uint256 oldTotal,
        uint256 newFrom,
        uint256 newTo
    ) external {
        if (to == address(0)) revert ZeroAddress();
        if (oldFrom != balance[from] || oldTo != balance[to] || oldTotal != totalSupply) {
            revert StaleProof();
        }
        if (oldFrom < amount) revert InsufficientBalance();

        if (newFrom != oldFrom - amount || newTo != oldTo + amount) revert SupplyDrift();
        if (newFrom + newTo != oldFrom + oldTo) revert SupplyDrift();

        balance[from] = newFrom;
        balance[to] = newTo;
    }
}
