// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice "Dumb" loan position that enforces a health-factor invariant.
contract DumbLoan {
    error StaleProof();
    error HealthFactor();

    struct Position {
        uint256 collateral;
        uint256 debt;
    }

    uint256 public immutable minHealthFactor;
    mapping(address => Position) public positions;

    /// @param minHealthFactor_ Scaled by 1e18 (e.g., 1.25e18 = 125%).
    constructor(uint256 minHealthFactor_) {
        minHealthFactor = minHealthFactor_;
    }

    function applyUpdate(address user, uint256 newCollateral, uint256 newDebt, uint256 oldCollateral, uint256 oldDebt)
        external
    {
        Position storage pos = positions[user];
        if (pos.collateral != oldCollateral || pos.debt != oldDebt) revert StaleProof();

        // Enforce collateralValue >= debt * minHealthFactor (scaled).
        if (newDebt > 0) {
            if (newCollateral * 1e18 < newDebt * minHealthFactor) revert HealthFactor();
        }

        pos.collateral = newCollateral;
        pos.debt = newDebt;
    }
}
