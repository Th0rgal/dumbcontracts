// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/DumbLoan.sol";

contract DumbLoanTest is Test {
    DumbLoan private loan;

    address private constant ALICE = address(0xA11CE);

    function setUp() public {
        // 150% health factor
        loan = new DumbLoan(1.5e18);
    }

    function testApplyUpdateHappy() public {
        loan.applyUpdate(ALICE, 150 ether, 100 ether, 0, 0);

        (uint256 collateral, uint256 debt) = loan.positions(ALICE);
        assertEq(collateral, 150 ether);
        assertEq(debt, 100 ether);
    }

    function testRejectsHealthFactor() public {
        vm.expectRevert(DumbLoan.HealthFactor.selector);
        loan.applyUpdate(ALICE, 120 ether, 100 ether, 0, 0);
    }

    function testRejectsStaleProof() public {
        loan.applyUpdate(ALICE, 150 ether, 100 ether, 0, 0);

        vm.expectRevert(DumbLoan.StaleProof.selector);
        loan.applyUpdate(ALICE, 200 ether, 50 ether, 0, 0);
    }
}
