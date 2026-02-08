// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/DumbToken.sol";

contract DumbTokenTest is Test {
    DumbToken private token;

    address private constant ALICE = address(0xA11CE);
    address private constant BOB = address(0xB0B);

    function setUp() public {
        token = new DumbToken(ALICE, 100);
    }

    function testApplyTransferHappy() public {
        uint256 oldFrom = token.balance(ALICE);
        uint256 oldTo = token.balance(BOB);
        uint256 oldTotal = token.totalSupply();

        token.applyTransfer(ALICE, BOB, 25, oldFrom, oldTo, oldTotal, 75, 25);

        assertEq(token.balance(ALICE), 75);
        assertEq(token.balance(BOB), 25);
        assertEq(token.totalSupply(), 100);
    }

    function testRejectsZeroTo() public {
        vm.expectRevert(DumbToken.ZeroAddress.selector);
        token.applyTransfer(ALICE, address(0), 1, 100, 0, 100, 99, 1);
    }

    function testRejectsStaleProof() public {
        vm.expectRevert(DumbToken.StaleProof.selector);
        token.applyTransfer(ALICE, BOB, 1, 99, 0, 100, 98, 1);
    }

    function testRejectsInsufficientBalance() public {
        uint256 oldFrom = token.balance(ALICE);
        uint256 oldTo = token.balance(BOB);
        uint256 oldTotal = token.totalSupply();

        vm.expectRevert(DumbToken.InsufficientBalance.selector);
        token.applyTransfer(ALICE, BOB, 200, oldFrom, oldTo, oldTotal, 0, 200);
    }

    function testRejectsSupplyDrift() public {
        uint256 oldFrom = token.balance(ALICE);
        uint256 oldTo = token.balance(BOB);
        uint256 oldTotal = token.totalSupply();

        vm.expectRevert(DumbToken.SupplyDrift.selector);
        token.applyTransfer(ALICE, BOB, 10, oldFrom, oldTo, oldTotal, 80, 25);
    }
}
