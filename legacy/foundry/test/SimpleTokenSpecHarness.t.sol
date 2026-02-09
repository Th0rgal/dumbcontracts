// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/SimpleTokenSpecHarness.sol";

contract SimpleTokenSpecHarnessTest is Test {
    SimpleTokenSpecHarness private token;

    address private constant ALICE = address(0xA11CE);
    address private constant BOB = address(0xB0B);

    function setUp() public {
        token = new SimpleTokenSpecHarness(ALICE, 1_000e18);
    }

    function testTransferSpecHappy() public {
        vm.prank(ALICE);
        token.transfer_spec(BOB, 250e18);

        assertEq(token.balance(ALICE), 750e18);
        assertEq(token.balance(BOB), 250e18);
        assertEq(token.totalSupply(), 1_000e18);
    }

    function testTransferSpecRejectsZeroAddress() public {
        vm.prank(ALICE);
        vm.expectRevert();
        token.transfer_spec(address(0), 1e18);
    }

    function testTransferSpecRejectsInsufficientBalance() public {
        vm.prank(BOB);
        vm.expectRevert();
        token.transfer_spec(ALICE, 1e18);
    }
}
