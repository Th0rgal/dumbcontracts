// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "../examples/solidity/Vault.sol";

contract VaultTest is Test {
    Vault internal vault;
    address internal alice = address(0xA11CE);
    address internal bob = address(0xB0B);

    function setUp() public {
        vault = new Vault();
    }

    function test_InitialState() public view {
        assertEq(vault.totalAssets(), 0);
        assertEq(vault.totalSupply(), 0);
        assertEq(vault.balanceOf(alice), 0);
    }

    function test_DepositMintsSharesOneToOne() public {
        vm.prank(alice);
        vault.deposit(100);

        assertEq(vault.balanceOf(alice), 100);
        assertEq(vault.totalAssets(), 100);
        assertEq(vault.totalSupply(), 100);
    }

    function test_WithdrawBurnsSharesOneToOne() public {
        vm.startPrank(alice);
        vault.deposit(100);
        vault.withdraw(40);
        vm.stopPrank();

        assertEq(vault.balanceOf(alice), 60);
        assertEq(vault.totalAssets(), 60);
        assertEq(vault.totalSupply(), 60);
    }

    function test_WithdrawRevertsWhenSharesInsufficient() public {
        vm.prank(alice);
        vault.deposit(10);

        vm.prank(alice);
        vm.expectRevert(Vault.InsufficientShares.selector);
        vault.withdraw(11);
    }

    function test_MultipleDepositorsConserveTotals() public {
        vm.prank(alice);
        vault.deposit(70);

        vm.prank(bob);
        vault.deposit(30);

        assertEq(vault.balanceOf(alice), 70);
        assertEq(vault.balanceOf(bob), 30);
        assertEq(vault.totalAssets(), 100);
        assertEq(vault.totalSupply(), 100);
    }

    function testFuzz_DepositWithdrawRoundTrip(uint128 amount) public {
        vm.prank(alice);
        vault.deposit(amount);

        vm.prank(alice);
        vault.withdraw(amount);

        assertEq(vault.balanceOf(alice), 0);
        assertEq(vault.totalAssets(), 0);
        assertEq(vault.totalSupply(), 0);
    }
}
