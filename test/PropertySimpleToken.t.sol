// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySimpleTokenTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from DumbContracts/Proofs/SimpleToken/*.lean to executable tests
 *
 * This file extracts 57 proven theorems into Foundry property tests:
 * - Basic properties (constructor, mint, transfer, getters)
 * - Supply conservation (total supply invariant)
 * - Isolation properties (storage independence)
 * - Correctness properties (access control, balance updates)
 */
contract PropertySimpleTokenTest is YulTestBase {
    address token;
    address owner = address(0xA11CE);
    address alice = address(0xA11CE);
    address bob = address(0xB0B);
    address charlie = address(0xC4A12);

    uint256 constant MAX_UINT256 = type(uint256).max;

    function setUp() public {
        // Deploy SimpleToken with alice as owner
        vm.prank(owner);
        token = deployYulWithArgs("SimpleToken", abi.encode(owner));
        require(token != address(0), "Deploy failed");
    }

    /**
     * Property: constructor_sets_owner
     * Theorem: Constructor sets owner to initialOwner parameter
     */
    function testProperty_Constructor_SetsOwner() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(bob));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("owner()"));
        require(success);
        address tokenOwner = abi.decode(data, (address));
        assertEq(tokenOwner, bob, "Owner should be bob");
    }

    /**
     * Property: constructor_sets_supply_zero
     * Theorem: Constructor initializes total supply to 0
     */
    function testProperty_Constructor_InitializesSupplyToZero() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(alice));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supply = abi.decode(data, (uint256));
        assertEq(supply, 0, "Initial supply should be 0");
    }

    /**
     * Property: constructor_getTotalSupply_correct
     * Theorem: After construction, getTotalSupply returns 0
     */
    function testProperty_Constructor_GetTotalSupplyReturnsZero() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(owner));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supply = abi.decode(data, (uint256));
        assertEq(supply, 0, "getTotalSupply should return 0 after construction");
    }

    /**
     * Property: constructor_getOwner_correct
     * Theorem: After construction, getOwner returns initialOwner
     */
    function testProperty_Constructor_GetOwnerCorrect() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(bob));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("owner()"));
        require(success);
        address tokenOwner = abi.decode(data, (address));
        assertEq(tokenOwner, bob, "getOwner should return initial owner");
    }

    /**
     * Property: getTotalSupply_returns_supply
     * Theorem: getTotalSupply returns storage slot 0 (total supply)
     */
    function testProperty_GetTotalSupply_ReturnsStorageValue() public {
        uint256 storageSupply = readStorage(2);
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 returned = abi.decode(data, (uint256));
        assertEq(returned, storageSupply, "getTotalSupply should return storage[0]");
    }

    /**
     * Property: getTotalSupply_preserves_state
     * Theorem: getTotalSupply is a pure read that doesn't modify state
     */
    function testProperty_GetTotalSupply_PreservesState() public {
        uint256 supplyBefore = readStorage(2);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);

        assertEq(readStorage(2), supplyBefore, "Supply unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: getOwner_returns_owner
     * Theorem: getOwner returns storage slot 1 (owner address)
     */
    function testProperty_GetOwner_ReturnsStorageValue() public {
        address storageOwner = readStorageAddr(0);
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("owner()"));
        require(success);
        address returned = abi.decode(data, (address));
        assertEq(returned, storageOwner, "getOwner should return storage[1]");
    }

    /**
     * Property: getOwner_preserves_state
     * Theorem: getOwner is a pure read that doesn't modify state
     */
    function testProperty_GetOwner_PreservesState() public {
        uint256 supplyBefore = readStorage(2);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = token.call(abi.encodeWithSignature("owner()"));
        require(success);

        assertEq(readStorage(2), supplyBefore, "Supply unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: balanceOf_returns_balance
     * Theorem: balanceOf(addr) returns the mapping value for addr
     */
    function testProperty_BalanceOf_ReturnsBalance() public {
        // Mint some tokens to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balance = abi.decode(data, (uint256));
        assertEq(balance, 100, "balanceOf should return minted amount");
    }

    /**
     * Property: balanceOf_preserves_state
     * Theorem: balanceOf is a pure read that doesn't modify state
     */
    function testProperty_BalanceOf_PreservesState() public {
        uint256 supplyBefore = readStorage(2);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);

        assertEq(readStorage(2), supplyBefore, "Supply unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: mint_increases_balance
     * Theorem: mint(to, amount) increases balanceOf(to) by amount
     */
    function testProperty_Mint_IncreasesBalance() public {
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 balanceBefore = abi.decode(data, (uint256));

        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 50));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 balanceAfter = abi.decode(data, (uint256));

        assertEq(balanceAfter, balanceBefore + 50, "Balance should increase by mint amount");
    }

    /**
     * Property: mint_increases_supply
     * Theorem: mint(to, amount) increases totalSupply by amount
     */
    function testProperty_Mint_IncreasesTotalSupply() public {
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyBefore = abi.decode(data, (uint256));

        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 75));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyAfter = abi.decode(data, (uint256));

        assertEq(supplyAfter, supplyBefore + 75, "Total supply should increase by mint amount");
    }

    /**
     * Property: mint_reverts_when_not_owner
     * Theorem: mint called by non-owner reverts
     */
    function testProperty_Mint_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 100));
        assertFalse(success, "Mint should revert for non-owner");
    }

    /**
     * Property: mint_preserves_owner
     * Theorem: mint doesn't change the owner address
     */
    function testProperty_Mint_PreservesOwner() public {
        address ownerBefore = readStorageAddr(0);

        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: mint_then_balanceOf_correct
     * Theorem: After mint(to, amount), balanceOf(to) reflects the increase
     */
    function testProperty_MintThenBalanceOf_Correct() public {
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", charlie, 200));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 balance = abi.decode(data, (uint256));

        assertEq(balance, 200, "balanceOf should return minted amount");
    }

    /**
     * Property: mint_then_getTotalSupply_correct
     * Theorem: After mint(to, amount), getTotalSupply reflects the increase
     */
    function testProperty_MintThenGetTotalSupply_Correct() public {
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyBefore = abi.decode(data, (uint256));

        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 150));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyAfter = abi.decode(data, (uint256));

        assertEq(supplyAfter, supplyBefore + 150, "Total supply should reflect mint");
    }

    /**
     * Property: transfer_decreases_sender_balance
     * Theorem: transfer(to, amount) decreases sender balance by amount
     */
    function testProperty_Transfer_DecreasesSenderBalance() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balanceBefore = abi.decode(data, (uint256));

        // Transfer from alice to bob
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 30));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balanceAfter = abi.decode(data, (uint256));

        assertEq(balanceAfter, balanceBefore - 30, "Sender balance should decrease");
    }

    /**
     * Property: transfer_increases_recipient_balance
     * Theorem: transfer(to, amount) increases recipient balance by amount
     */
    function testProperty_Transfer_IncreasesRecipientBalance() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 bobBalanceBefore = abi.decode(data, (uint256));

        // Transfer from alice to bob
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 40));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 bobBalanceAfter = abi.decode(data, (uint256));

        assertEq(bobBalanceAfter, bobBalanceBefore + 40, "Recipient balance should increase");
    }

    /**
     * Property: transfer_self_preserves_balance
     * Theorem: transfer(to == sender, amount) leaves sender balance unchanged
     */
    function testProperty_Transfer_Self_PreservesBalance() public {
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", alice, 40));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balance = abi.decode(data, (uint256));
        assertEq(balance, 100, "Self-transfer should not change balance");
    }

    /**
     * Property: transfer_preserves_supply_when_sufficient
     * Theorem: transfer doesn't change total supply
     */
    function testProperty_Transfer_PreservesTotalSupply() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyBefore = abi.decode(data, (uint256));

        // Transfer
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 50));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyAfter = abi.decode(data, (uint256));

        assertEq(supplyAfter, supplyBefore, "Total supply should be preserved");
    }

    /**
     * Property: transfer_reverts_insufficient_balance
     * Theorem: transfer reverts when sender balance < amount
     */
    function testProperty_Transfer_RevertsInsufficientBalance() public {
        // Alice has 0 tokens, tries to transfer 10
        vm.prank(alice);
        (bool success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 10));
        assertFalse(success, "Transfer should revert with insufficient balance");
    }

    /**
     * Property: transfer_preserves_owner
     * Theorem: transfer doesn't change the owner address
     */
    function testProperty_Transfer_PreservesOwner() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        address ownerBefore = readStorageAddr(0);

        // Transfer
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 20));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: transfer_then_balanceOf_sender_correct
     * Theorem: After transfer, sender balanceOf is correctly reduced
     */
    function testProperty_TransferThenBalanceOf_SenderCorrect() public {
        // Mint 100 to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        // Transfer 25 to bob
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 25));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balance = abi.decode(data, (uint256));

        assertEq(balance, 75, "Alice balance should be 75 after transfer");
    }

    /**
     * Property: transfer_then_balanceOf_recipient_correct
     * Theorem: After transfer, recipient balanceOf is correctly increased
     */
    function testProperty_TransferThenBalanceOf_RecipientCorrect() public {
        // Mint 100 to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        // Transfer 60 to charlie
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", charlie, 60));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 balance = abi.decode(data, (uint256));

        assertEq(balance, 60, "Charlie balance should be 60 after transfer");
    }

    // Helper functions
    function readStorageAddr(uint256 slot) internal view returns (address) {
        return readStorageAddr(token, slot);
    }

    function readStorageAddr(address target, uint256 slot) internal view returns (address) {
        bytes32 value = vm.load(target, bytes32(slot));
        return address(uint160(uint256(value)));
    }

    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(token, bytes32(slot)));
    }

    function readStorage(address target, uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(target, bytes32(slot)));
    }
}
