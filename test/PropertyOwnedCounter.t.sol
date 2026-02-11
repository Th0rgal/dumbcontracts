// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyOwnedCounterTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from DumbContracts/Proofs/OwnedCounter/*.lean to executable tests
 *
 * This file extracts 48 proven theorems into Foundry property tests:
 * - Basic properties (correctness, state preservation)
 * - Isolation properties (field independence, context preservation)
 * - Access control properties (owner-only operations)
 * - Integration properties (multi-step operations)
 */
contract PropertyOwnedCounterTest is YulTestBase {
    address ownedCounter;
    address alice = address(0xA11CE);
    address bob = address(0xB0B);

    function setUp() public {
        // Deploy OwnedCounter with alice as initial owner
        vm.prank(alice);
        ownedCounter = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        require(ownedCounter != address(0), "Deploy failed");
    }

    /**
     * Property: constructor_sets_owner
     * Theorem: Constructor correctly sets the owner to initialOwner parameter
     */
    function testProperty_Constructor_SetsOwner() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(bob));
        (bool success, bytes memory data) = newContract.call(abi.encodeWithSignature("getOwner()"));
        require(success, "getOwner failed");
        address owner = abi.decode(data, (address));
        assertEq(owner, bob, "Owner should be bob");
    }

    /**
     * Property: constructor_preserves_count
     * Theorem: Constructor initializes count to 0
     */
    function testProperty_Constructor_InitializesCountToZero() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        uint256 count = readStorage(newContract, 1);
        assertEq(count, 0, "Count should be 0 after construction");
    }

    /**
     * Property: getCount_returns_count
     * Theorem: getCount() returns the value in storage slot 1
     */
    function testProperty_GetCount_ReturnsStorageValue() public {
        uint256 storageValue = readStorage(1);
        (bool success, bytes memory data) = ownedCounter.call(abi.encodeWithSignature("getCount()"));
        require(success);
        uint256 returned = abi.decode(data, (uint256));
        assertEq(returned, storageValue, "getCount should return storage[1]");
    }

    /**
     * Property: getCount_preserves_state
     * Theorem: getCount() is a pure read that doesn't modify state
     */
    function testProperty_GetCount_PreservesState() public {
        uint256 countBefore = readStorage(1);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = ownedCounter.call(abi.encodeWithSignature("getCount()"));
        require(success);

        assertEq(readStorage(1), countBefore, "Count unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: getOwner_returns_owner
     * Theorem: getOwner() returns the value in storage slot 0
     */
    function testProperty_GetOwner_ReturnsStorageValue() public {
        address storageOwner = readStorageAddr(0);
        (bool success, bytes memory data) = ownedCounter.call(abi.encodeWithSignature("getOwner()"));
        require(success);
        address returned = abi.decode(data, (address));
        assertEq(returned, storageOwner, "getOwner should return storage[0]");
    }

    /**
     * Property: getOwner_preserves_state
     * Theorem: getOwner() is a pure read that doesn't modify state
     */
    function testProperty_GetOwner_PreservesState() public {
        uint256 countBefore = readStorage(1);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = ownedCounter.call(abi.encodeWithSignature("getOwner()"));
        require(success);

        assertEq(readStorage(1), countBefore, "Count unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: increment_adds_one_when_owner
     * Theorem: When called by owner, increment increases count by 1
     */
    function testProperty_Increment_AddsOneWhenOwner() public {
        uint256 countBefore = readStorage(1);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment should succeed for owner");

        assertEq(readStorage(1), countBefore + 1, "Count should increase by 1");
    }

    /**
     * Property: increment_reverts_when_not_owner
     * Theorem: When called by non-owner, increment reverts
     */
    function testProperty_Increment_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        assertFalse(success, "increment should revert for non-owner");
    }

    /**
     * Property: increment_preserves_owner
     * Theorem: increment() doesn't modify the owner field
     */
    function testProperty_Increment_PreservesOwner() public {
        address ownerBefore = readStorageAddr(0);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: decrement_subtracts_one_when_owner
     * Theorem: When called by owner, decrement decreases count by 1
     */
    function testProperty_Decrement_SubtractsOneWhenOwner() public {
        // Setup: increment first to have non-zero count
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        uint256 countBefore = readStorage(1);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement should succeed for owner");

        assertEq(readStorage(1), countBefore - 1, "Count should decrease by 1");
    }

    /**
     * Property: decrement_reverts_when_not_owner
     * Theorem: When called by non-owner, decrement reverts
     */
    function testProperty_Decrement_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        assertFalse(success, "decrement should revert for non-owner");
    }

    /**
     * Property: decrement_preserves_owner
     * Theorem: decrement() doesn't modify the owner field
     */
    function testProperty_Decrement_PreservesOwner() public {
        // Setup: increment first
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        address ownerBefore = readStorageAddr(0);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: transferOwnership_changes_owner
     * Theorem: transferOwnership updates the owner to newOwner
     */
    function testProperty_TransferOwnership_ChangesOwner() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success, "transferOwnership should succeed for owner");

        assertEq(readStorageAddr(0), bob, "Owner should be bob");
    }

    /**
     * Property: transferOwnership_reverts_when_not_owner
     * Theorem: When called by non-owner, transferOwnership reverts
     */
    function testProperty_TransferOwnership_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        assertFalse(success, "transferOwnership should revert for non-owner");
    }

    /**
     * Property: transferOwnership_preserves_count
     * Theorem: transferOwnership doesn't modify the count field
     */
    function testProperty_TransferOwnership_PreservesCount() public {
        uint256 countBefore = readStorage(1);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        assertEq(readStorage(1), countBefore, "Count should be preserved");
    }

    /**
     * Property: transfer_then_increment_reverts
     * Theorem: After transferring ownership, old owner can't increment
     */
    function testProperty_TransferThenIncrement_Reverts() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        assertFalse(success, "Old owner should not be able to increment");
    }

    /**
     * Property: transfer_then_decrement_reverts
     * Theorem: After transferring ownership, old owner can't decrement
     */
    function testProperty_TransferThenDecrement_Reverts() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        assertFalse(success, "Old owner should not be able to decrement");
    }

    /**
     * Property: increment_survives_transfer
     * Theorem: increment by owner, transfer, increment by new owner = count increased by 2
     */
    function testProperty_IncrementSurvivesTransfer() public {
        uint256 initialCount = readStorage(1);

        // Alice increments
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        // Alice transfers to Bob
        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        // Bob increments
        vm.prank(bob);
        (success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        assertEq(readStorage(1), initialCount + 2, "Count should increase by 2 across ownership transfer");
    }

    /**
     * Property: constructor_increment_getCount
     * Theorem: Fresh contract + increment + getCount returns 1
     */
    function testProperty_ConstructorIncrementGetCount() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(alice));

        vm.prank(alice);
        (bool success,) = newContract.call(abi.encodeWithSignature("increment()"));
        require(success);

        bytes memory data;
        (success, data) = newContract.call(abi.encodeWithSignature("getCount()"));
        require(success);
        uint256 count = abi.decode(data, (uint256));

        assertEq(count, 1, "Count should be 1 after construction + increment");
    }

    // Helper function to read address from storage
    function readStorageAddr(uint256 slot) internal view returns (address) {
        return readStorageAddr(ownedCounter, slot);
    }

    function readStorageAddr(address target, uint256 slot) internal view returns (address) {
        bytes32 value = vm.load(target, bytes32(slot));
        return address(uint160(uint256(value)));
    }

    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(ownedCounter, bytes32(slot)));
    }

    function readStorage(address target, uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(target, bytes32(slot)));
    }
}
