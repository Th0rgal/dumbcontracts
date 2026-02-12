# Safe Multisig Base ABI (Pinned)

This ABI snapshot is derived from the pinned interfaces at v1.5.0
(commit `dc437e8`), including `ISafe` plus the base manager interfaces
it inherits (`IModuleManager`, `IGuardManager`, `IOwnerManager`,
`IFallbackManager`, `INativeCurrencyPaymentFallback`, `IStorageAccessible`),
as well as `ISignatureValidator`.

## Functions (ISafe)
- `setup(address[],uint256,address,bytes,address,address,uint256,address)`
- `execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)`
- `checkSignatures(address,bytes32,bytes)`
- `checkNSignatures(address,bytes32,bytes,uint256)`
- `approveHash(bytes32)`
- `domainSeparator()`
- `getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)`
- `VERSION()`
- `nonce()`
- `signedMessages(bytes32)`
- `approvedHashes(address,bytes32)`

## Functions (IModuleManager)
- `enableModule(address)`
- `disableModule(address,address)`
- `execTransactionFromModule(address,uint256,bytes,uint8)`
- `execTransactionFromModuleReturnData(address,uint256,bytes,uint8)`
- `isModuleEnabled(address)`
- `getModulesPaginated(address,uint256)`
- `setModuleGuard(address)`

## Functions (IGuardManager)
- `setGuard(address)`

## Functions (IOwnerManager)
- `addOwnerWithThreshold(address,uint256)`
- `removeOwner(address,address,uint256)`
- `swapOwner(address,address,address)`
- `changeThreshold(uint256)`
- `getThreshold()`
- `isOwner(address)`
- `getOwners()`

## Functions (IFallbackManager)
- `setFallbackHandler(address)`
- `fallback()` (no selector; fallback function)

## Functions (INativeCurrencyPaymentFallback)
- `receive()` (no selector; receive function)

## Functions (IStorageAccessible)
- `getStorageAt(uint256,uint256)`
- `simulateAndRevert(address,bytes)`

## Functions (ISignatureValidator)
- `isValidSignature(bytes32,bytes)`

## Events (ISafe)
- `SafeSetup(address,address[],uint256,address,address)`
- `ApproveHash(bytes32,address)`
- `SignMsg(bytes32)`
- `ExecutionFailure(bytes32,uint256)`
- `ExecutionSuccess(bytes32,uint256)`

## Events (IModuleManager)
- `EnabledModule(address)`
- `DisabledModule(address)`
- `ExecutionFromModuleSuccess(address)`
- `ExecutionFromModuleFailure(address)`
- `ChangedModuleGuard(address)`

## Events (IGuardManager)
- `ChangedGuard(address)`

## Events (IOwnerManager)
- `AddedOwner(address)`
- `RemovedOwner(address)`
- `ChangedThreshold(uint256)`

## Events (IFallbackManager)
- `ChangedFallbackHandler(address)`

## Events (INativeCurrencyPaymentFallback)
- `SafeReceived(address,uint256)`

## Notes
- ABI signatures are written with Solidity canonical types; `Enum.Operation`
  is represented as `uint8` in the signatures.
