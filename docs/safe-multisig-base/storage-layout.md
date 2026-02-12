# Safe Base Storage Layout (v1.5.0)

This document records the linearized storage layout for the Safe base contract
based on the pinned source snapshot in `docs/safe-multisig-base/source/`.

Slot | Field | Type | Declared In
--- | --- | --- | ---
0 | `singleton` | `address` | `common/Singleton.sol`
1 | `modules` | `mapping(address => address)` | `base/ModuleManager.sol`
2 | `owners` | `mapping(address => address)` | `base/OwnerManager.sol`
3 | `ownerCount` | `uint256` | `base/OwnerManager.sol`
4 | `threshold` | `uint256` | `base/OwnerManager.sol`
5 | `nonce` | `uint256` | `Safe.sol`
6 | `_deprecatedDomainSeparator` | `bytes32` | `Safe.sol`
7 | `signedMessages` | `mapping(bytes32 => uint256)` | `Safe.sol`
8 | `approvedHashes` | `mapping(address => mapping(bytes32 => uint256))` | `Safe.sol`

Additional fixed storage slots (set via `sstore` with explicit hashes):
- `GUARD_STORAGE_SLOT` = `0x4a204f620c8c5ccdca3fd54d003badd85ba500436a431f0cbda4f558c93c34c8`
- `FALLBACK_HANDLER_STORAGE_SLOT` = `0x6c9a6c4a39284e37ed1cf53d337577d14212a4870fb976a4366c693b939918d5`
- `MODULE_GUARD_STORAGE_SLOT` = `0xb104e0b93118902c651344349b610029d694cfdec91c589c91ebafbcd0289947`

Notes:
- Mapping key types and nested mappings are not yet modeled in the EDSL.
- `singleton` must remain slot 0 to stay compatible with the Safe proxy layout.
