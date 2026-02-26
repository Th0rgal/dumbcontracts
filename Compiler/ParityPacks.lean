import Compiler.Codegen

namespace Compiler

/-- Pinned Solidity tuple metadata for one parity pack. -/
structure ParityTargetTuple where
  solcVersion : String
  solcCommit : String
  optimizerRuns : Nat
  viaIR : Bool
  evmVersion : String
  metadataMode : String
  deriving Repr, DecidableEq

/-- Versioned parity-pack selection unit. -/
structure ParityPack where
  id : String
  compat : ParityTargetTuple
  backendProfile : BackendProfile
  forcePatches : Bool
  defaultPatchMaxIterations : Nat
  deriving Repr, DecidableEq

def solc_0_8_28_o200_viair_false_evm_shanghai : ParityPack :=
  { id := "solc-0.8.28-o200-viair-false-evm-shanghai"
    compat := {
      solcVersion := "0.8.28"
      solcCommit := "7893614a"
      optimizerRuns := 200
      viaIR := false
      evmVersion := "shanghai"
      metadataMode := "default"
    }
    backendProfile := .solidityParity
    forcePatches := true
    defaultPatchMaxIterations := 2
  }

def solc_0_8_28_o999999_viair_true_evm_paris : ParityPack :=
  { id := "solc-0.8.28-o999999-viair-true-evm-paris"
    compat := {
      solcVersion := "0.8.28"
      solcCommit := "7893614a"
      optimizerRuns := 999999
      viaIR := true
      evmVersion := "paris"
      metadataMode := "none"
    }
    backendProfile := .solidityParity
    forcePatches := true
    defaultPatchMaxIterations := 2
  }

def allParityPacks : List ParityPack :=
  [solc_0_8_28_o200_viair_false_evm_shanghai,
   solc_0_8_28_o999999_viair_true_evm_paris]

def supportedParityPackIds : List String :=
  allParityPacks.map (·.id)

def findParityPack? (packId : String) : Option ParityPack :=
  allParityPacks.find? (fun pack => pack.id = packId)

end Compiler
