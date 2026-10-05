import MatrixMultiplication.Generated.SimplifiedVolumeSchema

/-! # Simplified volume certificate provenance manifest

This generated manifest binds the sparse Lean boundary to its binary certificate, archived static
program, source 32-bit certificate, certified result, and generator by full SHA-256 digests.
-/

namespace MatrixMultiplication.Generated.SimplifiedVolume.Manifest

def schema : String := "simplified-volume-lean-boundary-v1"
def certificateSHA256 : String := "eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082"
def archiveSHA256 : String := "1087c436aa466c3185770dad7e53a50b260460dcb712645776c319a81197bb7b"
def sourceCertificateSHA256 : String := "7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481"
def certifiedResultSHA256 : String := "9d0f8cf1e6cefe651d3e5b476a7b0b61fc12f2d3a4afaf8e34f209cf6051e284"
def generatorSHA256 : String := "002700ad998fd4e91ec58fd1c3b19e1a3a85bcd712a2d7078a1e6ef705d86a1e"
def topProbabilityBits : ℕ := 20
def localProbabilityBits : ℕ := 12
def activePrimaryValues : ℕ := 31419
def activeDualValues : ℕ := 12690

/-! Flattened semantic row conventions used by the sparse index maps. -/
def topZeroAtomCount : ℕ := 6 * 48
def topBranchAtomOffset : ℕ := topZeroAtomCount
def topBranchAtomCount : ℕ := 6 * 6 * 1785
def positiveLevelThreeRowCount : ℕ := 126
def positiveLevelThreeRegionRowCount : ℕ := 126 * 6
def edgeRowCount : ℕ := 126 * 6 * 10
def zeroLevelThreeRowCount : ℕ := 270
def zeroLevelFourRowCount : ℕ := 6 * 48
def rootDualRowWidth : ℕ := 3 * 17
def levelFourDualRowWidth : ℕ := 3 * 9
def levelThreeDualRowWidth : ℕ := 3 * 5

end MatrixMultiplication.Generated.SimplifiedVolume.Manifest
