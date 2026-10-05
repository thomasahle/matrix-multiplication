import MatrixMultiplication.Generated.SimplifiedVolumeSchema

/-! # Simplified volume certificate provenance manifest

This generated manifest binds the sparse Lean boundary to its binary certificate, archived static
program, source 32-bit certificate, certified result, and generator by full SHA-256 digests.
-/

namespace MatrixMultiplication.Generated.TotalQuotientPrimary.Manifest

def schema : String := "simplified-volume-lean-boundary-v1"
def certificateSHA256 : String := "e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3"
def archiveSHA256 : String := "1087c436aa466c3185770dad7e53a50b260460dcb712645776c319a81197bb7b"
def sourceCertificateSHA256 : String := "7a255f50ab903cb7f3da56d93ceccfff3acf39061463115655d7f3f63e746481"
def certifiedResultSHA256 : String := "463d6eda3e279535b7fba389486139b9cb4f00a70da2030f246cc5f760224158"
def generatorSHA256 : String := "272dc0e21cd5c63842d377215129ea3810c18f432e78490562eca64f2ae1ee6e"
def coarseningSpecification : String := "2:1=0|0;2:2=0|0|0;2:3=0|0"
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

end MatrixMultiplication.Generated.TotalQuotientPrimary.Manifest
