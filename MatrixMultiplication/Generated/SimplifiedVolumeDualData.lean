import MatrixMultiplication.Generated.SimplifiedVolumeRootDualData0
import MatrixMultiplication.Generated.SimplifiedVolumePos4DualData0
import MatrixMultiplication.Generated.SimplifiedVolumePos4DualData1
import MatrixMultiplication.Generated.SimplifiedVolumePos4DualData2
import MatrixMultiplication.Generated.SimplifiedVolumePos4DualData3
import MatrixMultiplication.Generated.SimplifiedVolumePos3DualData0
import MatrixMultiplication.Generated.SimplifiedVolumePos3DualData1
import MatrixMultiplication.Generated.SimplifiedVolumePos3DualData2
import MatrixMultiplication.Generated.SimplifiedVolumePos3DualData3

/-! # Simplified volume dual certificate data

This generated opt-in module aggregates independently checked chunks. -/

namespace MatrixMultiplication.Generated.SimplifiedVolume

def dualValueCount : ℕ :=
  RootDualData0.data.valueCount +
      Pos4DualData0.data.valueCount +
      Pos4DualData1.data.valueCount +
      Pos4DualData2.data.valueCount +
      Pos4DualData3.data.valueCount +
      Pos3DualData0.data.valueCount +
      Pos3DualData1.data.valueCount +
      Pos3DualData2.data.valueCount +
      Pos3DualData3.data.valueCount

theorem dualValueCount_eq : dualValueCount = 12690 := by
  unfold dualValueCount
  rw [RootDualData0.valueCount_eq, Pos4DualData0.valueCount_eq, Pos4DualData1.valueCount_eq, Pos4DualData2.valueCount_eq, Pos4DualData3.valueCount_eq, Pos3DualData0.valueCount_eq, Pos3DualData1.valueCount_eq, Pos3DualData2.valueCount_eq, Pos3DualData3.valueCount_eq]

def rootDualChunks : Array Float32BitsChunk := #[RootDualData0.data]

def rootDualChunkRanges : Array (ℕ × ℕ) := #[(0, 6)]

theorem rootDualChunkRanges_pairwise :
    rootDualChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def pos4DualChunks : Array Float32BitsChunk := #[Pos4DualData0.data, Pos4DualData1.data, Pos4DualData2.data, Pos4DualData3.data]

def pos4DualChunkRanges : Array (ℕ × ℕ) := #[(114, 782), (787, 1178), (1183, 3354), (3359, 3648)]

theorem pos4DualChunkRanges_pairwise :
    pos4DualChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def pos3DualChunks : Array Float32BitsChunk := #[Pos3DualData0.data, Pos3DualData1.data, Pos3DualData2.data, Pos3DualData3.data]

def pos3DualChunkRanges : Array (ℕ × ℕ) := #[(6, 246), (246, 434), (434, 640), (640, 732)]

theorem pos3DualChunkRanges_pairwise :
    pos3DualChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide


end MatrixMultiplication.Generated.SimplifiedVolume
