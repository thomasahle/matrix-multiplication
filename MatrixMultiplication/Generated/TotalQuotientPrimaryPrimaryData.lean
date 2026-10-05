import MatrixMultiplication.Generated.TotalQuotientPrimaryTopData0
import MatrixMultiplication.Generated.TotalQuotientPrimaryTopData1
import MatrixMultiplication.Generated.TotalQuotientPrimaryPos3AData0
import MatrixMultiplication.Generated.TotalQuotientPrimaryPos3AlphaData0
import MatrixMultiplication.Generated.TotalQuotientPrimaryPos3AlphaData1
import MatrixMultiplication.Generated.TotalQuotientPrimaryEdgeZero2Data0
import MatrixMultiplication.Generated.TotalQuotientPrimaryEdgeZero2Data1
import MatrixMultiplication.Generated.TotalQuotientPrimaryEdgeZero2Data2
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero3Data0
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data0
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data1
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data2
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data3
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data4
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data5
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data6
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data7
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data8
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data9
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data10
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data11
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data12
import MatrixMultiplication.Generated.TotalQuotientPrimaryZero4Data13
import MatrixMultiplication.Generated.TotalQuotientPrimaryMuData0

/-! # Simplified volume primary certificate data

This generated opt-in module aggregates independently checked chunks. -/

namespace MatrixMultiplication.Generated.TotalQuotientPrimary

open MatrixMultiplication.Generated.SimplifiedVolume

def primaryValueCount : ℕ :=
  TopData0.data.valueCount +
      TopData1.data.valueCount +
      Pos3AData0.data.valueCount +
      Pos3AlphaData0.data.valueCount +
      Pos3AlphaData1.data.valueCount +
      EdgeZero2Data0.data.valueCount +
      EdgeZero2Data1.data.valueCount +
      EdgeZero2Data2.data.valueCount +
      Zero3Data0.data.valueCount +
      Zero4Data0.data.valueCount +
      Zero4Data1.data.valueCount +
      Zero4Data2.data.valueCount +
      Zero4Data3.data.valueCount +
      Zero4Data4.data.valueCount +
      Zero4Data5.data.valueCount +
      Zero4Data6.data.valueCount +
      Zero4Data7.data.valueCount +
      Zero4Data8.data.valueCount +
      Zero4Data9.data.valueCount +
      Zero4Data10.data.valueCount +
      Zero4Data11.data.valueCount +
      Zero4Data12.data.valueCount +
      Zero4Data13.data.valueCount +
      MuData0.data.valueCount

theorem primaryValueCount_eq : primaryValueCount = 31419 := by
  unfold primaryValueCount
  rw [TopData0.valueCount_eq, TopData1.valueCount_eq, Pos3AData0.valueCount_eq, Pos3AlphaData0.valueCount_eq, Pos3AlphaData1.valueCount_eq, EdgeZero2Data0.valueCount_eq, EdgeZero2Data1.valueCount_eq, EdgeZero2Data2.valueCount_eq, Zero3Data0.valueCount_eq, Zero4Data0.valueCount_eq, Zero4Data1.valueCount_eq, Zero4Data2.valueCount_eq, Zero4Data3.valueCount_eq, Zero4Data4.valueCount_eq, Zero4Data5.valueCount_eq, Zero4Data6.valueCount_eq, Zero4Data7.valueCount_eq, Zero4Data8.valueCount_eq, Zero4Data9.valueCount_eq, Zero4Data10.valueCount_eq, Zero4Data11.valueCount_eq, Zero4Data12.valueCount_eq, Zero4Data13.valueCount_eq, MuData0.valueCount_eq]

def topChunks : Array SparseMassChunk := #[TopData0.data, TopData1.data]

def topChunkRanges : Array (ℕ × ℕ) := #[(51, 14534), (14534, 64278)]

theorem topChunkRanges_pairwise :
    topChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def pos3AChunks : Array SparseDyadicChunk := #[Pos3AData0.data]

def pos3AChunkRanges : Array (ℕ × ℕ) := #[(1, 122)]

theorem pos3AChunkRanges_pairwise :
    pos3AChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def pos3AlphaChunks : Array SparseDyadicChunk := #[Pos3AlphaData0.data, Pos3AlphaData1.data]

def pos3AlphaChunkRanges : Array (ℕ × ℕ) := #[(6, 437), (437, 732)]

theorem pos3AlphaChunkRanges_pairwise :
    pos3AlphaChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def edgeZero2Chunks : Array SparseDyadicChunk := #[EdgeZero2Data0.data, EdgeZero2Data1.data, EdgeZero2Data2.data]

def edgeZero2ChunkRanges : Array (ℕ × ℕ) := #[(60, 3228), (3229, 5447), (5447, 7314)]

theorem edgeZero2ChunkRanges_pairwise :
    edgeZero2ChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def zero3Chunks : Array SparseDyadicChunk := #[Zero3Data0.data]

def zero3ChunkRanges : Array (ℕ × ℕ) := #[(1, 266)]

theorem zero3ChunkRanges_pairwise :
    zero3ChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def zero4Chunks : Array SparseDyadicChunk := #[Zero4Data0.data, Zero4Data1.data, Zero4Data2.data, Zero4Data3.data, Zero4Data4.data, Zero4Data5.data, Zero4Data6.data, Zero4Data7.data, Zero4Data8.data, Zero4Data9.data, Zero4Data10.data, Zero4Data11.data, Zero4Data12.data, Zero4Data13.data]

def zero4ChunkRanges : Array (ℕ × ℕ) := #[(51, 55), (55, 56), (56, 57), (57, 59), (59, 73), (73, 76), (76, 78), (78, 79), (79, 80), (80, 81), (81, 82), (82, 84), (84, 87), (87, 91)]

theorem zero4ChunkRanges_pairwise :
    zero4ChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def muChunks : Array SparseScalarChunk := #[MuData0.data]

def muChunkRanges : Array (ℕ × ℕ) := #[(63, 7311)]

theorem muChunkRanges_pairwise :
    muChunkRanges.toList.Pairwise
      (fun earlier later => earlier.2 ≤ later.1) := by
  decide

def topNumeratorTotal : ℕ := TopData0.data.total + TopData1.data.total

theorem topNumeratorTotal_eq : topNumeratorTotal = 2 ^ 20 := by
  unfold topNumeratorTotal
  rw [TopData0.total_eq, TopData1.total_eq]
  decide

end MatrixMultiplication.Generated.TotalQuotientPrimary
