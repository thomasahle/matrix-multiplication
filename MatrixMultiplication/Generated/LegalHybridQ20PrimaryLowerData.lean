/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.PairedTotalWeightPrimaryEdgeZero2Data0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryEdgeZero2Data1
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryEdgeZero2Data2
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryMuData0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryPos3AData0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryPos3AlphaData0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryPos3AlphaData1
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero3Data0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data1
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data2
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data3
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data4
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data5
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data6
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data7
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data8
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data9
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data10
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data11
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data12
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data13

set_option autoImplicit false

/-!
# Existing lower primary data for the legal-hybrid q20 source image

This narrow leaf exposes the six lower primary-table fields already generated from candidate
`90dfb5ea1f9560845093afcf88dc12d11af836d3b34983886f0e915729bbfb8d`.  The q20 exporter checks
that all six underlying numerator arrays are byte-identical in candidate
`0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d` before emitting the new top
law.  In particular, this module imports neither the old top-law aggregate nor the large packed
zero4 presentation; it points directly to the existing independently checked lower chunks.

These finite distributions are the complete-split data used by [alman2025more],
`papers/sources/2404.16349/prelim.tex:249-278`, and by the Total-Weight normalization in
`better_bound/paper.tex:2057-2075`.  This module introduces no new numerical payload or semantic
claim.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.Generated.PairedTotalWeightPrimary

/-- Existing positive level-three local-law chunks. -/
def pos3AChunks : Array SparseDyadicChunk := #[Pos3AData0.data]

/-- Existing level-three conditional-law chunks. -/
def pos3AlphaChunks : Array SparseDyadicChunk :=
  #[Pos3AlphaData0.data, Pos3AlphaData1.data]

/-- Existing level-two edge-law chunks. -/
def edgeZero2Chunks : Array SparseDyadicChunk :=
  #[EdgeZero2Data0.data, EdgeZero2Data1.data, EdgeZero2Data2.data]

/-- Existing level-three zero-law chunks. -/
def zero3Chunks : Array SparseDyadicChunk := #[Zero3Data0.data]

/-- Existing unpacked level-four zero-law chunks. -/
def zero4Chunks : Array SparseDyadicChunk :=
  #[Zero4Data0.data, Zero4Data1.data, Zero4Data2.data, Zero4Data3.data,
    Zero4Data4.data, Zero4Data5.data, Zero4Data6.data, Zero4Data7.data,
    Zero4Data8.data, Zero4Data9.data, Zero4Data10.data, Zero4Data11.data,
    Zero4Data12.data, Zero4Data13.data]

/-- Existing level-two scalar-law chunks. -/
def muChunks : Array SparseScalarChunk := #[MuData0.data]

end MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower
