/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.LegalHybridQ20PrimaryData
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryLowerData

set_option autoImplicit false

/-!
# Primary tables for the canonical legal-hybrid q20 source image

This TW-28 source-image boundary replaces only the top law of the existing 90df source image.
Its other six fields point directly to the existing lower chunk leaves through a narrow
aggregate which imports neither the old top payload nor its packed zero4 presentation.
The generated top checks provide a globally ordered positive support, exactly 2,244 entries,
and exact `2^20` normalization. The
untrusted fail-closed exporter additionally checks that the ordered q20 support is byte-identical
to the 90df support before rendering it.

The top-law normalization represented here is the finite source image used in
`better_bound/paper.tex:2057-2075`.  Complete-split and recursive-constituent laws are described in
[alman2025more, `papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:41-47`].  This module does not import or replace the
existing `PairedTotalWeightA5SparseFactors`, and proves no semantic compatibility, entropy/log
bound, tensor restriction, survivor count, or endpoint.  In particular, the local seven-field
record keeps this source image independent of the old reconstruction packet; a downstream module
must explicitly translate it when the q20 semantic recurrence is ready.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.LegalHybridQ20PrimaryTables

open MatrixMultiplication.Generated.SimplifiedVolume

/-- The seven exact primary families stored by the isolated q20 source image. -/
structure PrimaryTables where
  top : Array SparseMassChunk
  pos3A : Array SparseDyadicChunk
  pos3Alpha : Array SparseDyadicChunk
  edgeZero2 : Array SparseDyadicChunk
  zero3 : Array SparseDyadicChunk
  zero4 : Array SparseDyadicChunk
  mu : Array SparseScalarChunk

/-- The canonical q20 top law paired with all six unchanged lower primary-table families. -/
def primaryTables : PrimaryTables :=
  { top := MatrixMultiplication.Generated.LegalHybridQ20Primary.topChunks
    pos3A := MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.pos3AChunks
    pos3Alpha := MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.pos3AlphaChunks
    edgeZero2 := MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.edgeZero2Chunks
    zero3 := MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.zero3Chunks
    zero4 := MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.zero4Chunks
    mu := MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.muChunks }

/-- All six non-top fields are definitionally the existing direct lower chunk families. -/
theorem lowerFields_eq_existing :
    primaryTables.pos3A =
        MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.pos3AChunks ∧
      primaryTables.pos3Alpha =
        MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.pos3AlphaChunks ∧
      primaryTables.edgeZero2 =
        MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.edgeZero2Chunks ∧
      primaryTables.zero3 =
        MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.zero3Chunks ∧
      primaryTables.zero4 =
        MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.zero4Chunks ∧
      primaryTables.mu =
        MatrixMultiplication.Generated.LegalHybridQ20Primary.Lower.muChunks := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Ordered sparse support of the q20 top law, with chunk boundaries forgotten. -/
def topSupportAtomIndices : List Nat :=
  MatrixMultiplication.Generated.LegalHybridQ20Primary.topSupportAtomIndices

/-- The q20 top law's ordered positive support is strictly increasing. -/
theorem topSupportAtomIndices_strictlyIncreasing :
    StrictlyIncreasing topSupportAtomIndices :=
  MatrixMultiplication.Generated.LegalHybridQ20Primary.topSupportAtomIndices_strictlyIncreasing

/-- The q20 top law's ordered positive support has exactly 2,244 entries. -/
theorem topSupportAtomIndices_length : topSupportAtomIndices.length = 2244 :=
  MatrixMultiplication.Generated.LegalHybridQ20Primary.topSupportAtomIndices_length

/-- The q20 top field contains exactly 2,244 positive coordinates. -/
theorem topValueCount_eq :
    MatrixMultiplication.Generated.LegalHybridQ20Primary.topValueCount = 2244 :=
  MatrixMultiplication.Generated.LegalHybridQ20Primary.topValueCount_eq

/-- The q20 top field is normalized at its native denominator. -/
theorem topNumeratorTotal_eq :
    MatrixMultiplication.Generated.LegalHybridQ20Primary.topNumeratorTotal = 2 ^ 20 :=
  MatrixMultiplication.Generated.LegalHybridQ20Primary.topNumeratorTotal_eq

end MatrixMultiplication.LegalHybridQ20PrimaryTables
