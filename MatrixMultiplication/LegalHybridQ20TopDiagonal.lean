/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry
import AlgebraicComplexity.MatrixMultiplication.LevelFourZeroLawGeometry
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryData

set_option autoImplicit false

/-!
# Diagonal positive support of the literal q20 top law

The regional division of [alman2025more], Claim `cl:dividing_into_region_zero_out`,
`papers/sources/2404.16349/constituent.tex:153-175`, assigns a regional multiplicity to each
retained constituent. The q20 candidate specializes its positive top law to the diagonal
root/incoming-region face, as required by `better_bound/legal_hybrid/check_directed.py:258-261`.
This module proves that finite support property from q20's own stored addresses, not from
another certificate, the 225-row schedule, a numerical checker result, or a free support array.

The address convention places the boundary atoms first, followed by positive atoms in
root-major, incoming-region-major, ordered-pair order. The offset is the public geometric
expression `regionCount * zeroFourShapeCount = 6 * 48`; the pair width is the public
`levelFourPairCount = 1785`. These are definitionally the reconstruction convention's
`topZeroAtomCount` and `topPairCount`. The local notation below introduces no new constants
into the public statements, and no predecessor manifest or lower probability table is imported.

Proof sketch: split each native address list into pieces of at most 50 natural numbers and
check each piece separately. Array/list concatenation identities
and the native `data_eq_rawData` theorems transport those twelve proofs to the exact stored
support. A supported atom above the boundary offset therefore has equal decoded root and
incoming region. No numerator array is reduced. The result does not discard boundary atoms,
construct a regional tensor restriction, identify a global reference, or prove a copy count.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- The q20 source image is this project's candidate with SHA-256
  `0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d`.
-/

namespace MatrixMultiplication.LegalHybridQ20TopDiagonal

open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData
open MatrixMultiplication.LevelFourRemainingReconstruction (zeroFourShapeCount)
open MatrixMultiplication.Generated.LegalHybridQ20Primary
open MatrixMultiplication.Generated.SimplifiedVolume

local notation "topZeroAtomCount" => regionCount * zeroFourShapeCount
local notation "topPairCount" => levelFourPairCount

/-- A sparse top atom is a boundary atom or has equal root and incoming-region labels. -/
def boundaryOrDiagonal (atom : ℕ) : Prop :=
  atom < topZeroAtomCount ∨
    (atom - topZeroAtomCount) / topPairCount / regionCount =
      ((atom - topZeroAtomCount) / topPairCount) % regionCount

/-- Decidability involves only arithmetic on one native address. -/
private instance (atom : ℕ) : Decidable (boundaryOrDiagonal atom) := by
  unfold boundaryOrDiagonal
  infer_instance

/-- Reassemble bounded list-prefix and suffix checks without re-evaluating their entries. -/
private theorem all_of_take_drop {atoms : List ℕ} (count : ℕ)
    (hleft : All boundaryOrDiagonal (atoms.take count))
    (hright : All boundaryOrDiagonal (atoms.drop count)) :
    All boundaryOrDiagonal atoms := by
  simpa only [List.take_append_drop] using ArrayCore.all_append hleft hright

/-- Diagonal-face check for the first 200 native addresses, in four bounded pieces. -/
private theorem native0_0 :
    All boundaryOrDiagonal TopData0.DataBlock0.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 0/1, with 200 addresses. -/
private theorem native0_1 :
    All boundaryOrDiagonal TopData0.DataBlock1.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 0/2, with 200 addresses. -/
private theorem native0_2 :
    All boundaryOrDiagonal TopData0.DataBlock2.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 0/3, with 200 addresses. -/
private theorem native0_3 :
    All boundaryOrDiagonal TopData0.DataBlock3.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 0/4, with 200 addresses. -/
private theorem native0_4 :
    All boundaryOrDiagonal TopData0.DataBlock4.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 0/5, with 200 addresses. -/
private theorem native0_5 :
    All boundaryOrDiagonal TopData0.DataBlock5.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 0/6, with 200 addresses. -/
private theorem native0_6 :
    All boundaryOrDiagonal TopData0.DataBlock6.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 0/7, with 200 addresses. -/
private theorem native0_7 :
    All boundaryOrDiagonal TopData0.DataBlock7.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 1/0, with 200 addresses. -/
private theorem native1_0 :
    All boundaryOrDiagonal TopData1.DataBlock0.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 1/1, with 200 addresses. -/
private theorem native1_1 :
    All boundaryOrDiagonal TopData1.DataBlock1.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for native block 1/2, with 200 addresses. -/
private theorem native1_2 :
    All boundaryOrDiagonal TopData1.DataBlock2.data.atomIndices.toList := by
  apply all_of_take_drop 50
  · decide
  · apply all_of_take_drop 50
    · decide
    · apply all_of_take_drop 50
      · decide
      · decide

/-- Diagonal-face check for the final 44 native addresses. -/
private theorem native1_3 :
    All boundaryOrDiagonal TopData1.DataBlock3.data.atomIndices.toList := by decide

/-- The first semantic chunk inherits its eight native support checks structurally. -/
private theorem top0_checked : All boundaryOrDiagonal TopData0.data.atomIndices.toList := by
  rw [TopData0.data_eq_rawData]
  simp only [TopData0.rawData, ArrayCore.appendMassChunk, ArrayCore.concatArrays_toList,
    List.append_assoc]
  exact ArrayCore.all_append native0_0 <|
    ArrayCore.all_append native0_1 <|
    ArrayCore.all_append native0_2 <|
    ArrayCore.all_append native0_3 <|
    ArrayCore.all_append native0_4 <|
    ArrayCore.all_append native0_5 <|
    ArrayCore.all_append native0_6 native0_7

/-- The second semantic chunk inherits its four native support checks structurally. -/
private theorem top1_checked : All boundaryOrDiagonal TopData1.data.atomIndices.toList := by
  rw [TopData1.data_eq_rawData]
  simp only [TopData1.rawData, ArrayCore.appendMassChunk, ArrayCore.concatArrays_toList,
    List.append_assoc]
  exact ArrayCore.all_append native1_0 <|
    ArrayCore.all_append native1_1 <|
    ArrayCore.all_append native1_2 native1_3

/-- Every atom in the exact q20 top support lies on the boundary or the diagonal regional face.

Proof sketch: concatenate the two semantic-chunk proofs. Each was obtained from its checked
native lists without evaluating the concatenated support or importing any lower-law data. -/
theorem topSupport_boundaryOrDiagonal : All boundaryOrDiagonal topSupportAtomIndices := by
  unfold topSupportAtomIndices
  exact ArrayCore.all_append top0_checked top1_checked

/-- Above the boundary offset, an actual q20 support atom has equal root and incoming region. -/
theorem topSupport_root_eq_region {atom : ℕ} (hmem : atom ∈ topSupportAtomIndices)
    (hpositive : topZeroAtomCount ≤ atom) :
    (atom - topZeroAtomCount) / topPairCount / regionCount =
      ((atom - topZeroAtomCount) / topPairCount) % regionCount := by
  have hface : boundaryOrDiagonal atom :=
    All.of_mem (predicate := boundaryOrDiagonal) (value := atom)
      topSupport_boundaryOrDiagonal hmem
  rcases hface with hboundary | hdiagonal
  · exact False.elim (Nat.not_lt_of_ge hpositive hboundary)
  · exact hdiagonal

end MatrixMultiplication.LegalHybridQ20TopDiagonal
