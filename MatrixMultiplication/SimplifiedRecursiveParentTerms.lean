/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-!
# Exact parent terms for the simplified recursive certificate

At level three, one ordered split numerator is multiplied by one depth-two complete-split row for
each labelled child.  Consequently the exact parent sample count is the literal ordered-split
subtotal times `2^24`; it need not be postulated to equal a global denominator.  This module
reconstructs the three complete-split parent rows and packages them as one exact interface term.
The reconstruction is parameterized by the quotient slot map, while the original public names
remain sorted-pair specializations.

The sole certificate-facing predicate below checks that each reconstructed leg row has that common
total.  Word support is proved from the explicit weight guard, so it is not a generated hypothesis.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedRecursiveParentTerms

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- Big-endian ternary code of one depth-two complete-split word. -/
def splitWordTwoCode (word : SplitWord 2) : ℕ :=
  (word ⟨0, by decide⟩ : ℕ) * 27 +
    (word ⟨1, by decide⟩ : ℕ) * 9 +
      (word ⟨2, by decide⟩ : ℕ) * 3 +
        (word ⟨3, by decide⟩ : ℕ)

/-- Product denominator of the two level-two child profile rows. -/
def levelThreeChildProductScale : ℕ := 2 ^ 24

/-- Exact sample count of the reconstructed level-three parent term. -/
def levelThreeParentSamples
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) : ℕ :=
  levelThreeSamples data node region * levelThreeChildProductScale

/-- Exact complete-split count of one oriented parent leg for a supplied quotient slot map.

The explicit support guard prevents `List.idxOf`'s fallback value from receiving off-weight mass.
All quotient dependence is routed through `supportSlot`; the shape and orientation conventions are
shared by every certificate family.
-/
def levelThreeParentWordCountFor (supportSlot : ℕ → ℕ → ℕ)
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 2) : ℕ :=
  let physical := coordinateOfLeg (sigma c)
  let total := (levelThreeParentIndex node sigma).count c
  if splitWordWeight word = total then
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.quotientBetaThreeRegionNumerator
      supportSlot data node.val region.val physical.val
        ((MatrixMultiplication.SimplifiedVolumeReconstruction.ternarySupportCodes 4 total).idxOf
          (splitWordTwoCode word))
  else 0

/-- Sorted-pair specialization of the oriented parent row used by the original certificate. -/
def levelThreeParentWordCount
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 2) : ℕ :=
  levelThreeParentWordCountFor
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.sortedPairSupportSlot
    data node region sigma c word

/-- A quotient-parametric reconstructed word can be nonzero only at the advertised weight. -/
theorem levelThreeParentWordCountFor_supported
    (supportSlot : ℕ → ℕ → ℕ)
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 2)
    (hcount : levelThreeParentWordCountFor supportSlot data node region sigma c word ≠ 0) :
    splitWordWeight word = (levelThreeParentIndex node sigma).count c := by
  by_contra hweight
  exact hcount (by simp [levelThreeParentWordCountFor, hweight])

/-- Every nonzero reconstructed word has the coordinate weight advertised by the parent index. -/
theorem levelThreeParentWordCount_supported
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (c : Leg) (word : SplitWord 2)
    (hcount : levelThreeParentWordCount data node region sigma c word ≠ 0) :
    splitWordWeight word = (levelThreeParentIndex node sigma).count c := by
  exact levelThreeParentWordCountFor_supported
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.sortedPairSupportSlot
    data node region sigma c word hcount

/-- Finite normalization condition for the three parent rows of a supplied quotient. -/
def LevelThreeParentRowsValidFor (supportSlot : ℕ → ℕ → ℕ)
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Prop :=
  ∀ c, ∑ word, levelThreeParentWordCountFor supportSlot data node region sigma c word =
    levelThreeParentSamples data node region

/-- Sorted-pair specialization of parent-row normalization. -/
def LevelThreeParentRowsValid
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) : Prop :=
  LevelThreeParentRowsValidFor
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.sortedPairSupportSlot
    data node region sigma

/-- Exact finite parent term reconstructed from valid rows of a supplied quotient. -/
noncomputable def levelThreeParentTermFor (supportSlot : ℕ → ℕ → ℕ)
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeParentRowsValidFor supportSlot data node region sigma) :
    ExactInterfaceTermParameters 2 :=
  ExactInterfaceTermParameters.ofCountRows
    (levelThreeParentIndex node sigma)
    (levelThreeParentWordCountFor supportSlot data node region sigma)
    hvalid
    (levelThreeParentWordCountFor_supported supportSlot data node region sigma)

/-- Sorted-pair specialization of the exact finite parent term. -/
noncomputable def levelThreeParentTerm
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeParentRowsValid data node region sigma) :
    ExactInterfaceTermParameters 2 :=
  levelThreeParentTermFor
    MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence.sortedPairSupportSlot
    data node region sigma hvalid

@[simp] theorem levelThreeParentTermFor_multiplicity
    (supportSlot : ℕ → ℕ → ℕ)
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeParentRowsValidFor supportSlot data node region sigma) :
    (levelThreeParentTermFor supportSlot data node region sigma hvalid).multiplicity =
      levelThreeParentSamples data node region :=
  rfl

@[simp] theorem levelThreeParentTerm_multiplicity
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeParentRowsValid data node region sigma) :
    (levelThreeParentTerm data node region sigma hvalid).multiplicity =
      levelThreeParentSamples data node region :=
  rfl

@[simp] theorem levelThreeParentTermFor_index
    (supportSlot : ℕ → ℕ → ℕ)
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeParentRowsValidFor supportSlot data node region sigma) :
    (levelThreeParentTermFor supportSlot data node region sigma hvalid).index =
      levelThreeParentIndex node sigma :=
  rfl

@[simp] theorem levelThreeParentTerm_index
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeParentRowsValid data node region sigma) :
    (levelThreeParentTerm data node region sigma hvalid).index =
      levelThreeParentIndex node sigma :=
  rfl

/-- Ordered left-child type at the exact multiplicity of the reconstructed parent term. -/
noncomputable def levelThreeParentSplitType
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation) :
    ExactRecursiveSplitType
      ((PositiveLevelThreeData.nodeShape node).orientedLeg sigma) 4
      (levelThreeParentSamples data node region) :=
  (levelThreeSplitType data node region sigma).scale levelThreeChildProductScale

end MatrixMultiplication.SimplifiedRecursiveParentTerms
