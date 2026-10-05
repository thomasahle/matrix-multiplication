/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetFiber
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightQuotientCompatibility
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibilityPushforward

set_option autoImplicit false

/-!
# Total-weight features on doubled recursive CW occurrences

Recursive Coppersmith--Winograd compatibility sees the two labelled children of each parent
occurrence.  Its raw symbols are complete-split words, whereas affine hashing records only their
total weights.  This module proves the exact finite bridge between those two views.

The feature model is defined directly on the complete doubled recursive quotient address.  Raw
logical-`Z` compatibility pushes forward to feature compatibility because cell multiplicities
commute with the noninjective total-weight map.  For a supported target profile, feature
compatibility then forces equality of the entire doubled `Z` word.  No hashing, tensor
restriction, competitor bound, asymptotic estimate, or certificate datum is used.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- Total-weight feature model on all left and right child occurrences of one recursive parent
word.  The address is stored in physical coordinates and read in logical coordinates through
`sigma`. -/
def cwRecursiveTotalWeightFeatureCompatibilityModel
    {Part : Type u} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation) :
    FeatureCompatibilityModel
      (fun _c ↦ Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth)
      Part (CWRecursiveChildDigit depth) ((n + 1) + (n + 1)) where
  symbols _c word := word
  coarse := cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma

@[simp] theorem cwRecursiveTotalWeightFeatureCompatibilityModel_symbols
    {Part : Type u} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (c : Leg) (word : Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth) :
    (cwRecursiveTotalWeightFeatureCompatibilityModel
      depth n partAt sigma).symbols c word = word :=
  rfl

@[simp] theorem cwRecursiveTotalWeightFeatureCompatibilityModel_coarse
    {Part : Type u} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : CWRecursiveCoarseAddress depth n) :
    (cwRecursiveTotalWeightFeatureCompatibilityModel
      depth n partAt sigma).coarse address =
        cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma address :=
  rfl

/-- Taking total weight pointwise in a raw labelled-child split word gives exactly the recursive
hash quotient word. -/
theorem cwSplitWordTotalDigit_comp_recursiveChildChunks
    {Part : Type u} (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (logicalLeg : Leg)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwSplitWordTotalDigit depth ∘
        (cwRecursiveChildCompatibilityModel depth n partAt).chunks logicalLeg word =
      cwRecursiveLabelledChildWord depth n word := by
  funext occurrence
  apply Fin.ext
  simpa only [Function.comp_apply, cwSplitWordTotalDigit_val,
    cwRecursiveChildCompatibilityModel_chunks] using
      (val_cwRecursiveLabelledChildWord_eq_splitWordWeight
        depth n word occurrence).symm

/-- The pushed total-weight target table in one `Z` cell is literally the finite pushforward of
the raw complete-split table in that cell. -/
theorem cwTotalWeightPushforwardTargets_zCellProfile
    {Part : Type u} {depth : ℕ}
    (rawTargets : CompatibilityTargets Part depth)
    (cell : ZCompatibilityCell Part) :
    (cwTotalWeightPushforwardTargets rawTargets).zCellProfile cell =
      WordType.mappedType (cwSplitWordTotalDigit depth)
        (rawTargets.zCellProfile cell) := by
  cases cell <;> rfl

/-- Raw recursive logical-`Z` compatibility descends exactly to total-weight feature
compatibility on the two recursive hash groups. -/
theorem cwRecursive_orientedCompatibleZ_to_totalWeightFeatureCompatibleZ
    {Part : Type u} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (rawTargets : CompatibilityTargets Part depth)
    (target other : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hcompatible : OrientedCompatibleZ sigma
      (cwRecursiveChildCompatibilityModel depth n partAt) rawTargets
      (target (sigma .Z)) other) :
    (cwRecursiveTotalWeightFeatureCompatibilityModel
      depth n partAt sigma).FeatureCompatibleZ
        (cwTotalWeightPushforwardTargets rawTargets)
        (cwRecursiveChildGroup depth n target (sigma .Z))
        (cwRecursiveChildGroup depth n other) := by
  let rawModel := cwRecursiveChildCompatibilityModel depth n partAt
  let featureModel := cwRecursiveTotalWeightFeatureCompatibilityModel
    depth n partAt sigma
  have hraw : rawModel.CompatibleZ rawTargets
      (target (sigma .Z)) (logicalAddress sigma other) := by
    simpa only [OrientedCompatibleZ] using hcompatible
  have hcells :
      (fun occurrence ↦ zCompatibilityCell
        (featureModel.coarse (cwRecursiveChildGroup depth n other) occurrence)) =
      (fun occurrence ↦ zCompatibilityCell
        (rawModel.coarse (logicalAddress sigma other) occurrence)) := by
    rw [show featureModel.coarse (cwRecursiveChildGroup depth n other) =
        cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma
          (cwRecursiveChildGroup depth n other) by rfl,
      cwRecursiveChildCompatibilityModel_coarse_eq_orientedSequence]
  have hsymbols :
      featureModel.symbols .Z
          (cwRecursiveChildGroup depth n target (sigma .Z)) =
        cwSplitWordTotalDigit depth ∘
          rawModel.chunks .Z (target (sigma .Z)) := by
    exact (cwSplitWordTotalDigit_comp_recursiveChildChunks
      depth n partAt .Z (target (sigma .Z))).symm
  intro cell symbol
  change CWCoarseDigit depth at symbol
  have hrawProfile :
      (fun word ↦ cellMultiplicity
        (fun occurrence ↦ zCompatibilityCell
          (rawModel.coarse (logicalAddress sigma other) occurrence))
        (rawModel.chunks .Z (target (sigma .Z))) cell word) =
      rawTargets.zCellProfile cell := by
    funext word
    exact hraw cell word
  have hpush :=
    MoreAsymmetryCompatibility.cellMultiplicity_comp_eq_mappedType
      (fun occurrence ↦ zCompatibilityCell
        (rawModel.coarse (logicalAddress sigma other) occurrence))
      (rawModel.chunks .Z (target (sigma .Z)))
      (cwSplitWordTotalDigit depth) cell
  calc
    cellMultiplicity
        (fun occurrence ↦ zCompatibilityCell
          (featureModel.coarse (cwRecursiveChildGroup depth n other) occurrence))
        (featureModel.symbols .Z
          (cwRecursiveChildGroup depth n target (sigma .Z))) cell symbol =
      cellMultiplicity
        (fun occurrence ↦ zCompatibilityCell
          (rawModel.coarse (logicalAddress sigma other) occurrence))
        (cwSplitWordTotalDigit depth ∘
          rawModel.chunks .Z (target (sigma .Z))) cell symbol := by
      rw [hcells, hsymbols]
      rfl
    _ = WordType.mappedType (cwSplitWordTotalDigit depth)
        (cellMultiplicity
          (fun occurrence ↦ zCompatibilityCell
            (rawModel.coarse (logicalAddress sigma other) occurrence))
          (rawModel.chunks .Z (target (sigma .Z))) cell) symbol :=
      congrFun hpush symbol
    _ = WordType.mappedType (cwSplitWordTotalDigit depth)
        (rawTargets.zCellProfile cell) symbol := by
      exact congrArg
        (fun profile ↦ WordType.mappedType
          (cwSplitWordTotalDigit depth) profile symbol) hrawProfile
    _ = (cwTotalWeightPushforwardTargets rawTargets).zCellProfile cell symbol :=
      congrFun
        (cwTotalWeightPushforwardTargets_zCellProfile rawTargets cell).symm symbol

/-- For supported raw targets, a total-weight-compatible logical-`Z` label is the tested
address's complete logical-`Z` quotient word. -/
theorem cwRecursiveTotalWeight_label_eq_Z_of_featureCompatibleZ
    {Part : Type u} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    (label : Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth)
    (address : CWRecursiveCoarseAddress depth n)
    (hcompatible :
      (cwRecursiveTotalWeightFeatureCompatibilityModel
        depth n partAt sigma).FeatureCompatibleZ
          (cwTotalWeightPushforwardTargets rawTargets) label address) :
    label = address (sigma .Z) := by
  funext occurrence
  apply Fin.ext
  exact FeatureCompatibilityModel.symbolWeight_eq_coarseZ_of_featureCompatibleZ
    (cwRecursiveTotalWeightFeatureCompatibilityModel depth n partAt sigma)
    (cwTotalWeightPushforwardTargets rawTargets) Fin.val
    (cwTotalWeightPushforwardTargets_isZWeightSupported rawTargets hsupported)
    label address hcompatible occurrence

end AlgebraicComplexity.Examples
