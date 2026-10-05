/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibilityContainment

/-!
# Coarse containment forced by raw complete-split compatibility

The paper defines a fine block to be compatible with a coarse constituent only when the fine
block lies inside that constituent's corresponding coarse leg.  In the partition-friendly
formulation, compatibility is expressed by empirical complete-split profiles on compatibility
cells.  The containment clause is then a theorem, but only after proving the structural support
invariant of the prescribed target tables.

This file proves that theorem for the raw complete-split model.  A compatible logical-`Y` label
has, sample by sample, the logical-`Y` coarse coordinate of the constituent; likewise for `Z`.
The result is the raw counterpart of
`FeatureCompatibilityModel.symbolWeight_eq_coarseY_of_featureCompatibleY` and is the bridge that
licenses the shared-leg affine collision lemma.
-/

namespace AlgebraicComplexity

open Tensor

namespace MoreAsymmetryCompatibility.CompatibilityModel

universe u v

variable {A : Leg → Type v} {Part : Type u} [DecidableEq Part]
variable {depth samples : ℕ}

/-- A raw complete-split `Y` label compatible with an address has the address's coarse `Y`
coordinate at every sample. -/
theorem splitWordWeight_eq_coarseY_of_compatibleY
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (label : A .Y) (address : BlockAddress A)
    (hcompatible : model.CompatibleY targets label address)
    (sample : Fin samples) :
    splitWordWeight (model.chunks .Y label sample) =
      (model.coarse address sample).y := by
  let cell := yCompatibilityCell (model.coarse address sample)
  let word := model.chunks .Y label sample
  have hpositive : 0 < cellMultiplicity
      (fun position ↦ yCompatibilityCell (model.coarse address position))
      (model.chunks .Y label) cell word :=
    cellMultiplicity_pos_of_apply_eq _ _ sample cell word rfl rfl
  have htargetPositive : 0 < targets.yCellProfile cell word := by
    rw [← hcompatible cell word]
    exact hpositive
  exact (targets.yCellProfile_weight_eq hsupported cell word htargetPositive).trans
    (YCompatibilityCell.yValue_yCompatibilityCell _)

/-- A raw complete-split `Z` label compatible with an address has the address's coarse `Z`
coordinate at every sample. -/
theorem splitWordWeight_eq_coarseZ_of_compatibleZ
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (label : A .Z) (address : BlockAddress A)
    (hcompatible : model.CompatibleZ targets label address)
    (sample : Fin samples) :
    splitWordWeight (model.chunks .Z label sample) =
      (model.coarse address sample).z := by
  let cell := zCompatibilityCell (model.coarse address sample)
  let word := model.chunks .Z label sample
  have hpositive : 0 < cellMultiplicity
      (fun position ↦ zCompatibilityCell (model.coarse address position))
      (model.chunks .Z label) cell word :=
    cellMultiplicity_pos_of_apply_eq _ _ sample cell word rfl rfl
  have htargetPositive : 0 < targets.zCellProfile cell word := by
    rw [← hcompatible cell word]
    exact hpositive
  exact (targets.zCellProfile_weight_eq hsupported cell word htargetPositive).trans
    (ZCompatibilityCell.zValue_zCompatibilityCell _)

end MoreAsymmetryCompatibility.CompatibilityModel

end AlgebraicComplexity
