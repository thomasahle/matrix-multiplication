/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.IdentityOrientationCompatibilityCounting
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityTransport

/-!
# Orientation transport for loss-free compatibility counts

The certificate uses one repeated `XZY` orientation.  These results are stated for an arbitrary
orientation because the transport is definitional after passing to `logicalAddress`; no new
counting argument or enumeration of the six permutations is introduced.
-/

open scoped BigOperators

namespace AlgebraicComplexity.MoreAsymmetryCompatibility.CompatibilityModel

open Tensor

universe u v

variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {Part : Type u} [DecidableEq Part]
variable {depth samples : ℕ}

/-- Loss-free compatible-label count on the physical `sigma Y` leg of an oriented region. -/
theorem card_orientedCompatibleLabelsY_le_prod_multinomial
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A (sigma .Y))) (address : BlockAddress A)
    (hlegal : (fun pair : ObservedCell
        (model.yCellWord (logicalAddress sigma address)) × SplitWord depth ↦
          targets.yCellProfile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell
        (model.yCellWord (logicalAddress sigma address)) × SplitWord depth) samples)
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell
            (model.yCellWord (logicalAddress sigma address)) × SplitWord depth ↦
          targets.yCellProfile pair.1.1 pair.2) =
      WordType.multiplicity
        (observedCellWord (model.yCellWord (logicalAddress sigma address))))
    (hinjective : Set.InjOn (model.chunks .Y) labels) :
    (Tensor.compatibleLabels labels (OrientedCompatibleY sigma model targets) address).card ≤
      ∏ cell : ObservedCell (model.yCellWord (logicalAddress sigma address)),
        Nat.multinomial Finset.univ (targets.yCellProfile cell.1) := by
  have hsame :
      Tensor.compatibleLabels labels (OrientedCompatibleY sigma model targets) address =
        Tensor.compatibleLabels (A := OrientedLabelFamily sigma A) labels
          (model.CompatibleY targets)
          (logicalAddress sigma address) := by
    ext label
    simp [OrientedCompatibleY]
  rw [hsame]
  exact model.card_compatibleLabelsY_le_prod_multinomial targets labels
    (logicalAddress sigma address) hlegal hfst hinjective

/-- Orientation-parametric `Y` count in the form used after compatibility soundness: the fixed
address's own physical `sigma Y` label supplies legality and the first marginal. -/
theorem card_orientedCompatibleLabelsY_le_prod_multinomial_of_self
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A (sigma .Y))) (address : BlockAddress A)
    (hinjective : Set.InjOn (model.chunks .Y) labels)
    (hself_mem : address (sigma .Y) ∈ labels)
    (hself : OrientedCompatibleY sigma model targets (address (sigma .Y)) address) :
    (Tensor.compatibleLabels labels (OrientedCompatibleY sigma model targets) address).card ≤
      ∏ cell : ObservedCell (model.yCellWord (logicalAddress sigma address)),
        Nat.multinomial Finset.univ (targets.yCellProfile cell.1) := by
  have hsame :
      Tensor.compatibleLabels labels (OrientedCompatibleY sigma model targets) address =
        Tensor.compatibleLabels (A := OrientedLabelFamily sigma A) labels
          (model.CompatibleY targets) (logicalAddress sigma address) := by
    ext label
    simp [OrientedCompatibleY]
  rw [hsame]
  exact model.card_compatibleLabelsY_le_prod_multinomial_of_self targets labels
    (logicalAddress sigma address) hinjective
      (by simpa using hself_mem) (by simpa [OrientedCompatibleY] using hself)

/-- Loss-free oriented `Y` count directly from the invariants enforced by the first zero-out. -/
theorem card_orientedCompatibleLabelsY_le_prod_multinomial_of_passes
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A (sigma .Y))) (address : BlockAddress A)
    (hinjective : Set.InjOn (model.chunks .Y) labels)
    (hself_mem : address (sigma .Y) ∈ labels)
    (hpasses : model.PassesYFirstZeroOut targets (logicalAddress sigma address)) :
    (Tensor.compatibleLabels labels (OrientedCompatibleY sigma model targets) address).card ≤
      ∏ cell : ObservedCell (model.yCellWord (logicalAddress sigma address)),
        Nat.multinomial Finset.univ (targets.yCellProfile cell.1) :=
  model.card_orientedCompatibleLabelsY_le_prod_multinomial_of_self sigma targets labels
    address hinjective hself_mem
      (model.orientedCompatibleY_of_passesYFirstZeroOut sigma targets address hpasses)

/-- Loss-free compatible-label count on the physical `sigma Z` leg of an oriented region. -/
theorem card_orientedCompatibleLabelsZ_le_prod_multinomial
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A (sigma .Z))) (address : BlockAddress A)
    (hlegal : (fun pair : ObservedCell
        (model.zCellWord (logicalAddress sigma address)) × SplitWord depth ↦
          targets.zCellProfile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell
        (model.zCellWord (logicalAddress sigma address)) × SplitWord depth) samples)
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell
            (model.zCellWord (logicalAddress sigma address)) × SplitWord depth ↦
          targets.zCellProfile pair.1.1 pair.2) =
      WordType.multiplicity
        (observedCellWord (model.zCellWord (logicalAddress sigma address))))
    (hinjective : Set.InjOn (model.chunks .Z) labels) :
    (Tensor.compatibleLabels labels (OrientedCompatibleZ sigma model targets) address).card ≤
      ∏ cell : ObservedCell (model.zCellWord (logicalAddress sigma address)),
        Nat.multinomial Finset.univ (targets.zCellProfile cell.1) := by
  have hsame :
      Tensor.compatibleLabels labels (OrientedCompatibleZ sigma model targets) address =
        Tensor.compatibleLabels (A := OrientedLabelFamily sigma A) labels
          (model.CompatibleZ targets)
          (logicalAddress sigma address) := by
    ext label
    simp [OrientedCompatibleZ]
  rw [hsame]
  exact model.card_compatibleLabelsZ_le_prod_multinomial targets labels
    (logicalAddress sigma address) hlegal hfst hinjective

/-- Orientation-parametric `Z` count in the form used after compatibility soundness: the fixed
address's own physical `sigma Z` label supplies legality and the first marginal. -/
theorem card_orientedCompatibleLabelsZ_le_prod_multinomial_of_self
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A (sigma .Z))) (address : BlockAddress A)
    (hinjective : Set.InjOn (model.chunks .Z) labels)
    (hself_mem : address (sigma .Z) ∈ labels)
    (hself : OrientedCompatibleZ sigma model targets (address (sigma .Z)) address) :
    (Tensor.compatibleLabels labels (OrientedCompatibleZ sigma model targets) address).card ≤
      ∏ cell : ObservedCell (model.zCellWord (logicalAddress sigma address)),
        Nat.multinomial Finset.univ (targets.zCellProfile cell.1) := by
  have hsame :
      Tensor.compatibleLabels labels (OrientedCompatibleZ sigma model targets) address =
        Tensor.compatibleLabels (A := OrientedLabelFamily sigma A) labels
          (model.CompatibleZ targets) (logicalAddress sigma address) := by
    ext label
    simp [OrientedCompatibleZ]
  rw [hsame]
  exact model.card_compatibleLabelsZ_le_prod_multinomial_of_self targets labels
    (logicalAddress sigma address) hinjective
      (by simpa using hself_mem) (by simpa [OrientedCompatibleZ] using hself)

/-- Loss-free oriented `Z` count directly from the invariants enforced by the first zero-out. -/
theorem card_orientedCompatibleLabelsZ_le_prod_multinomial_of_passes
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A (sigma .Z))) (address : BlockAddress A)
    (hinjective : Set.InjOn (model.chunks .Z) labels)
    (hself_mem : address (sigma .Z) ∈ labels)
    (hpasses : model.PassesZFirstZeroOut targets (logicalAddress sigma address)) :
    (Tensor.compatibleLabels labels (OrientedCompatibleZ sigma model targets) address).card ≤
      ∏ cell : ObservedCell (model.zCellWord (logicalAddress sigma address)),
        Nat.multinomial Finset.univ (targets.zCellProfile cell.1) :=
  model.card_orientedCompatibleLabelsZ_le_prod_multinomial_of_self sigma targets labels
    address hinjective hself_mem
      (model.orientedCompatibleZ_of_passesZFirstZeroOut sigma targets address hpasses)

end AlgebraicComplexity.MoreAsymmetryCompatibility.CompatibilityModel
