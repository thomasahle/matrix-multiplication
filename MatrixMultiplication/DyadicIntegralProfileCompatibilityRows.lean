/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.CompatibilityRateCore
import MatrixMultiplication.DyadicIntegralProfileEntropyCore

set_option autoImplicit false

/-!
# Integral-profile semantics of dyadic compatibility rows

This module constructs the evaluator rows attached to an arbitrary finite compatibility
requirement system and proves their exact division-free entropy rate.  It assumes no normalization,
positivity, recursion depth, tensor construction, or numerical certificate.
-/

open scoped BigOperators

namespace AlgebraicComplexity.CompatibleSplit

open AlgebraicComplexity.WordType
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.DyadicIntegralProfileEntropy
open MatrixMultiplication.SimplifiedExponentRootRecurrence

noncomputable section

universe u v w x

namespace SplitRequirements

variable {C : Type u} {L : Type v} {Z : Type w}
variable [Fintype C] [DecidableEq C]
variable [Fintype L] [DecidableEq L]
variable [Fintype Z] [DecidableEq Z]

/-- Canonical evaluator rows attached to a finite compatibility requirement system and its
parent complete-split profile.

The first family contains precisely the individually charged boundary cells.  The second family
contains every pooled positive cell, including zero rows.  The leading row is supplied separately
because it is the parent law, whereas `S.typicalType` records one labelled child occurrence;
homogeneous entropy makes retaining or dropping zero compatibility rows immaterial. -/
noncomputable def canonicalCompatibilityRows
    {P : Type x} [Fintype P] [DecidableEq P]
    (S : SplitRequirements C L Z) (parentProfile : P → ℕ) :
    CompatibilityRows where
  pooled := numeratorList parentProfile
  first := ((Finset.univ.filter fun c ↦ S.boundary c = true).toList.map fun c ↦
    numeratorList (S.splitCount c))
  groups := (Finset.univ.toList.map fun z ↦ numeratorList (S.pooledSplit z))

/-- The canonical boundary-row family has exactly the boundary contribution to the compatibility
conditional-entropy mass. -/
theorem sum_boundaryRows_eq
    {P : Type x} [Fintype P] [DecidableEq P]
    (S : SplitRequirements C L Z) (parentProfile : P → ℕ) (bits : ℕ) :
    (((S.canonicalCompatibilityRows parentProfile).first.map
      (weightedEntropyList bits)).sum) =
      (∑ c, if S.boundary c then
        ((profileMass (S.splitCount c) : ℝ) * profileEntropyNats (S.splitCount c)) /
          ((2 : ℝ) ^ bits * Real.log 2)
      else 0) := by
  classical
  unfold canonicalCompatibilityRows
  simp only [List.map_map, Function.comp_apply, weightedEntropyList_numeratorList,
    weightedEntropy_eq_profileEntropyMass_div, Finset.sum_map_toList]
  rw [Finset.sum_filter]

/-- The canonical pooled-row family has exactly the pooled contribution to the compatibility
conditional-entropy mass. -/
theorem sum_groupRows_eq
    {P : Type x} [Fintype P] [DecidableEq P]
    (S : SplitRequirements C L Z) (parentProfile : P → ℕ) (bits : ℕ) :
    (((S.canonicalCompatibilityRows parentProfile).groups.map
      (weightedEntropyList bits)).sum) =
      ∑ z, ((profileMass (S.pooledSplit z) : ℝ) *
        profileEntropyNats (S.pooledSplit z)) /
          ((2 : ℝ) ^ bits * Real.log 2) := by
  classical
  unfold canonicalCompatibilityRows
  simp only [List.map_map, Function.comp_apply, weightedEntropyList_numeratorList,
    weightedEntropy_eq_profileEntropyMass_div, Finset.sum_map_toList]

/-- The entropy sum subtracted by the canonical evaluator is the semantic compatible-row entropy
mass at the common dyadic/base-two scale. -/
theorem subtractedEntropy_eq_rowEntropyMass
    {P : Type x} [Fintype P] [DecidableEq P]
    (S : SplitRequirements C L Z) (parentProfile : P → ℕ) (bits : ℕ) :
    ((S.canonicalCompatibilityRows parentProfile).first.map
        (weightedEntropyList bits)).sum +
        ((S.canonicalCompatibilityRows parentProfile).groups.map
          (weightedEntropyList bits)).sum =
      rowEntropyMass S.compatibleType /
        ((2 : ℝ) ^ bits * Real.log 2) := by
  rw [S.sum_boundaryRows_eq parentProfile bits, S.sum_groupRows_eq parentProfile bits,
    S.rowEntropyMass_compatibleType, add_div, Finset.sum_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases hc : S.boundary c = true <;> simp [hc]

/-- Exact semantic interpretation of the canonical compatibility branch.

The bracketed correction is `H(parent) - H(split | visible)` at the represented dyadic scale,
equivalently `I(visible; split) + H(parent) - H(split)`.  It is kept in this division-free
conditional-entropy form so the theorem needs neither a positivity nor a normalization
hypothesis. -/
theorem canonicalCompatibilityRows_rate
    {P : Type x} [Fintype P] [DecidableEq P]
    (S : SplitRequirements C L Z) (parentProfile : P → ℕ) (bits : ℕ) :
    ((S.canonicalCompatibilityRows parentProfile).rate bits) =
      -(S.compatibilityLogLoss /
          ((2 : ℝ) ^ bits * Real.log 2)) +
        (weightedEntropy bits parentProfile -
          rowEntropyMass S.typicalType /
            ((2 : ℝ) ^ bits * Real.log 2)) := by
  rw [CompatibilityRows.rate, sub_sub, S.subtractedEntropy_eq_rowEntropyMass parentProfile bits,
    canonicalCompatibilityRows, weightedEntropyList_numeratorList]
  unfold compatibilityLogLoss
  ring

end SplitRequirements

end

end AlgebraicComplexity.CompatibleSplit
