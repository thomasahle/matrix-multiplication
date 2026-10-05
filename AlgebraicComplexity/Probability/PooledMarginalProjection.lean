/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.MarginalProjection
import AlgebraicComplexity.Probability.PooledMarginalProjectionCore
import AlgebraicComplexity.Probability.SupportRestriction
import Mathlib.Tactic.Linarith

/-!
# Information projections with a pooled occurrence marginal

Recursive tensor constituents prescribe the total number of occurrences of each child symbol,
but do not in general prescribe separate left- and right-child marginals.  The affine constraint
is therefore

`Q_left(a) + Q_right(a) = P_left(a) + P_right(a)`

for every feature value `a`.  This module proves the corresponding finite information-projection
theorem.  If the reference log-density is a coarse potential plus one common potential evaluated
at the left and right occurrence features, then its expectation is constant on that pooled
affine fiber.  Consequently every feasible law satisfies

`H(Q | coarse) + D(Q_parent || P_parent) ≤ H(P | coarse)`.

Both positive and sparse reference laws are supported.  The sparse theorem deletes common
structural zeroes exactly, without padding or renormalization.  Its quadratic corollary contains
only rational operations on the two probability laws and is intended for method-of-types and
certificate applications.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u₁ u₂ u₃ u₄

namespace ProbabilityVector

variable {S : Type u₁} {A : Type u₂}
variable [Fintype S] [Fintype A] [DecidableEq A]

/-- Equality of a pooled pair of pushforward marginals preserves the sum of expectations of
every statistic on the common target alphabet. -/
theorem expectation_comp_add_eq_of_pushforward_weight_add_eq
    (left right : S → A) (p q : ProbabilityVector S)
    (hpool : ∀ a,
      (p.pushforward left).weight a + (p.pushforward right).weight a =
        (q.pushforward left).weight a + (q.pushforward right).weight a)
    (potential : A → ℝ) :
    p.expectation (potential ∘ left) + p.expectation (potential ∘ right) =
      q.expectation (potential ∘ left) + q.expectation (potential ∘ right) := by
  rw [← pushforward_expectation left p potential,
    ← pushforward_expectation right p potential,
    ← pushforward_expectation left q potential,
    ← pushforward_expectation right q potential]
  unfold expectation
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← add_mul, ← add_mul, hpool a]

end ProbabilityVector

namespace PooledMarginalProjectionModel

variable
    {S : Type u₁} {U : Type u₂} {A : Type u₃}
    [Fintype S] [Fintype U] [Fintype A]
    [DecidableEq U] [DecidableEq A]

/-- The reference log-density has invariant expectation on the pooled affine fiber. -/
theorem expectation_log_reference_eq
    (M : PooledMarginalProjectionModel S U A)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.expectation (fun s ↦ Real.log (M.reference.weight s)) =
      M.reference.expectation (fun s ↦ Real.log (M.reference.weight s)) := by
  rcases hq with ⟨hcoarse, hpool⟩
  let c : S → ℝ := M.coarsePotential ∘ M.coarse
  let l : S → ℝ := M.featurePotential ∘ M.leftFeature
  let r : S → ℝ := M.featurePotential ∘ M.rightFeature
  have hfeatures : q.expectation l + q.expectation r =
      M.reference.expectation l + M.reference.expectation r := by
    exact ProbabilityVector.expectation_comp_add_eq_of_pushforward_weight_add_eq
      M.leftFeature M.rightFeature q M.reference hpool M.featurePotential
  calc
    q.expectation (fun s ↦ Real.log (M.reference.weight s)) =
        q.expectation (fun s ↦ c s + (l s + r s)) :=
      q.expectation_congr M.log_reference_weight
    _ = q.expectation c + (q.expectation l + q.expectation r) := by
      rw [ProbabilityVector.expectation_add, ProbabilityVector.expectation_add]
    _ = M.reference.expectation c +
        (M.reference.expectation l + M.reference.expectation r) := by
      rw [ProbabilityVector.expectation_comp_eq_of_pushforward_eq
        M.coarse q M.reference hcoarse M.coarsePotential, hfeatures]
    _ = M.reference.expectation (fun s ↦ c s + (l s + r s)) := by
      rw [ProbabilityVector.expectation_add, ProbabilityVector.expectation_add]
    _ = M.reference.expectation (fun s ↦ Real.log (M.reference.weight s)) :=
      M.reference.expectation_congr (fun s ↦ (M.log_reference_weight s).symm)

/-- Pooled parent-consistency inequality in nats for an arbitrary surjective parent statistic. -/
theorem conditionalEntropy_add_parentKl_le
    {P : Type u₄} [Fintype P] [DecidableEq P]
    (M : PooledMarginalProjectionModel S U A)
    (parent : S → P) (hparent : Function.Surjective parent)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropy M.coarse +
        (q.pushforward parent).klDiv (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropy M.coarse := by
  have hlog := expectation_log_reference_eq M q hq
  have hkl : q.klDiv M.reference = M.reference.entropy - q.entropy :=
    ProbabilityVector.klDiv_eq_entropy_sub_of_expectation_log_eq
      q M.reference M.reference_pos hlog
  have hdata := ProbabilityVector.klDiv_pushforward_le
    parent q M.reference M.reference_pos hparent
  have hcoarseEntropy :
      (q.pushforward M.coarse).entropy =
        (M.reference.pushforward M.coarse).entropy :=
    congrArg ProbabilityVector.entropy hq.1
  unfold ProbabilityVector.conditionalEntropy
  rw [hcoarseEntropy]
  linarith

/-- Pooled parent-consistency inequality in bits. -/
theorem conditionalEntropyBits_add_parentKlBits_le
    {P : Type u₄} [Fintype P] [DecidableEq P]
    (M : PooledMarginalProjectionModel S U A)
    (parent : S → P) (hparent : Function.Surjective parent)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).klDivBits (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropyBits M.coarse := by
  unfold ProbabilityVector.conditionalEntropyBits ProbabilityVector.klDivBits
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (conditionalEntropy_add_parentKl_le M parent hparent q hq)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Fully rational-in-the-laws pooled correction. -/
theorem conditionalEntropyBits_add_parentQuadratic_le
    {P : Type u₄} [Fintype P] [DecidableEq P]
    (M : PooledMarginalProjectionModel S U A)
    (parent : S → P) (hparent : Function.Surjective parent)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).quadraticKlLowerBits
          (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropyBits M.coarse := by
  have hreferenceParent : ∀ z, 0 < (M.reference.pushforward parent).weight z :=
    ProbabilityVector.pushforward_weight_pos_of_surjective
      parent M.reference M.reference_pos hparent
  have hquadratic := ProbabilityVector.quadraticKlLowerBits_le_klDivBits
    (q.pushforward parent) (M.reference.pushforward parent) hreferenceParent
  have hkl := conditionalEntropyBits_add_parentKlBits_le M parent hparent q hq
  linarith

end PooledMarginalProjectionModel

/-! ## Sparse reference laws -/

namespace SparsePooledMarginalProjectionModel

variable
    {S : Type u₁} {U : Type u₂} {A : Type u₃}
    [Fintype S] [Fintype U] [Fintype A]
    [DecidableEq U] [DecidableEq A]

/-- Delete the structural zeroes to obtain the exact positive pooled model. -/
noncomputable def onPositiveSupport
    (M : SparsePooledMarginalProjectionModel S U A) :
    PooledMarginalProjectionModel M.reference.PositiveSupport U A where
  reference := M.reference.positiveSupportRestriction
  coarse := M.coarse ∘ Subtype.val
  leftFeature := M.leftFeature ∘ Subtype.val
  rightFeature := M.rightFeature ∘ Subtype.val
  coarsePotential := M.coarsePotential
  featurePotential := M.featurePotential
  reference_pos := M.reference.positiveSupportRestriction_pos
  log_reference_weight s := M.log_reference_weight s.1 s.2

/-- Restricting a sparse feasible law preserves the pooled affine constraints. -/
theorem restrict_isFeasible
    (M : SparsePooledMarginalProjectionModel S U A)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    M.onPositiveSupport.IsFeasible
      (q.restrictToPositiveSupport M.reference hq.1) := by
  rcases hq with ⟨hac, hcoarse, hpool⟩
  constructor
  · change
      (q.restrictToPositiveSupport M.reference hac).pushforward
          (M.coarse ∘ Subtype.val) =
        M.reference.positiveSupportRestriction.pushforward
          (M.coarse ∘ Subtype.val)
    rw [ProbabilityVector.restrictToPositiveSupport_pushforward
      q M.reference hac M.coarse]
    rw [ProbabilityVector.positiveSupportRestriction_pushforward
      M.reference M.coarse]
    exact hcoarse
  · intro a
    change
      ((q.restrictToPositiveSupport M.reference hac).pushforward
          (M.leftFeature ∘ Subtype.val)).weight a +
        ((q.restrictToPositiveSupport M.reference hac).pushforward
          (M.rightFeature ∘ Subtype.val)).weight a =
      (M.reference.positiveSupportRestriction.pushforward
          (M.leftFeature ∘ Subtype.val)).weight a +
        (M.reference.positiveSupportRestriction.pushforward
          (M.rightFeature ∘ Subtype.val)).weight a
    rw [ProbabilityVector.restrictToPositiveSupport_pushforward
        q M.reference hac M.leftFeature,
      ProbabilityVector.restrictToPositiveSupport_pushforward
        q M.reference hac M.rightFeature,
      ProbabilityVector.positiveSupportRestriction_pushforward
        M.reference M.leftFeature,
      ProbabilityVector.positiveSupportRestriction_pushforward
        M.reference M.rightFeature]
    exact hpool a

/-- Sparse pooled parent-consistency correction in nats. -/
theorem conditionalEntropy_add_parentKl_le
    {P : Type u₄} [Fintype P] [DecidableEq P]
    (M : SparsePooledMarginalProjectionModel S U A)
    (parent : S → P) (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropy M.coarse +
        (q.pushforward parent).klDiv (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropy M.coarse := by
  let qSupport := q.restrictToPositiveSupport M.reference hq.1
  have hsFeasible : M.onPositiveSupport.IsFeasible qSupport :=
    M.restrict_isFeasible q hq
  have hcore := M.onPositiveSupport.conditionalEntropy_add_parentKl_le
    (M.reference.positiveSupportMap parent)
    (M.reference.positiveSupportMap_surjective parent)
    qSupport hsFeasible
  have hqPush := ProbabilityVector.restrictToPositiveSupport_pushforward_positiveSupportMap
    q M.reference hq.1 parent
  have hrefPush :=
    ProbabilityVector.positiveSupportRestriction_pushforward_positiveSupportMap
      M.reference parent
  have hparentAC := hq.1.pushforward parent
  change
    qSupport.conditionalEntropy (M.coarse ∘ Subtype.val) +
        (qSupport.pushforward (M.reference.positiveSupportMap parent)).klDiv
          (M.reference.positiveSupportRestriction.pushforward
            (M.reference.positiveSupportMap parent)) ≤
      M.reference.positiveSupportRestriction.conditionalEntropy
        (M.coarse ∘ Subtype.val) at hcore
  rw [hqPush, hrefPush,
    ProbabilityVector.restrictToPositiveSupport_klDiv
      (q.pushforward parent) (M.reference.pushforward parent) hparentAC,
    ProbabilityVector.restrictToPositiveSupport_conditionalEntropy
      q M.reference hq.1 M.coarse,
    ProbabilityVector.positiveSupportRestriction_conditionalEntropy
      M.reference M.coarse] at hcore
  exact hcore

/-- Sparse pooled parent-consistency correction in bits. -/
theorem conditionalEntropyBits_add_parentKlBits_le
    {P : Type u₄} [Fintype P] [DecidableEq P]
    (M : SparsePooledMarginalProjectionModel S U A)
    (parent : S → P) (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).klDivBits (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropyBits M.coarse := by
  unfold ProbabilityVector.conditionalEntropyBits ProbabilityVector.klDivBits
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (conditionalEntropy_add_parentKl_le M parent q hq)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Sparse pooled rational correction used by exact type-counting clients. -/
theorem conditionalEntropyBits_add_parentQuadratic_le
    {P : Type u₄} [Fintype P] [DecidableEq P]
    (M : SparsePooledMarginalProjectionModel S U A)
    (parent : S → P) (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).quadraticKlLowerBits
          (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropyBits M.coarse := by
  have hquadratic :=
    ProbabilityVector.quadraticKlLowerBits_le_klDivBits_of_absoluteContinuity
      (q.pushforward parent) (M.reference.pushforward parent) (hq.1.pushforward parent)
  have hkl := conditionalEntropyBits_add_parentKlBits_le M parent q hq
  linarith

end SparsePooledMarginalProjectionModel

end AlgebraicComplexity
