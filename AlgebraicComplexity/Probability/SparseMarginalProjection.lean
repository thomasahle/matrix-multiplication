/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.MarginalProjection
import AlgebraicComplexity.Probability.SupportRestriction
import Mathlib.Tactic.Linarith

/-!
# Sparse finite marginal information projections

The full-support model in `MarginalProjection.lean` is the clean mathematical core.  Concrete
tensor certificates, however, contain structural zeroes.  This file supplies the exact adapter:
restrict both the reference and every feasible law to the positive reference support, invoke the
full-support theorem there, and transport entropy and the rational quadratic correction back to
the ambient certificate arrays.

Unlike positive padding, support restriction does not perturb any probability or entropy.  The
main theorem `conditionalEntropyBits_add_parentQuadratic_le` therefore applies directly to sparse
dyadic certificate tables.
-/

namespace AlgebraicComplexity

universe u₁ u₂ u₃ u₄ u₅

/-- A possibly sparse finite reference law whose positive log-density is controlled by three
feature potentials.  No assertion is made at structural-zero samples. -/
structure SparseThreeMarginalProjectionModel
    (S : Type u₁) (U : Type u₂) (A : Type u₃) (B : Type u₄)
    [Fintype S] [Fintype U] [Fintype A] [Fintype B] where
  reference : ProbabilityVector S
  coarse : S → U
  leftFeature : S → A
  rightFeature : S → B
  coarsePotential : U → ℝ
  leftPotential : A → ℝ
  rightPotential : B → ℝ
  log_reference_weight : ∀ s, 0 < reference.weight s →
    Real.log (reference.weight s) =
      coarsePotential (coarse s) +
        (leftPotential (leftFeature s) + rightPotential (rightFeature s))

namespace SparseThreeMarginalProjectionModel

variable
    {S : Type u₁} {U : Type u₂} {A : Type u₃} {B : Type u₄}
    [Fintype S] [Fintype U] [Fintype A] [Fintype B]
    [DecidableEq U] [DecidableEq A] [DecidableEq B]

/-- Feasibility includes absolute continuity with respect to the structural reference support,
in addition to preservation of the three feature marginals. -/
def IsFeasible (M : SparseThreeMarginalProjectionModel S U A B)
    (q : ProbabilityVector S) : Prop :=
  q.IsAbsolutelyContinuous M.reference ∧
    q.pushforward M.coarse = M.reference.pushforward M.coarse ∧
    q.pushforward M.leftFeature = M.reference.pushforward M.leftFeature ∧
    q.pushforward M.rightFeature = M.reference.pushforward M.rightFeature

/-- The exact full-support information-projection problem obtained by deleting structural
zeroes. -/
noncomputable def onPositiveSupport
    (M : SparseThreeMarginalProjectionModel S U A B) :
    ThreeMarginalProjectionModel M.reference.PositiveSupport U A B where
  reference := M.reference.positiveSupportRestriction
  coarse := M.coarse ∘ Subtype.val
  leftFeature := M.leftFeature ∘ Subtype.val
  rightFeature := M.rightFeature ∘ Subtype.val
  coarsePotential := M.coarsePotential
  leftPotential := M.leftPotential
  rightPotential := M.rightPotential
  reference_pos := M.reference.positiveSupportRestriction_pos
  log_reference_weight s := M.log_reference_weight s.1 s.2

/-- Restricting a sparse feasible law produces a feasible law for the positive-support model. -/
theorem restrict_isFeasible
    (M : SparseThreeMarginalProjectionModel S U A B)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    M.onPositiveSupport.IsFeasible
      (q.restrictToPositiveSupport M.reference hq.1) := by
  rcases hq with ⟨hac, hcoarse, hleft, hright⟩
  constructor
  · change
      (q.restrictToPositiveSupport M.reference hac).pushforward
          (M.coarse ∘ Subtype.val) =
        M.reference.positiveSupportRestriction.pushforward
          (M.coarse ∘ Subtype.val)
    rw [ProbabilityVector.restrictToPositiveSupport_pushforward q M.reference hac M.coarse]
    rw [ProbabilityVector.positiveSupportRestriction_pushforward M.reference M.coarse]
    exact hcoarse
  constructor
  · change
      (q.restrictToPositiveSupport M.reference hac).pushforward
          (M.leftFeature ∘ Subtype.val) =
        M.reference.positiveSupportRestriction.pushforward
          (M.leftFeature ∘ Subtype.val)
    rw [ProbabilityVector.restrictToPositiveSupport_pushforward
      q M.reference hac M.leftFeature]
    rw [ProbabilityVector.positiveSupportRestriction_pushforward
      M.reference M.leftFeature]
    exact hleft
  · change
      (q.restrictToPositiveSupport M.reference hac).pushforward
          (M.rightFeature ∘ Subtype.val) =
        M.reference.positiveSupportRestriction.pushforward
          (M.rightFeature ∘ Subtype.val)
    rw [ProbabilityVector.restrictToPositiveSupport_pushforward
      q M.reference hac M.rightFeature]
    rw [ProbabilityVector.positiveSupportRestriction_pushforward
      M.reference M.rightFeature]
    exact hright

/-- Sparse parent-consistency correction in nats, for an arbitrary ambient parent statistic.
Structural zeroes in the pushed-forward parent law are retained harmlessly. -/
theorem conditionalEntropy_add_parentKl_le
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : SparseThreeMarginalProjectionModel S U A B)
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

/-- Sparse parent-consistency correction in bits. -/
theorem conditionalEntropyBits_add_parentKlBits_le
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : SparseThreeMarginalProjectionModel S U A B)
    (parent : S → P) (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).klDivBits (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropyBits M.coarse := by
  unfold ProbabilityVector.conditionalEntropyBits ProbabilityVector.klDivBits
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (conditionalEntropy_add_parentKl_le M parent q hq)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Fully rational-in-the-laws sparse parent correction used by exact certificate checkers. -/
theorem conditionalEntropyBits_add_parentQuadratic_le
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : SparseThreeMarginalProjectionModel S U A B)
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

/-- Prescribed-parent form of the sparse rational correction. -/
theorem conditionalEntropyBits_le_sub_prescribedParentQuadratic
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : SparseThreeMarginalProjectionModel S U A B)
    (parent : S → P) (q : ProbabilityVector S) (β : ProbabilityVector P)
    (hq : M.IsFeasible q) (hβ : q.pushforward parent = β) :
    q.conditionalEntropyBits M.coarse ≤
      M.reference.conditionalEntropyBits M.coarse -
        β.quadraticKlLowerBits (M.reference.pushforward parent) := by
  have h := conditionalEntropyBits_add_parentQuadratic_le M parent q hq
  rw [hβ] at h
  linarith

end SparseThreeMarginalProjectionModel

end AlgebraicComplexity
