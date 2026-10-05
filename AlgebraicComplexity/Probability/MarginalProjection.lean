/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.KullbackLeiblerBounds
import Mathlib.Tactic.Linarith

/-!
# Finite marginal information projections

This module proves the support-aware form of the parent-consistency argument.  The fine sample
space `S` is arbitrary, so it may already be the subtype of structurally legal states.  A positive
reference law has a log-density that decomposes into potentials of three finite features.  Every
law preserving those feature marginals therefore has the same reference-log-density expectation.

For any surjective statistic `parent : S → P`, deterministic data processing gives

`H(Q | coarse) + D(Q_parent || reference_parent) ≤ H(reference | coarse)`.

The parent statistic need not be the raw pair of child symbols.  In recursive tensor applications
it can be the exact complete-split concatenation/scatter map.  A rational quadratic corollary is
also provided for certificate checking.
-/

namespace AlgebraicComplexity

universe u₁ u₂ u₃ u₄ u₅

/-- A positive finite reference law whose log-density is a sum of three marginal potentials. -/
structure ThreeMarginalProjectionModel
    (S : Type u₁) (U : Type u₂) (A : Type u₃) (B : Type u₄)
    [Fintype S] [Fintype U] [Fintype A] [Fintype B] where
  reference : ProbabilityVector S
  coarse : S → U
  leftFeature : S → A
  rightFeature : S → B
  coarsePotential : U → ℝ
  leftPotential : A → ℝ
  rightPotential : B → ℝ
  reference_pos : ∀ s, 0 < reference.weight s
  log_reference_weight : ∀ s,
    Real.log (reference.weight s) =
      coarsePotential (coarse s) +
        (leftPotential (leftFeature s) + rightPotential (rightFeature s))

namespace ThreeMarginalProjectionModel

variable
    {S : Type u₁} {U : Type u₂} {A : Type u₃} {B : Type u₄}
    [Fintype S] [Fintype U] [Fintype A] [Fintype B]
    [DecidableEq U] [DecidableEq A] [DecidableEq B]

/-- Feasible laws preserve exactly the three feature marginals controlling the reference
log-density. -/
def IsFeasible (M : ThreeMarginalProjectionModel S U A B)
    (q : ProbabilityVector S) : Prop :=
  q.pushforward M.coarse = M.reference.pushforward M.coarse ∧
    q.pushforward M.leftFeature = M.reference.pushforward M.leftFeature ∧
    q.pushforward M.rightFeature = M.reference.pushforward M.rightFeature

/-- The reference log-density has invariant expectation on the feasible affine family. -/
theorem expectation_log_reference_eq
    (M : ThreeMarginalProjectionModel S U A B)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.expectation (fun s ↦ Real.log (M.reference.weight s)) =
      M.reference.expectation (fun s ↦ Real.log (M.reference.weight s)) := by
  rcases hq with ⟨hcoarse, hleft, hright⟩
  let c : S → ℝ := M.coarsePotential ∘ M.coarse
  let l : S → ℝ := M.leftPotential ∘ M.leftFeature
  let r : S → ℝ := M.rightPotential ∘ M.rightFeature
  calc
    q.expectation (fun s ↦ Real.log (M.reference.weight s)) =
        q.expectation (fun s ↦ c s + (l s + r s)) :=
      q.expectation_congr M.log_reference_weight
    _ = q.expectation c + (q.expectation l + q.expectation r) := by
      rw [ProbabilityVector.expectation_add, ProbabilityVector.expectation_add]
    _ = M.reference.expectation c +
        (M.reference.expectation l + M.reference.expectation r) := by
      rw [ProbabilityVector.expectation_comp_eq_of_pushforward_eq
          M.coarse q M.reference hcoarse M.coarsePotential,
        ProbabilityVector.expectation_comp_eq_of_pushforward_eq
          M.leftFeature q M.reference hleft M.leftPotential,
        ProbabilityVector.expectation_comp_eq_of_pushforward_eq
          M.rightFeature q M.reference hright M.rightPotential]
    _ = M.reference.expectation (fun s ↦ c s + (l s + r s)) := by
      rw [ProbabilityVector.expectation_add, ProbabilityVector.expectation_add]
    _ = M.reference.expectation (fun s ↦ Real.log (M.reference.weight s)) :=
      M.reference.expectation_congr (fun s ↦ (M.log_reference_weight s).symm)

/-- Parent-consistency correction for an arbitrary structural parent map, in nats. -/
theorem conditionalEntropy_add_parentKl_le
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : ThreeMarginalProjectionModel S U A B)
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

/-- Parent-consistency correction for an arbitrary structural parent map, in bits. -/
theorem conditionalEntropyBits_add_parentKlBits_le
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : ThreeMarginalProjectionModel S U A B)
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

/-- Rational quadratic version for an arbitrary structural parent map. -/
theorem conditionalEntropyBits_add_parentQuadratic_le
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : ThreeMarginalProjectionModel S U A B)
    (parent : S → P) (hparent : Function.Surjective parent)
    (q : ProbabilityVector S) (hq : M.IsFeasible q) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).quadraticKlLowerBits (M.reference.pushforward parent) ≤
      M.reference.conditionalEntropyBits M.coarse := by
  have hreferenceParent : ∀ z, 0 < (M.reference.pushforward parent).weight z :=
    ProbabilityVector.pushforward_weight_pos_of_surjective
      parent M.reference M.reference_pos hparent
  have hquadratic := ProbabilityVector.quadraticKlLowerBits_le_klDivBits
    (q.pushforward parent) (M.reference.pushforward parent) hreferenceParent
  have hkl := conditionalEntropyBits_add_parentKlBits_le M parent hparent q hq
  linarith

/-- Prescribed-parent rational correction for an arbitrary structural parent map. -/
theorem conditionalEntropyBits_le_sub_prescribedParentQuadratic
    {P : Type u₅} [Fintype P] [DecidableEq P]
    (M : ThreeMarginalProjectionModel S U A B)
    (parent : S → P) (hparent : Function.Surjective parent)
    (q : ProbabilityVector S) (β : ProbabilityVector P)
    (hq : M.IsFeasible q) (hβ : q.pushforward parent = β) :
    q.conditionalEntropyBits M.coarse ≤
      M.reference.conditionalEntropyBits M.coarse -
        β.quadraticKlLowerBits (M.reference.pushforward parent) := by
  have h := conditionalEntropyBits_add_parentQuadratic_le M parent hparent q hq
  rw [hβ] at h
  linarith

end ThreeMarginalProjectionModel

end AlgebraicComplexity
