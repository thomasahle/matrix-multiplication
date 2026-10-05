/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.EntropyChainRule
import AlgebraicComplexity.Probability.EntropyMonotonicity
import AlgebraicComplexity.Probability.Conditioning
import Mathlib.Tactic.Linarith

/-!
# Entropy bounds for finite mixtures

This module packages the two complementary entropy estimates for a finite mixture.  If `mix` is
an outer law and `family b` are its component laws, then

`sum_b mix(b) H(family b) <= H(mix.mixture family)
  <= H(mix) + sum_b mix(b) H(family b)`.

The lower bound is concavity of `Real.negMulLog`; the upper bound reveals the component label and
uses deterministic entropy monotonicity.  Their combination first bounds the conditional-entropy
difference `H(coarse, feature) - H(coarse)`.  A separate, deliberately named theorem bounds the
double-coarse rate residual `H(coarse, feature) - 2 H(coarse)` used by global-competitor hashing.
Keeping the two formulas visibly distinct prevents a conditional-entropy estimate from being
mistaken for the exponent in a tensor-extraction rate.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w x

namespace ProbabilityVector

/-- Entropy is concave under finite mixtures.

Proof sketch: apply finite Jensen to `Real.negMulLog` separately at every output coordinate, then
exchange the two finite sums. -/
theorem sum_entropy_le_entropy_mixture
    {B : Type u} {O : Type v} [Fintype B] [Fintype O]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) :
    (∑ b, mix.weight b * (family b).entropy) ≤ (mix.mixture family).entropy := by
  classical
  unfold entropy
  simp only [mixture_weight]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro o _
  simpa [smul_eq_mul] using
    (Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset B))
      (w := mix.weight)
      (p := fun b ↦ (family b).weight o)
      (fun b _ ↦ mix.nonneg b)
      mix.total
      (fun b _ ↦ (family b).nonneg o))

/-- Revealing the component label bounds the entropy of a finite mixture from above.

Proof sketch: the mixture is the second marginal of `mix.joint family`.  Deterministic entropy
monotonicity and the joint entropy chain rule give the claim. -/
theorem entropy_mixture_le
    {B : Type u} {O : Type v} [Fintype B] [Fintype O]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) :
    (mix.mixture family).entropy ≤
      mix.entropy + ∑ b, mix.weight b * (family b).entropy := by
  classical
  have h := (mix.joint family).entropy_pushforward_le Prod.snd
  rw [pushforward_joint_snd, entropy_joint] at h
  exact h

/-- Concavity of entropy under finite mixtures, measured in bits. -/
theorem sum_entropyBits_le_entropyBits_mixture
    {B : Type u} {O : Type v} [Fintype B] [Fintype O]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) :
    (∑ b, mix.weight b * (family b).entropyBits) ≤
      (mix.mixture family).entropyBits := by
  have h := sum_entropy_le_entropy_mixture mix family
  unfold entropyBits
  calc
    (∑ b, mix.weight b * ((family b).entropy / Real.log 2)) =
        (∑ b, mix.weight b * (family b).entropy) / Real.log 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ (mix.mixture family).entropy / Real.log 2 :=
      div_le_div_of_nonneg_right h (Real.log_pos (by norm_num)).le

/-- Revealing the component label bounds mixture entropy in bits from above. -/
theorem entropyBits_mixture_le
    {B : Type u} {O : Type v} [Fintype B] [Fintype O]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) :
    (mix.mixture family).entropyBits ≤
      mix.entropyBits + ∑ b, mix.weight b * (family b).entropyBits := by
  have h := entropy_mixture_le mix family
  unfold entropyBits
  calc
    (mix.mixture family).entropy / Real.log 2 ≤
        (mix.entropy + ∑ b, mix.weight b * (family b).entropy) / Real.log 2 :=
      div_le_div_of_nonneg_right h (Real.log_pos (by norm_num)).le
    _ = mix.entropy / Real.log 2 +
        ∑ b, mix.weight b * ((family b).entropy / Real.log 2) := by
      rw [add_div, Finset.sum_div]
      apply congrArg (fun x ↦ mix.entropy / Real.log 2 + x)
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Concavity of entropy after applying the same deterministic observation to every component. -/
theorem sum_entropy_pushforward_le_entropy_pushforward_mixture
    {B : Type u} {O : Type v} {A : Type w}
    [Fintype B] [Fintype O] [Fintype A] [DecidableEq A]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) (f : O → A) :
    (∑ b, mix.weight b * ((family b).pushforward f).entropy) ≤
      ((mix.mixture family).pushforward f).entropy := by
  classical
  rw [pushforward_mixture]
  exact sum_entropy_le_entropy_mixture mix (fun b ↦ (family b).pushforward f)

/-- Revealing the component label bounds the entropy of an observed mixture from above. -/
theorem entropy_pushforward_mixture_le
    {B : Type u} {O : Type v} {A : Type w}
    [Fintype B] [Fintype O] [Fintype A] [DecidableEq A]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) (f : O → A) :
    ((mix.mixture family).pushforward f).entropy ≤
      mix.entropy + ∑ b, mix.weight b * ((family b).pushforward f).entropy := by
  classical
  rw [pushforward_mixture]
  exact entropy_mixture_le mix (fun b ↦ (family b).pushforward f)

/-- Concavity in bits after applying the same deterministic observation to every component. -/
theorem sum_entropyBits_pushforward_le_entropyBits_pushforward_mixture
    {B : Type u} {O : Type v} {A : Type w}
    [Fintype B] [Fintype O] [Fintype A] [DecidableEq A]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) (f : O → A) :
    (∑ b, mix.weight b * ((family b).pushforward f).entropyBits) ≤
      ((mix.mixture family).pushforward f).entropyBits := by
  classical
  rw [pushforward_mixture]
  exact sum_entropyBits_le_entropyBits_mixture mix
    (fun b ↦ (family b).pushforward f)

/-- Revealing the component label bounds the entropy in bits of an observed mixture. -/
theorem entropyBits_pushforward_mixture_le
    {B : Type u} {O : Type v} {A : Type w}
    [Fintype B] [Fintype O] [Fintype A] [DecidableEq A]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O) (f : O → A) :
    ((mix.mixture family).pushforward f).entropyBits ≤
      mix.entropyBits + ∑ b, mix.weight b * ((family b).pushforward f).entropyBits := by
  classical
  rw [pushforward_mixture]
  exact entropyBits_mixture_le mix (fun b ↦ (family b).pushforward f)

/-- A nonnegative multiple of an observed entropy may be subtracted componentwise through a
finite mixture.

For any `coarsePenalty ≥ 0`, the global residual
`H(coarse, feature) - coarsePenalty * H(coarse)` is at most the outer entropy plus the weighted
component residuals.  The theorem does not require disjoint component supports or recoverability
of the outer label.  The conditional-entropy and global-competitor formulas are respectively the
special cases `coarsePenalty = 1` and `coarsePenalty = 2` below.

Proof sketch: upper-bound the joint observation by revealing the component label.  Entropy
concavity lower-bounds the coarse observation; multiply that inequality by the nonnegative
penalty, subtract it, and distribute the resulting finite sum. -/
theorem entropy_pair_sub_mul_entropy_coarse_mixture_le
    {B : Type u} {O : Type v} {C : Type w} {L : Type x}
    [Fintype B] [Fintype O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O)
    (coarse : O → C) (feature : O → L)
    (coarsePenalty : ℝ) (hpenalty : 0 ≤ coarsePenalty) (bound : B → ℝ)
    (hbound : ∀ b,
      ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy -
          coarsePenalty * ((family b).pushforward coarse).entropy ≤ bound b) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropy -
        coarsePenalty * ((mix.mixture family).pushforward coarse).entropy ≤
      mix.entropy + ∑ b, mix.weight b * bound b := by
  classical
  have hpair := entropy_pushforward_mixture_le mix family
    (fun o ↦ (coarse o, feature o))
  have hcoarse := sum_entropy_pushforward_le_entropy_pushforward_mixture
    mix family coarse
  have hcoarseScaled :
      coarsePenalty *
          (∑ b, mix.weight b * ((family b).pushforward coarse).entropy) ≤
        coarsePenalty * ((mix.mixture family).pushforward coarse).entropy :=
    mul_le_mul_of_nonneg_left hcoarse hpenalty
  have hweighted :
      (∑ b, mix.weight b *
        (((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy -
          coarsePenalty * ((family b).pushforward coarse).entropy)) ≤
        ∑ b, mix.weight b * bound b := by
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left (hbound b) (mix.nonneg b)
  have hweighted' :
      (∑ b, mix.weight b *
          ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy) -
        coarsePenalty *
          ∑ b, mix.weight b * ((family b).pushforward coarse).entropy ≤
        ∑ b, mix.weight b * bound b := by
    calc
      (∑ b, mix.weight b *
          ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy) -
          coarsePenalty *
            ∑ b, mix.weight b * ((family b).pushforward coarse).entropy =
        ∑ b, mix.weight b *
          (((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy -
            coarsePenalty * ((family b).pushforward coarse).entropy) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro b _
          ring
      _ ≤ ∑ b, mix.weight b * bound b := hweighted
  calc
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropy -
        coarsePenalty * ((mix.mixture family).pushforward coarse).entropy ≤
      mix.entropy +
        ((∑ b, mix.weight b *
            ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy) -
          coarsePenalty *
            ∑ b, mix.weight b * ((family b).pushforward coarse).entropy) := by
        linarith
    _ ≤ mix.entropy + ∑ b, mix.weight b * bound b := by
      linarith

/-- Base-two form of `entropy_pair_sub_mul_entropy_coarse_mixture_le`. -/
theorem entropyBits_pair_sub_mul_entropyBits_coarse_mixture_le
    {B : Type u} {O : Type v} {C : Type w} {L : Type x}
    [Fintype B] [Fintype O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O)
    (coarse : O → C) (feature : O → L)
    (coarsePenalty : ℝ) (hpenalty : 0 ≤ coarsePenalty) (bound : B → ℝ)
    (hbound : ∀ b,
      ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          coarsePenalty * ((family b).pushforward coarse).entropyBits ≤ bound b) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        coarsePenalty * ((mix.mixture family).pushforward coarse).entropyBits ≤
      mix.entropyBits + ∑ b, mix.weight b * bound b := by
  classical
  have hpair := entropyBits_pushforward_mixture_le mix family
    (fun o ↦ (coarse o, feature o))
  have hcoarse := sum_entropyBits_pushforward_le_entropyBits_pushforward_mixture
    mix family coarse
  have hcoarseScaled :
      coarsePenalty *
          (∑ b, mix.weight b * ((family b).pushforward coarse).entropyBits) ≤
        coarsePenalty * ((mix.mixture family).pushforward coarse).entropyBits :=
    mul_le_mul_of_nonneg_left hcoarse hpenalty
  have hweighted :
      (∑ b, mix.weight b *
        (((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          coarsePenalty * ((family b).pushforward coarse).entropyBits)) ≤
        ∑ b, mix.weight b * bound b := by
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left (hbound b) (mix.nonneg b)
  have hweighted' :
      (∑ b, mix.weight b *
          ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits) -
        coarsePenalty *
          ∑ b, mix.weight b * ((family b).pushforward coarse).entropyBits ≤
        ∑ b, mix.weight b * bound b := by
    calc
      (∑ b, mix.weight b *
          ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits) -
          coarsePenalty *
            ∑ b, mix.weight b * ((family b).pushforward coarse).entropyBits =
        ∑ b, mix.weight b *
          (((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
            coarsePenalty * ((family b).pushforward coarse).entropyBits) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro b _
          ring
      _ ≤ ∑ b, mix.weight b * bound b := hweighted
  calc
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        coarsePenalty * ((mix.mixture family).pushforward coarse).entropyBits ≤
      mix.entropyBits +
        ((∑ b, mix.weight b *
            ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits) -
          coarsePenalty *
            ∑ b, mix.weight b * ((family b).pushforward coarse).entropyBits) := by
        linarith
    _ ≤ mix.entropyBits + ∑ b, mix.weight b * bound b := by
      linarith

/-! ## Conditional-entropy and double-coarse specializations -/

/-- The conditional-entropy difference `H(coarse, feature) - H(coarse)` of a finite mixture is at
most the outer entropy plus the weighted componentwise differences. -/
theorem entropy_pair_sub_entropy_coarse_mixture_le
    {B : Type u} {O : Type v} {C : Type w} {L : Type x}
    [Fintype B] [Fintype O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O)
    (coarse : O → C) (feature : O → L) (bound : B → ℝ)
    (hbound : ∀ b,
      ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy -
          ((family b).pushforward coarse).entropy ≤ bound b) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropy -
        ((mix.mixture family).pushforward coarse).entropy ≤
      mix.entropy + ∑ b, mix.weight b * bound b := by
  simpa using entropy_pair_sub_mul_entropy_coarse_mixture_le
    mix family coarse feature (1 : ℝ) (by norm_num) bound (by
      intro b
      simpa using hbound b)

/-- Base-two form of `entropy_pair_sub_entropy_coarse_mixture_le`. -/
theorem entropyBits_pair_sub_entropyBits_coarse_mixture_le
    {B : Type u} {O : Type v} {C : Type w} {L : Type x}
    [Fintype B] [Fintype O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O)
    (coarse : O → C) (feature : O → L) (bound : B → ℝ)
    (hbound : ∀ b,
      ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          ((family b).pushforward coarse).entropyBits ≤ bound b) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        ((mix.mixture family).pushforward coarse).entropyBits ≤
      mix.entropyBits + ∑ b, mix.weight b * bound b := by
  simpa using entropyBits_pair_sub_mul_entropyBits_coarse_mixture_le
    mix family coarse feature (1 : ℝ) (by norm_num) bound (by
      intro b
      simpa using hbound b)

/-! ## The double-coarse residual used by global-competitor rates -/

/-- A finite mixture bounds the rate residual
`H(coarse, feature) - 2 H(coarse)` by the outer entropy plus the weighted component residuals.

Equivalently, this is `H(feature | coarse) - H(coarse)`.  The second coarse-entropy subtraction is
essential in total-weight hashing rates and is deliberately visible in the theorem name.

Proof sketch: upper-bound the joint observation by revealing the mixture label, and apply entropy
concavity twice to the two subtracted copies of the coarse observation. -/
theorem entropy_pair_sub_two_mul_entropy_coarse_mixture_le
    {B : Type u} {O : Type v} {C : Type w} {L : Type x}
    [Fintype B] [Fintype O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O)
    (coarse : O → C) (feature : O → L) (bound : B → ℝ)
    (hbound : ∀ b,
      ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropy -
          2 * ((family b).pushforward coarse).entropy ≤ bound b) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropy -
        2 * ((mix.mixture family).pushforward coarse).entropy ≤
      mix.entropy + ∑ b, mix.weight b * bound b := by
  simpa using entropy_pair_sub_mul_entropy_coarse_mixture_le
    mix family coarse feature (2 : ℝ) (by norm_num) bound hbound

/-- Base-two form of `entropy_pair_sub_two_mul_entropy_coarse_mixture_le`. -/
theorem entropyBits_pair_sub_two_mul_entropyBits_coarse_mixture_le
    {B : Type u} {O : Type v} {C : Type w} {L : Type x}
    [Fintype B] [Fintype O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector B) (family : B → ProbabilityVector O)
    (coarse : O → C) (feature : O → L) (bound : B → ℝ)
    (hbound : ∀ b,
      ((family b).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          2 * ((family b).pushforward coarse).entropyBits ≤ bound b) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        2 * ((mix.mixture family).pushforward coarse).entropyBits ≤
      mix.entropyBits + ∑ b, mix.weight b * bound b := by
  simpa using entropyBits_pair_sub_mul_entropyBits_coarse_mixture_le
    mix family coarse feature (2 : ℝ) (by norm_num) bound hbound

/-- Splitting into a common (`false`) component and an exceptional (`true`) component bounds the
conditional-entropy difference by the entropy of the split plus one bit per exceptional sample.

The hypotheses are deliberately semantic: the common component has nonpositive
conditional-entropy difference and the exceptional component has difference at most one bit.  A
finite-support client can establish those facts by its own rigidity and two-point-fiber arguments.

Proof sketch: specialize the general residual theorem to bounds `0` and `1`; the weighted bound is
exactly the probability of the exceptional component. -/
theorem entropyBits_pair_sub_entropyBits_coarse_boolMixture_le
    {O : Type v} {C : Type w} {L : Type x}
    [Fintype O] [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector Bool) (family : Bool → ProbabilityVector O)
    (coarse : O → C) (feature : O → L)
    (hcommon :
      ((family false).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          ((family false).pushforward coarse).entropyBits ≤ 0)
    (hexceptional :
      ((family true).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          ((family true).pushforward coarse).entropyBits ≤ 1) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        ((mix.mixture family).pushforward coarse).entropyBits ≤
      mix.entropyBits + mix.weight true := by
  have h := entropyBits_pair_sub_entropyBits_coarse_mixture_le
    mix family coarse feature (fun b ↦ if b then 1 else 0) (by
      intro b
      cases b
      · simpa using hcommon
      · simpa using hexceptional)
  simpa using h

/-- Boolean specialization of the double-coarse rate-residual inequality.  A nonpositive common
component and a one-bit exceptional component cost at most `H₂(B) + P(B=true)` globally. -/
theorem entropyBits_pair_sub_two_mul_entropyBits_coarse_boolMixture_le
    {O : Type v} {C : Type w} {L : Type x}
    [Fintype O] [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L]
    (mix : ProbabilityVector Bool) (family : Bool → ProbabilityVector O)
    (coarse : O → C) (feature : O → L)
    (hcommon :
      ((family false).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          2 * ((family false).pushforward coarse).entropyBits ≤ 0)
    (hexceptional :
      ((family true).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
          2 * ((family true).pushforward coarse).entropyBits ≤ 1) :
    ((mix.mixture family).pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        2 * ((mix.mixture family).pushforward coarse).entropyBits ≤
      mix.entropyBits + mix.weight true := by
  have h := entropyBits_pair_sub_two_mul_entropyBits_coarse_mixture_le
    mix family coarse feature (fun b ↦ if b then 1 else 0) (by
      intro b
      cases b
      · simpa using hcommon
      · simpa using hexceptional)
  simpa using h

/-- Conditional-entropy-difference bound obtained by conditioning one finite law on a
deterministic label.

This is the direct event-splitting form of
`entropyBits_pair_sub_entropyBits_coarse_mixture_le`: callers prove one difference bound for each
normalized fiber, while the theorem reconstructs the original law automatically.  Zero-mass
fibers use the point-mass convention from `conditionOnFiber`, so their contribution is
definitionally harmless.

Proof sketch: decompose the law through `mixture_conditionOnFiber`, then apply the finite-mixture
residual theorem. -/
theorem entropyBits_pair_sub_entropyBits_coarse_conditionOnFiber_le
    {B : Type u} {O : Type v} {C : Type w} {L : Type x}
    [Fintype B] [DecidableEq B] [Fintype O] [Nonempty O]
    [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L]
    (p : ProbabilityVector O) (label : O → B)
    (coarse : O → C) (feature : O → L) (bound : B → ℝ)
    (hbound : ∀ b,
      ((p.conditionOnFiber label b).pushforward
          (fun o ↦ (coarse o, feature o))).entropyBits -
        ((p.conditionOnFiber label b).pushforward coarse).entropyBits ≤ bound b) :
    (p.pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        (p.pushforward coarse).entropyBits ≤
      (p.pushforward label).entropyBits +
        ∑ b, (p.pushforward label).weight b * bound b := by
  have h := entropyBits_pair_sub_entropyBits_coarse_mixture_le
    (p.pushforward label) (p.conditionOnFiber label) coarse feature bound hbound
  simpa only [mixture_conditionOnFiber] using h

/-- Revealing a Boolean exceptional event bounds the conditional-entropy difference by its entropy
plus one bit per exceptional sample, provided the common conditional law has nonpositive
difference and the exceptional conditional law has difference at most one bit. -/
theorem entropyBits_pair_sub_entropyBits_coarse_boolConditioning_le
    {O : Type v} {C : Type w} {L : Type x}
    [Fintype O] [Nonempty O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (p : ProbabilityVector O) (exceptional : O → Bool)
    (coarse : O → C) (feature : O → L)
    (hcommon :
      ((p.conditionOnFiber exceptional false).pushforward
          (fun o ↦ (coarse o, feature o))).entropyBits -
        ((p.conditionOnFiber exceptional false).pushforward coarse).entropyBits ≤ 0)
    (hexceptional :
      ((p.conditionOnFiber exceptional true).pushforward
          (fun o ↦ (coarse o, feature o))).entropyBits -
        ((p.conditionOnFiber exceptional true).pushforward coarse).entropyBits ≤ 1) :
    (p.pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        (p.pushforward coarse).entropyBits ≤
      (p.pushforward exceptional).entropyBits +
        (p.pushforward exceptional).weight true := by
  have h := entropyBits_pair_sub_entropyBits_coarse_conditionOnFiber_le
    p exceptional coarse feature (fun b ↦ if b then 1 else 0) (by
      intro b
      cases b
      · simpa using hcommon
      · simpa using hexceptional)
  simpa using h

/-- Direct deterministic-event form of the double-coarse rate-residual inequality. -/
theorem entropyBits_pair_sub_two_mul_entropyBits_coarse_boolConditioning_le
    {O : Type v} {C : Type w} {L : Type x}
    [Fintype O] [Nonempty O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (p : ProbabilityVector O) (exceptional : O → Bool)
    (coarse : O → C) (feature : O → L)
    (hcommon :
      ((p.conditionOnFiber exceptional false).pushforward
          (fun o ↦ (coarse o, feature o))).entropyBits -
        2 * ((p.conditionOnFiber exceptional false).pushforward coarse).entropyBits ≤ 0)
    (hexceptional :
      ((p.conditionOnFiber exceptional true).pushforward
          (fun o ↦ (coarse o, feature o))).entropyBits -
        2 * ((p.conditionOnFiber exceptional true).pushforward coarse).entropyBits ≤ 1) :
    (p.pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        2 * (p.pushforward coarse).entropyBits ≤
      (p.pushforward exceptional).entropyBits +
        (p.pushforward exceptional).weight true := by
  have h := entropyBits_pair_sub_two_mul_entropyBits_coarse_boolMixture_le
    (p.pushforward exceptional) (p.conditionOnFiber exceptional)
    coarse feature hcommon hexceptional
  simpa only [mixture_conditionOnFiber] using h

/-- Conditioning on the same coarse statistic that is subtracted from the entropy introduces no
extra reveal-the-label cost.

Each normalized coarse fiber contributes only the entropy of the requested joint observation.
The statement is an inequality because different coarse fibers are assembled with the general
mixture upper bound; no positivity of individual coarse masses is required.

Proof sketch: reconstruct `p` from its coarse conditional laws.  Apply the observed-mixture upper
bound to `(coarse, feature)`, then cancel the outer entropy, which is exactly the entropy of
`p.pushforward coarse`. -/
theorem entropyBits_pair_sub_entropyBits_coarse_conditionOnFiber_le_sum
    {O : Type v} {C : Type w} {L : Type x}
    [Fintype O] [Nonempty O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (p : ProbabilityVector O) (coarse : O → C) (feature : O → L)
    (bound : C → ℝ)
    (hbound : ∀ c,
      ((p.conditionOnFiber coarse c).pushforward
        (fun o ↦ (coarse o, feature o))).entropyBits ≤ bound c) :
    (p.pushforward (fun o ↦ (coarse o, feature o))).entropyBits -
        (p.pushforward coarse).entropyBits ≤
      ∑ c, (p.pushforward coarse).weight c * bound c := by
  classical
  have hpair := entropyBits_pushforward_mixture_le
    (p.pushforward coarse) (p.conditionOnFiber coarse)
    (fun o ↦ (coarse o, feature o))
  rw [mixture_conditionOnFiber] at hpair
  have hweighted :
      (∑ c, (p.pushforward coarse).weight c *
        ((p.conditionOnFiber coarse c).pushforward
          (fun o ↦ (coarse o, feature o))).entropyBits) ≤
        ∑ c, (p.pushforward coarse).weight c * bound c := by
    apply Finset.sum_le_sum
    intro c _
    exact mul_le_mul_of_nonneg_left (hbound c) ((p.pushforward coarse).nonneg c)
  linarith

/-- If a feature is constant on the positive part of one coarse fiber, the joint
`(coarse, feature)` observation of the corresponding conditional law has zero entropy.

The theorem is zero-safe: when the coarse fiber has zero mass, `conditionOnFiber` is a point mass
and the conclusion still holds without consulting `hconstant`.
-/
theorem entropyBits_pushforward_pair_conditionOnFiber_eq_zero_of_constant
    {O : Type v} {C : Type w} {L : Type x}
    [Fintype O] [Nonempty O] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L]
    (p : ProbabilityVector O) (coarse : O → C) (feature : O → L)
    (c : C) (value : L)
    (hconstant : ∀ o, 0 < p.weight o → coarse o = c → feature o = value) :
    ((p.conditionOnFiber coarse c).pushforward
      (fun o ↦ (coarse o, feature o))).entropyBits = 0 := by
  classical
  by_cases hmass : (p.pushforward coarse).weight c = 0
  · rw [conditionOnFiber_eq_pointMass_of_weight_eq_zero p coarse c hmass,
      pushforward_pointMass]
    exact entropyBits_pointMass _
  · have hpoint :
        (p.conditionOnFiber coarse c).pushforward
            (fun o ↦ (coarse o, feature o)) = pointMass (c, value) := by
      apply pushforward_eq_pointMass_of_forall_weight_pos
      intro o hpos
      rw [conditionOnFiber_weight_of_ne p coarse c hmass] at hpos
      by_cases hcoarse : coarse o = c
      · have hpne : p.weight o ≠ 0 := by
          intro hpzero
          simp [hcoarse, hpzero] at hpos
        have hp : 0 < p.weight o :=
          lt_of_le_of_ne (p.nonneg o) (Ne.symm hpne)
        exact Prod.ext hcoarse (hconstant o hp hcoarse)
      · simp [hcoarse] at hpos
    rw [hpoint]
    exact entropyBits_pointMass (c, value)

end ProbabilityVector

end AlgebraicComplexity
