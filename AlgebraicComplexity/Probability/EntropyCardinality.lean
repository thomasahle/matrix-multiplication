/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.KullbackLeiblerBasic
import AlgebraicComplexity.Probability.SupportRestrictionCore
import AlgebraicComplexity.Probability.EntropyMonotonicity

/-!
# Entropy bounds from finite support cardinality

This module proves the standard finite-alphabet estimate

`H(p) ≤ log |I|`

for the repository's concrete `ProbabilityVector`, then sharpens it by deleting zero-weight
coordinates.  Its base-two two-point corollary says that any law supported on at most two points
has entropy at most one bit.  These are generic finite-information statements; tensor clients
should use them instead of reproducing a paper-specific cardinality calculation.
-/

namespace AlgebraicComplexity

universe u

namespace ProbabilityVector

variable {I : Type u} [Fintype I]

/-- The Shannon entropy of a law on a nonempty finite alphabet is at most the logarithm of the
alphabet cardinality.

Proof sketch: compare the law with the uniform distribution.  Expanding the nonnegative KL
divergence against that full-support reference gives exactly `log |I| - H(p)`.
-/
theorem entropy_le_log_card [Nonempty I] (p : ProbabilityVector I) :
    p.entropy ≤ Real.log (Fintype.card I : ℝ) := by
  let uniform := uniformVector I
  have huniform : ∀ i, 0 < uniform.weight i := by
    intro i
    exact uniformVector_weight_pos i
  have hkl := klDiv_nonneg p uniform huniform
  rw [klDiv_eq_neg_entropy_sub_expectation_log p uniform huniform] at hkl
  have hexpect :
      p.expectation (fun i ↦ Real.log (uniform.weight i)) =
        Real.log ((Fintype.card I : ℝ)⁻¹) := by
    simpa only [uniform, uniformVector_weight] using
      p.expectation_const (Real.log ((Fintype.card I : ℝ)⁻¹))
  rw [hexpect, Real.log_inv] at hkl
  linarith

/-- Base-two form of the finite-alphabet entropy bound. -/
theorem entropyBits_le_log_card_div_log_two [Nonempty I] (p : ProbabilityVector I) :
    p.entropyBits ≤ Real.log (Fintype.card I : ℝ) / Real.log 2 := by
  unfold entropyBits
  exact div_le_div_of_nonneg_right p.entropy_le_log_card
    (Real.log_pos (by norm_num)).le

/-- Every probability vector has at least one positive coordinate. -/
theorem positiveSupport_nonempty (p : ProbabilityVector I) : Nonempty p.PositiveSupport := by
  classical
  have hsum : 0 < ∑ i, p.weight i := by rw [p.total]; norm_num
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ p.nonneg i)).mp hsum
  exact ⟨⟨i, hi⟩⟩

/-- Entropy is bounded by the logarithm of the number of positive-weight coordinates, rather than
the size of the ambient alphabet.

Proof sketch: restrict the law to its positive support, where entropy is unchanged, and apply the
finite-alphabet bound on that subtype. -/
theorem entropy_le_log_card_positiveSupport (p : ProbabilityVector I) :
    p.entropy ≤ Real.log (Fintype.card p.PositiveSupport : ℝ) := by
  letI : Nonempty p.PositiveSupport := p.positiveSupport_nonempty
  rw [← p.positiveSupportRestriction_entropy]
  exact p.positiveSupportRestriction.entropy_le_log_card

/-- Base-two positive-support cardinality bound. -/
theorem entropyBits_le_log_card_positiveSupport_div_log_two
    (p : ProbabilityVector I) :
    p.entropyBits ≤
      Real.log (Fintype.card p.PositiveSupport : ℝ) / Real.log 2 := by
  unfold entropyBits
  exact div_le_div_of_nonneg_right p.entropy_le_log_card_positiveSupport
    (Real.log_pos (by norm_num)).le

/-- A probability law with at most two positive coordinates has entropy at most one bit. -/
theorem entropyBits_le_one_of_card_positiveSupport_le_two
    (p : ProbabilityVector I) (hcard : Fintype.card p.PositiveSupport ≤ 2) :
    p.entropyBits ≤ 1 := by
  have hpositive : 0 < Fintype.card p.PositiveSupport :=
    Fintype.card_pos_iff.mpr p.positiveSupport_nonempty
  have hcast : (Fintype.card p.PositiveSupport : ℝ) ≤ 2 := by
    exact_mod_cast hcard
  have hlog : Real.log (Fintype.card p.PositiveSupport : ℝ) ≤ Real.log 2 :=
    Real.log_le_log (Nat.cast_pos.mpr hpositive) hcast
  calc
    p.entropyBits ≤
        Real.log (Fintype.card p.PositiveSupport : ℝ) / Real.log 2 :=
      p.entropyBits_le_log_card_positiveSupport_div_log_two
    _ ≤ Real.log 2 / Real.log 2 :=
      div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num)).le
    _ = 1 := div_self (Real.log_pos (by norm_num)).ne'

/-- A deterministic observation of a law supported on at most two source points has entropy at
most one bit.  The ambient source and target alphabets may be much larger.

Proof sketch: every positive output coordinate has a positive source preimage, so the positive
output support injects into the image of the supplied source-support set.  That image has at most
two elements, and the positive-support cardinality bound applies. -/
theorem entropyBits_pushforward_le_one_of_support_card_le_two
    {O : Type*} [Fintype O] [DecidableEq O]
    (p : ProbabilityVector I) (f : I → O) (support : Finset I)
    (hsupport : ∀ i, 0 < p.weight i → i ∈ support)
    (hcard : support.card ≤ 2) :
    (p.pushforward f).entropyBits ≤ 1 := by
  classical
  let outputSupport : Finset O := support.image f
  let embed : (p.pushforward f).PositiveSupport → {o : O // o ∈ outputSupport} :=
    fun o ↦ ⟨o.1, by
      have hsum : 0 < ∑ i, if f i = o.1 then p.weight i else 0 := by
        simpa only [pushforward_weight] using o.2
      obtain ⟨i, _, hi⟩ :=
        (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ by
          by_cases hfi : f i = o.1
          · simpa [hfi] using p.nonneg i
          · simp [hfi])).mp hsum
      have hfi : f i = o.1 := by
        by_contra hne
        simp [hne] at hi
      have hpi : 0 < p.weight i := by simpa [hfi] using hi
      exact Finset.mem_image.mpr ⟨i, hsupport i hpi, hfi⟩⟩
  have hinjective : Function.Injective embed := by
    intro left right h
    apply Subtype.ext
    simpa [embed] using congrArg Subtype.val h
  have houtputCard : Fintype.card (p.pushforward f).PositiveSupport ≤ 2 := by
    calc
      Fintype.card (p.pushforward f).PositiveSupport ≤
          Fintype.card {o : O // o ∈ outputSupport} :=
        Fintype.card_le_of_injective embed hinjective
      _ = outputSupport.card := by simp
      _ ≤ support.card := Finset.card_image_le
      _ ≤ 2 := hcard
  exact (p.pushforward f).entropyBits_le_one_of_card_positiveSupport_le_two houtputCard

/-- The elementary scalar lower bound `x(1-x) ≤ -x log x` on the probability interval. -/
private theorem mul_one_sub_le_negMulLog {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x) ≤ Real.negMulLog x := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp
  · have hlog := Real.log_le_sub_one_of_pos hxpos
    have hscaled := mul_le_mul_of_nonneg_left hlog hx
    rw [Real.negMulLog_eq_neg]
    nlinarith

/-- If `i` is a maximum-weight coordinate, entropy in bits dominates the total mass away from
that coordinate: `1 - p(i) ≤ H₂(p)`.

Proof sketch: `p(j)(1-p(j)) ≤ -p(j) log p(j)` coordinatewise.  Maximality gives
`sum_j p(j)^2 ≤ p(i)`, hence `1-p(i) ≤ sum_j p(j)(1-p(j)) ≤ H(p)`.  Finally
`log 2 ≤ 1`, so converting nats to bits can only increase this nonnegative quantity. -/
theorem one_sub_weight_le_entropyBits_of_forall_weight_le
    (p : ProbabilityVector I) (i : I) (hmax : ∀ j, p.weight j ≤ p.weight i) :
    1 - p.weight i ≤ p.entropyBits := by
  classical
  have hsq : ∑ j, (p.weight j) ^ 2 ≤ p.weight i := by
    calc
      (∑ j, (p.weight j) ^ 2) ≤ ∑ j, p.weight i * p.weight j := by
        apply Finset.sum_le_sum
        intro j _
        have hmul := mul_le_mul_of_nonneg_right (hmax j) (p.nonneg j)
        nlinarith
      _ = p.weight i * ∑ j, p.weight j := by rw [Finset.mul_sum]
      _ = p.weight i := by rw [p.total, mul_one]
  have hquadratic :
      ∑ j, p.weight j * (1 - p.weight j) =
        1 - ∑ j, (p.weight j) ^ 2 := by
    calc
      (∑ j, p.weight j * (1 - p.weight j)) =
          ∑ j, (p.weight j - (p.weight j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ j, p.weight j) - ∑ j, (p.weight j) ^ 2 :=
        by rw [← Finset.sum_sub_distrib]
      _ = 1 - ∑ j, (p.weight j) ^ 2 := by rw [p.total]
  have htoEntropy :
      ∑ j, p.weight j * (1 - p.weight j) ≤ p.entropy := by
    unfold entropy
    apply Finset.sum_le_sum
    intro j _
    exact mul_one_sub_le_negMulLog (p.nonneg j) (p.weight_le_one j)
  have hnatToBits : p.entropy ≤ p.entropyBits := by
    have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogLeOne : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    unfold entropyBits
    rw [le_div_iff₀ hlogPos]
    exact mul_le_of_le_one_right p.entropy_nonneg hlogLeOne
  rw [hquadratic] at htoEntropy
  exact (by linarith : 1 - p.weight i ≤ p.entropy).trans hnatToBits

end ProbabilityVector

end AlgebraicComplexity
