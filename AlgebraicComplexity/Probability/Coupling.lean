/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.EntropyChainRule
import AlgebraicComplexity.Probability.KullbackLeiblerBasic
import AlgebraicComplexity.Probability.Pushforward
import AlgebraicComplexity.Probability.SupportRestrictionCore
import Mathlib.Tactic.Linarith

/-!
# Finite couplings and entropy subadditivity

This module is the reusable core of the two-letter probability API.  It defines a finite coupling,
proves exact marginal and product laws, establishes Shannon-entropy subadditivity even for sparse
marginals, and shows that the independent product maximizes entropy among all couplings with fixed
marginals.

Channels, mutual-information identities, parent-consistency corrections, and three-feature
combination loss remain in `Probability/TwoLetter.lean`.  Separating them lets ordinary
maximum-entropy tensorization use only the coupling theorem it mathematically needs.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w x y z u' v'

namespace ProbabilityVector

variable {D : Type u} {E : Type v} [Fintype D] [Fintype E]

/-! ## Pushforwards and finite couplings -/

/-- Expectations may be changed pointwise wherever the law has nonzero mass. -/
theorem expectation_congr_of_weight_ne_zero
    {I : Type u} [Fintype I] (p : ProbabilityVector I) (f g : I → ℝ)
    (h : ∀ i, p.weight i ≠ 0 → f i = g i) :
    p.expectation f = p.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p.weight i = 0
  · simp [hi]
  · rw [h i hi]

/-- A joint finite law has prescribed first and second marginals. -/
def IsCoupling (joint : ProbabilityVector (D × E))
    (left : ProbabilityVector D) (right : ProbabilityVector E)
    [DecidableEq D] [DecidableEq E] : Prop :=
  joint.pushforward Prod.fst = left ∧ joint.pushforward Prod.snd = right

namespace IsCoupling

variable [DecidableEq D] [DecidableEq E]
variable {joint : ProbabilityVector (D × E)}
variable {left : ProbabilityVector D} {right : ProbabilityVector E}

/-- Every joint law is canonically a coupling of its own coordinate marginals. -/
theorem marginals (joint : ProbabilityVector (D × E)) :
    joint.IsCoupling (joint.pushforward Prod.fst) (joint.pushforward Prod.snd) :=
  ⟨rfl, rfl⟩

/-- The first coordinate preserves every downstream deterministic interface exactly. -/
theorem pushforward_left
    (h : joint.IsCoupling left right)
    {A : Type w} [Fintype A] [DecidableEq A] (f : D → A) :
    joint.pushforward (f ∘ Prod.fst) = left.pushforward f := by
  rw [← pushforward_comp f Prod.fst joint, h.1]

/-- The second coordinate preserves every downstream deterministic interface exactly. -/
theorem pushforward_right
    (h : joint.IsCoupling left right)
    {A : Type w} [Fintype A] [DecidableEq A] (f : E → A) :
    joint.pushforward (f ∘ Prod.snd) = right.pushforward f := by
  rw [← pushforward_comp f Prod.snd joint, h.2]

/-- Expectations of first-coordinate statistics agree with the first marginal. -/
theorem expectation_left (h : joint.IsCoupling left right) (f : D → ℝ) :
    joint.expectation (f ∘ Prod.fst) = left.expectation f := by
  rw [← pushforward_expectation Prod.fst joint f, h.1]

/-- Expectations of second-coordinate statistics agree with the second marginal. -/
theorem expectation_right (h : joint.IsCoupling left right) (f : E → ℝ) :
    joint.expectation (f ∘ Prod.snd) = right.expectation f := by
  rw [← pushforward_expectation Prod.snd joint f, h.2]

/-- Applying one deterministic interface to each coordinate sends a coupling to a coupling of
the two pushed-forward laws. -/
theorem pushforward_prodMap
    (h : joint.IsCoupling left right)
    {A : Type w} {B : Type x}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : D → A) (g : E → B) :
    (joint.pushforward (fun de ↦ (f de.1, g de.2))).IsCoupling
      (left.pushforward f) (right.pushforward g) := by
  constructor
  · calc
      (joint.pushforward (fun de ↦ (f de.1, g de.2))).pushforward Prod.fst =
          joint.pushforward (Prod.fst ∘ fun de ↦ (f de.1, g de.2)) :=
        pushforward_comp _ _ _
      _ = joint.pushforward (f ∘ Prod.fst) := by rfl
      _ = left.pushforward f := h.pushforward_left f
  · calc
      (joint.pushforward (fun de ↦ (f de.1, g de.2))).pushforward Prod.snd =
          joint.pushforward (Prod.snd ∘ fun de ↦ (f de.1, g de.2)) :=
        pushforward_comp _ _ _
      _ = joint.pushforward (g ∘ Prod.snd) := by rfl
      _ = right.pushforward g := h.pushforward_right g

/-- A coupling is absolutely continuous with respect to the product of its marginals. -/
theorem isAbsolutelyContinuous_product (h : joint.IsCoupling left right) :
    joint.IsAbsolutelyContinuous (left.product right) := by
  rintro ⟨d, e⟩ hzero
  rw [product_weight] at hzero
  rcases mul_eq_zero.mp hzero with hleft | hright
  · have hle := weight_le_pushforward_weight Prod.fst joint (d, e)
    rw [h.1] at hle
    exact le_antisymm (by simpa [hleft] using hle) (joint.nonneg (d, e))
  · have hle := weight_le_pushforward_weight Prod.snd joint (d, e)
    rw [h.2] at hle
    exact le_antisymm (by simpa [hright] using hle) (joint.nonneg (d, e))

end IsCoupling

/-- The first marginal of an independent product is its first factor. -/
@[simp] theorem pushforward_product_fst [DecidableEq D]
    (left : ProbabilityVector D) (right : ProbabilityVector E) :
    (left.product right).pushforward Prod.fst = left := by
  change (left.joint (fun _ ↦ right)).pushforward Prod.fst = left
  exact pushforward_joint_fst left (fun _ ↦ right)

/-- The second marginal of an independent product is its second factor. -/
@[simp] theorem pushforward_product_snd [DecidableEq E]
    (left : ProbabilityVector D) (right : ProbabilityVector E) :
    (left.product right).pushforward Prod.snd = right := by
  classical
  ext e
  rw [pushforward_weight, Fintype.sum_prod_type]
  simp_rw [product_weight]
  calc
    (∑ d, ∑ e', if e' = e then left.weight d * right.weight e' else 0) =
        ∑ d, left.weight d * right.weight e := by simp
    _ = (∑ d, left.weight d) * right.weight e := by rw [Finset.sum_mul]
    _ = right.weight e := by rw [left.total, one_mul]

/-- Independent products are couplings of their factors. -/
theorem product_isCoupling [DecidableEq D] [DecidableEq E]
    (left : ProbabilityVector D) (right : ProbabilityVector E) :
    (left.product right).IsCoupling left right :=
  ⟨pushforward_product_fst left right, pushforward_product_snd left right⟩

/-- Independent products commute with applying deterministic interfaces to both coordinates. -/
theorem pushforward_product_prodMap
    {A : Type w} {B : Type x}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (left : ProbabilityVector D) (right : ProbabilityVector E)
    (f : D → A) (g : E → B) :
    (left.product right).pushforward (fun de ↦ (f de.1, g de.2)) =
      (left.pushforward f).product (right.pushforward g) := by
  classical
  ext ab
  rcases ab with ⟨a, b⟩
  simp only [pushforward_weight, product_weight, Fintype.sum_prod_type]
  calc
    (∑ d, ∑ e, if (f d, g e) = (a, b) then left.weight d * right.weight e else 0) =
        ∑ d, (if f d = a then left.weight d else 0) *
          ∑ e, if g e = b then right.weight e else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : f d = a
      · simp only [hd, if_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : g e = b <;> simp [he]
      · simp [hd]
    _ = (∑ d, if f d = a then left.weight d else 0) *
          ∑ e, if g e = b then right.weight e else 0 := by
      rw [Finset.sum_mul]

/-! ## Entropy of arbitrary couplings -/

/-- Sparse-reference form of the entropy-gap identity. -/
theorem klDiv_eq_entropy_sub_of_expectation_log_eq_of_absoluteContinuity
    {I : Type u} [Fintype I] (p q : ProbabilityVector I)
    (hac : p.IsAbsolutelyContinuous q)
    (hlog : p.expectation (fun i ↦ Real.log (q.weight i)) =
      q.expectation (fun i ↦ Real.log (q.weight i))) :
    p.klDiv q = q.entropy - p.entropy := by
  let p' := restrictToPositiveSupport p q hac
  let q' := q.positiveSupportRestriction
  have hlog' : p'.expectation (fun i ↦ Real.log (q'.weight i)) =
      q'.expectation (fun i ↦ Real.log (q'.weight i)) := by
    change
      p'.expectation ((fun i ↦ Real.log (q.weight i)) ∘ Subtype.val) =
        q'.expectation ((fun i ↦ Real.log (q.weight i)) ∘ Subtype.val)
    rw [restrictToPositiveSupport_expectation p q hac,
      show q' = restrictToPositiveSupport q q (isAbsolutelyContinuous_refl q) by rfl,
      restrictToPositiveSupport_expectation q q (isAbsolutelyContinuous_refl q)]
    exact hlog
  have hgap := klDiv_eq_entropy_sub_of_expectation_log_eq
    p' q' q.positiveSupportRestriction_pos hlog'
  rw [show p' = restrictToPositiveSupport p q hac by rfl,
    show q' = q.positiveSupportRestriction by rfl,
    restrictToPositiveSupport_klDiv p q hac,
    positiveSupportRestriction_entropy q,
    restrictToPositiveSupport_entropy p q hac] at hgap
  exact hgap

/-- Gibbs' inequality for a sparse reference under absolute continuity. -/
theorem klDiv_nonneg_of_absoluteContinuity
    {I : Type u} [Fintype I] (p q : ProbabilityVector I)
    (hac : p.IsAbsolutelyContinuous q) :
    0 ≤ p.klDiv q := by
  have h := klDiv_nonneg
    (restrictToPositiveSupport p q hac) q.positiveSupportRestriction
      q.positiveSupportRestriction_pos
  rw [restrictToPositiveSupport_klDiv p q hac] at h
  exact h

/-- The expected log-density of a product reference splits into its two marginal terms under
every coupling of those marginals. -/
theorem IsCoupling.expectation_log_product
    [DecidableEq D] [DecidableEq E]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) :
    joint.expectation (fun de ↦ Real.log ((left.product right).weight de)) =
      left.expectation (fun d ↦ Real.log (left.weight d)) +
        right.expectation (fun e ↦ Real.log (right.weight e)) := by
  have hac := h.isAbsolutelyContinuous_product
  calc
    joint.expectation (fun de ↦ Real.log ((left.product right).weight de)) =
        joint.expectation (fun de ↦
          Real.log (left.weight de.1) + Real.log (right.weight de.2)) := by
      apply expectation_congr_of_weight_ne_zero
      intro de hjoint
      have hproduct : (left.product right).weight de ≠ 0 := by
        intro hzero
        exact hjoint (hac de hzero)
      have hmarginals : left.weight de.1 ≠ 0 ∧ right.weight de.2 ≠ 0 := by
        change left.weight de.1 * right.weight de.2 ≠ 0 at hproduct
        exact mul_ne_zero_iff.mp hproduct
      exact Real.log_mul hmarginals.1 hmarginals.2
    _ = joint.expectation (fun de ↦ Real.log (left.weight de.1)) +
          joint.expectation (fun de ↦ Real.log (right.weight de.2)) :=
      expectation_add joint _ _
    _ = left.expectation (fun d ↦ Real.log (left.weight d)) +
          right.expectation (fun e ↦ Real.log (right.weight e)) := by
      congr 1
      · have hleft := h.expectation_left (fun d ↦ Real.log (left.weight d))
        unfold Function.comp at hleft
        exact hleft
      · have hright := h.expectation_right (fun e ↦ Real.log (right.weight e))
        unfold Function.comp at hright
        exact hright

/-- KL divergence from the product of the marginals is exactly the entropy-subadditivity gap. -/
theorem IsCoupling.klDiv_product_eq_entropy_gap
    [DecidableEq D] [DecidableEq E]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) :
    joint.klDiv (left.product right) =
      left.entropy + right.entropy - joint.entropy := by
  have hreference := (product_isCoupling left right).expectation_log_product
  have hlog :
      joint.expectation (fun de ↦ Real.log ((left.product right).weight de)) =
        (left.product right).expectation
          (fun de ↦ Real.log ((left.product right).weight de)) :=
    h.expectation_log_product.trans hreference.symm
  calc
    joint.klDiv (left.product right) =
        (left.product right).entropy - joint.entropy :=
      klDiv_eq_entropy_sub_of_expectation_log_eq_of_absoluteContinuity
        joint (left.product right) h.isAbsolutelyContinuous_product hlog
    _ = left.entropy + right.entropy - joint.entropy := by
      rw [entropy_product]

/-- Finite Shannon entropy is subadditive for an arbitrary coupling. -/
theorem IsCoupling.entropy_le_add
    [DecidableEq D] [DecidableEq E]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) :
    joint.entropy ≤ left.entropy + right.entropy := by
  have hnonneg := klDiv_nonneg_of_absoluteContinuity
    joint (left.product right) h.isAbsolutelyContinuous_product
  rw [h.klDiv_product_eq_entropy_gap] at hnonneg
  linarith

/-- Base-two entropy is subadditive for an arbitrary coupling. -/
theorem IsCoupling.entropyBits_le_add
    [DecidableEq D] [DecidableEq E]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) :
    joint.entropyBits ≤ left.entropyBits + right.entropyBits := by
  unfold entropyBits
  rw [← add_div]
  exact div_le_div_of_nonneg_right h.entropy_le_add
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The independent product has maximum entropy among all couplings with the same marginals. -/
theorem product_isMaximumEntropyCoupling
    [DecidableEq D] [DecidableEq E]
    (left : ProbabilityVector D) (right : ProbabilityVector E) :
    ∀ joint : ProbabilityVector (D × E),
      joint.IsCoupling left right → joint.entropy ≤ (left.product right).entropy := by
  intro joint hjoint
  rw [entropy_product]
  exact hjoint.entropy_le_add

end ProbabilityVector

end AlgebraicComplexity
