/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.CrossEntropyDefs
import AlgebraicComplexity.Probability.Entropy
import AlgebraicComplexity.Probability.KullbackLeiblerDefs

/-!
# Core restriction to a positive probability support

This lightweight module removes common structural zeroes from two finite probability laws without
renormalizing them.  It defines the positive-support restriction and proves preservation of total
mass, expectations, entropy, and finite Kullback--Leibler divergence.

Deterministic pushforward, conditional-entropy, data-processing, and quadratic-bound laws live in
`Probability/SupportRestriction.lean`.  Keeping those downstream prevents elementary sparse-law
arguments from importing derivative-based KL estimates.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ProbabilityVector

variable {I : Type u} [Fintype I]

/-- The finite subtype on which a reference probability vector is strictly positive. -/
abbrev PositiveSupport (q : ProbabilityVector I) := {i : I // 0 < q.weight i}

noncomputable instance (q : ProbabilityVector I) : Fintype q.PositiveSupport :=
  inferInstanceAs (Fintype {i : I // 0 < q.weight i})

/-- A nonnegative probability coordinate outside the positive support is zero. -/
theorem weight_eq_zero_of_not_mem_positiveSupport
    (q : ProbabilityVector I) (i : I) (hi : ¬ 0 < q.weight i) :
    q.weight i = 0 := by
  exact le_antisymm (not_lt.mp hi) (q.nonneg i)

/-- Summing a function that vanishes off the positive support may be performed on the support
subtype instead of the ambient finite type. -/
theorem sum_positiveSupport_eq
    (q : ProbabilityVector I) (f : I → ℝ)
    (hzero : ∀ i, q.weight i = 0 → f i = 0) :
    (∑ i : q.PositiveSupport, f i.1) = ∑ i, f i := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I ↦ 0 < q.weight i) f
  have hcomplement :
      (∑ i : {i : I // ¬ 0 < q.weight i}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hzero i.1 (weight_eq_zero_of_not_mem_positiveSupport q i.1 i.2)
  rw [hcomplement, add_zero] at hsplit
  exact hsplit

/-- Restrict `p` to the positive support of an absolutely-continuous reference `q`.

The weights are unchanged, rather than conditionally renormalized. -/
noncomputable def restrictToPositiveSupport
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    ProbabilityVector q.PositiveSupport where
  weight i := p.weight i.1
  nonneg i := p.nonneg i.1
  total := by
    rw [sum_positiveSupport_eq q p.weight h]
    exact p.total

@[simp] theorem restrictToPositiveSupport_weight
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q)
    (i : q.PositiveSupport) :
    (restrictToPositiveSupport p q h).weight i = p.weight i.1 :=
  rfl

/-- A law is absolutely continuous with respect to itself. -/
theorem isAbsolutelyContinuous_refl (p : ProbabilityVector I) :
    p.IsAbsolutelyContinuous p := by
  intro i h
  exact h

/-- The reference law restricted to its own positive support. -/
noncomputable def positiveSupportRestriction (q : ProbabilityVector I) :
    ProbabilityVector q.PositiveSupport :=
  restrictToPositiveSupport q q (isAbsolutelyContinuous_refl q)

@[simp] theorem positiveSupportRestriction_weight
    (q : ProbabilityVector I) (i : q.PositiveSupport) :
    q.positiveSupportRestriction.weight i = q.weight i.1 :=
  rfl

/-- The restricted reference is strictly positive at every coordinate. -/
theorem positiveSupportRestriction_pos
    (q : ProbabilityVector I) (i : q.PositiveSupport) :
    0 < q.positiveSupportRestriction.weight i :=
  i.2

/-- Restriction preserves expectations of ambient statistics. -/
theorem restrictToPositiveSupport_expectation
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) (f : I → ℝ) :
    (restrictToPositiveSupport p q h).expectation (f ∘ Subtype.val) =
      p.expectation f := by
  unfold expectation
  simp only [restrictToPositiveSupport_weight, Function.comp_apply]
  rw [sum_positiveSupport_eq q (fun i ↦ p.weight i * f i)]
  intro i hqi
  simp [h i hqi]

/-- Restriction preserves Shannon entropy. -/
theorem restrictToPositiveSupport_entropy
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (restrictToPositiveSupport p q h).entropy = p.entropy := by
  unfold entropy
  simp only [restrictToPositiveSupport_weight]
  rw [sum_positiveSupport_eq q (fun i ↦ Real.negMulLog (p.weight i))]
  intro i hqi
  simp [h i hqi]

/-- Restriction preserves base-two Shannon entropy. -/
theorem restrictToPositiveSupport_entropyBits
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (restrictToPositiveSupport p q h).entropyBits = p.entropyBits := by
  unfold entropyBits
  rw [restrictToPositiveSupport_entropy p q h]

/-- Restricting a reference law to its own support preserves entropy. -/
theorem positiveSupportRestriction_entropy (q : ProbabilityVector I) :
    q.positiveSupportRestriction.entropy = q.entropy := by
  simpa only [positiveSupportRestriction] using
    restrictToPositiveSupport_entropy q q (isAbsolutelyContinuous_refl q)

/-- Restricting a reference law to its own support preserves entropy in bits. -/
theorem positiveSupportRestriction_entropyBits (q : ProbabilityVector I) :
    q.positiveSupportRestriction.entropyBits = q.entropyBits := by
  simpa only [positiveSupportRestriction] using
    restrictToPositiveSupport_entropyBits q q (isAbsolutelyContinuous_refl q)

/-- Restriction preserves finite KL divergence, with the ambient `0 / 0 = 0` convention on
deleted common-zero coordinates. -/
theorem restrictToPositiveSupport_klDiv
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (restrictToPositiveSupport p q h).klDiv q.positiveSupportRestriction =
      p.klDiv q := by
  unfold klDiv
  simp only [restrictToPositiveSupport_weight, positiveSupportRestriction_weight]
  rw [sum_positiveSupport_eq q (fun i ↦
    p.weight i * Real.log (p.weight i / q.weight i))]
  intro i hqi
  simp [h i hqi]

/-- Restriction preserves finite KL divergence in bits. -/
theorem restrictToPositiveSupport_klDivBits
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (restrictToPositiveSupport p q h).klDivBits q.positiveSupportRestriction =
      p.klDivBits q := by
  unfold klDivBits
  rw [restrictToPositiveSupport_klDiv p q h]

end ProbabilityVector

end AlgebraicComplexity
