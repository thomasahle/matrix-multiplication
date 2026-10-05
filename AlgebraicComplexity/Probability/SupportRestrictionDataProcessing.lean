/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.KullbackLeibler
import AlgebraicComplexity.Probability.SupportRestrictionCore

/-!
# Sparse deterministic data processing

This module is the lightweight deterministic part of positive-support restriction.  It proves
that restriction commutes with finite pushforward, constructs the induced surjection between
positive supports, and derives KL data processing for arbitrary finite maps and sparse reference
laws.

The derivative-based quantitative KL estimates remain downstream in
`Probability/SupportRestriction.lean`.  Keeping them separate lets entropy and type-counting
clients use sparse data processing without loading the calculus-heavy bounds environment.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ProbabilityVector

variable {I : Type u} [Fintype I]

/-- A deterministic pushforward is unchanged after deleting common structural zeroes. -/
theorem restrictToPositiveSupport_pushforward
    {J : Type v} [Fintype J] [DecidableEq J]
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) (f : I → J) :
    (restrictToPositiveSupport p q h).pushforward (f ∘ Subtype.val) =
      p.pushforward f := by
  apply ProbabilityVector.ext
  funext j
  simp only [pushforward_weight, restrictToPositiveSupport_weight, Function.comp_apply]
  rw [sum_positiveSupport_eq q (fun i ↦ if f i = j then p.weight i else 0)]
  intro i hqi
  simp [h i hqi]

/-- Restriction of a reference law to its own support commutes with every pushforward. -/
theorem positiveSupportRestriction_pushforward
    {J : Type v} [Fintype J] [DecidableEq J]
    (q : ProbabilityVector I) (f : I → J) :
    q.positiveSupportRestriction.pushforward (f ∘ Subtype.val) = q.pushforward f := by
  simpa only [positiveSupportRestriction] using
    restrictToPositiveSupport_pushforward q q (isAbsolutelyContinuous_refl q) f

/-- Absolute continuity is preserved by deterministic pushforward. -/
theorem IsAbsolutelyContinuous.pushforward
    {J : Type v} [Fintype J] [DecidableEq J]
    {p q : ProbabilityVector I} (h : p.IsAbsolutelyContinuous q) (f : I → J) :
    (p.pushforward f).IsAbsolutelyContinuous (q.pushforward f) := by
  intro j hqj
  rw [pushforward_weight]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hfi : f i = j
  · have hqi : q.weight i = 0 := by
      by_contra hqinonzero
      have hqipos : 0 < q.weight i :=
        lt_of_le_of_ne (q.nonneg i) (Ne.symm hqinonzero)
      have hpositive : 0 < (q.pushforward f).weight j := by
        rw [pushforward_weight]
        exact Finset.sum_pos'
          (fun k _ ↦ by split_ifs; exact q.nonneg k; exact le_rfl)
          ⟨i, Finset.mem_univ i, by simp [hfi, hqipos]⟩
      exact hpositive.ne' hqj
    simp [hfi, h i hqi]
  · simp [hfi]

/-- The map induced by `f` from the positive support of a law onto the positive support of its
pushforward. -/
noncomputable def positiveSupportMap
    {J : Type v} [Fintype J] [DecidableEq J]
    (q : ProbabilityVector I) (f : I → J) :
    q.PositiveSupport → (q.pushforward f).PositiveSupport :=
  fun i ↦ ⟨f i.1, by
    rw [pushforward_weight]
    exact Finset.sum_pos'
      (fun k _ ↦ by split_ifs; exact q.nonneg k; exact le_rfl)
      ⟨i.1, Finset.mem_univ i.1, by simp [i.2]⟩⟩

@[simp] theorem positiveSupportMap_val
    {J : Type v} [Fintype J] [DecidableEq J]
    (q : ProbabilityVector I) (f : I → J) (i : q.PositiveSupport) :
    (positiveSupportMap q f i).1 = f i.1 :=
  rfl

/-- Every positive pushforward coordinate has a positive preimage coordinate. -/
theorem positiveSupportMap_surjective
    {J : Type v} [Fintype J] [DecidableEq J]
    (q : ProbabilityVector I) (f : I → J) :
    Function.Surjective (positiveSupportMap q f) := by
  classical
  intro j
  have hj : 0 < ∑ i, if f i = j.1 then q.weight i else 0 := by
    simpa only [pushforward_weight] using j.2
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun i _ ↦ by split_ifs; exact q.nonneg i; exact le_rfl)).mp hj
  by_cases hfi : f i = j.1
  · have hqi : 0 < q.weight i := by simpa [hfi] using hi
    refine ⟨⟨i, hqi⟩, ?_⟩
    apply Subtype.ext
    exact hfi
  · simp [hfi] at hi

/-- Restriction commutes with pushforward after both source and target structural zeroes are
removed. -/
theorem restrictToPositiveSupport_pushforward_positiveSupportMap
    {J : Type v} [Fintype J] [DecidableEq J]
    (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) (f : I → J) :
    (restrictToPositiveSupport p q h).pushforward (positiveSupportMap q f) =
      restrictToPositiveSupport (p.pushforward f) (q.pushforward f) (h.pushforward f) := by
  classical
  apply ProbabilityVector.ext
  funext j
  simp only [pushforward_weight, restrictToPositiveSupport_weight]
  calc
    (∑ i : q.PositiveSupport,
        if positiveSupportMap q f i = j then p.weight i.1 else 0) =
        ∑ i : q.PositiveSupport, if f i.1 = j.1 then p.weight i.1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : f i.1 = j.1
      · have hs : positiveSupportMap q f i = j := Subtype.ext hij
        simp [hij, hs]
      · have hs : positiveSupportMap q f i ≠ j :=
          fun hs ↦ hij (congrArg Subtype.val hs)
        simp [hij, hs]
    _ = ∑ i, if f i = j.1 then p.weight i else 0 := by
      simpa using sum_positiveSupport_eq q
        (fun i ↦ if f i = j.1 then p.weight i else 0)
        (fun i hqi ↦ by simp [h i hqi])
    _ = (p.pushforward f).weight j.1 := by rw [pushforward_weight]

/-- The reference restriction pushes forward to the restriction of the reference pushforward. -/
theorem positiveSupportRestriction_pushforward_positiveSupportMap
    {J : Type v} [Fintype J] [DecidableEq J]
    (q : ProbabilityVector I) (f : I → J) :
    q.positiveSupportRestriction.pushforward (positiveSupportMap q f) =
      (q.pushforward f).positiveSupportRestriction := by
  simpa only [positiveSupportRestriction] using
    restrictToPositiveSupport_pushforward_positiveSupportMap q q
      (isAbsolutelyContinuous_refl q) f

/-- Deterministic data processing for arbitrary finite maps and possibly sparse reference laws.
The existing full-support/surjective theorem is applied exactly on the positive support. -/
theorem klDiv_pushforward_le_of_absoluteContinuity
    {J : Type v} [Fintype J] [DecidableEq J]
    (f : I → J) (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (p.pushforward f).klDiv (q.pushforward f) ≤ p.klDiv q := by
  have hdata := klDiv_pushforward_le
    (positiveSupportMap q f)
    (restrictToPositiveSupport p q h)
    q.positiveSupportRestriction
    q.positiveSupportRestriction_pos
    (positiveSupportMap_surjective q f)
  rw [restrictToPositiveSupport_pushforward_positiveSupportMap p q h f,
    positiveSupportRestriction_pushforward_positiveSupportMap q f,
    restrictToPositiveSupport_klDiv
      (p.pushforward f) (q.pushforward f) (h.pushforward f),
    restrictToPositiveSupport_klDiv p q h] at hdata
  exact hdata

/-- Arbitrary-map sparse-reference data processing in bits. -/
theorem klDivBits_pushforward_le_of_absoluteContinuity
    {J : Type v} [Fintype J] [DecidableEq J]
    (f : I → J) (p q : ProbabilityVector I) (h : p.IsAbsolutelyContinuous q) :
    (p.pushforward f).klDivBits (q.pushforward f) ≤ p.klDivBits q := by
  unfold klDivBits
  exact div_le_div_of_nonneg_right
    (klDiv_pushforward_le_of_absoluteContinuity f p q h)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

end ProbabilityVector

end AlgebraicComplexity
