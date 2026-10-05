/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite

/-!
# Deterministic pushforwards and finite mixtures

This lightweight module proves the functorial law for deterministic pushforwards of
`ProbabilityVector`s, their compatibility with finite mixtures, and the second marginal of a
joint law.  It is kept below the coupling and reindexing layers so clients that only compose finite
statistics or channels do not import entropy, Kullback--Leibler divergence, or the two-letter
compatibility calculus.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w

namespace ProbabilityVector

/-- Deterministically observing a point mass gives the point mass at the observed value. -/
@[simp] theorem pushforward_pointMass
    {I : Type u} {O : Type v} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (f : I → O) (i : I) :
    (pointMass i).pushforward f = pointMass (f i) := by
  classical
  ext o
  simp only [pushforward_weight, pointMass_weight]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro j _ hji
    simp [hji]
  · simp

/-- If a deterministic observation is constant on every positive-weight coordinate, its
pushforward is the corresponding point mass.  Zero-weight coordinates need not satisfy the
constant-value equation. -/
theorem pushforward_eq_pointMass_of_forall_weight_pos
    {I : Type u} {O : Type v} [Fintype I] [Fintype O] [DecidableEq O]
    (p : ProbabilityVector I) (f : I → O) (o : O)
    (hconstant : ∀ i, 0 < p.weight i → f i = o) :
    p.pushforward f = pointMass o := by
  classical
  ext y
  rw [pushforward_weight, pointMass_weight]
  by_cases hy : y = o
  · subst y
    calc
      (∑ i, if f i = o then p.weight i else 0) = ∑ i, p.weight i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : f i = o
        · simp [hi]
        · have hnotpos : ¬ 0 < p.weight i := fun hpos ↦ hi (hconstant i hpos)
          have hzero : p.weight i = 0 :=
            le_antisymm (not_lt.mp hnotpos) (p.nonneg i)
          simp [hi, hzero]
      _ = 1 := p.total
      _ = (if o = o then 1 else 0) := by simp
  · have hzero : ∀ i, f i = y → p.weight i = 0 := by
      intro i hiy
      have hnotpos : ¬ 0 < p.weight i := by
        intro hpos
        have hio := hconstant i hpos
        exact hy (hiy.symm.trans hio)
      exact le_antisymm (not_lt.mp hnotpos) (p.nonneg i)
    simp only [hy, if_false]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hiy : f i = y
    · simp [hiy, hzero i hiy]
    · simp [hiy]

/-- Finite pushforwards compose exactly.

Proof sketch: expand both pushforwards, exchange the two finite sums, and observe that for each
source coordinate only the intermediate value `f i` contributes. -/
theorem pushforward_comp
    {I : Type u} {J : Type v} {K : Type w}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (g : J → K) (f : I → J) (p : ProbabilityVector I) :
    (p.pushforward f).pushforward g = p.pushforward (g ∘ f) := by
  classical
  ext k
  simp only [pushforward_weight]
  calc
    (∑ j, if g j = k then ∑ i, if f i = j then p.weight i else 0 else 0) =
        ∑ j, ∑ i, if g j = k then
          (if f i = j then p.weight i else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : g j = k <;> simp [hj]
    _ = ∑ i, ∑ j, if g j = k then
          (if f i = j then p.weight i else 0) else 0 := Finset.sum_comm
    _ = ∑ i, if (g ∘ f) i = k then p.weight i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (f i)]
      · simp [Function.comp_apply]
      · intro j _ hji
        simp [Ne.symm hji]
      · simp

/-- Applying a finite channel and then pushing forward is the mixture of the pushed-forward
conditional laws.

Proof sketch: expand the two finite sums, exchange them, and factor the outer channel weight. -/
theorem pushforward_mixture
    {I : Type u} {O : Type v} {A : Type w}
    [Fintype I] [Fintype O] [Fintype A] [DecidableEq A]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) (f : O → A) :
    (input.mixture channel).pushforward f =
      input.mixture (fun i ↦ (channel i).pushforward f) := by
  classical
  ext a
  simp only [pushforward_weight, mixture_weight]
  calc
    (∑ o, if f o = a then ∑ i, input.weight i * (channel i).weight o else 0) =
        ∑ o, ∑ i, if f o = a then input.weight i * (channel i).weight o else 0 := by
      apply Finset.sum_congr rfl
      intro o _
      by_cases ho : f o = a <;> simp [ho]
    _ = ∑ i, ∑ o, if f o = a then input.weight i * (channel i).weight o else 0 :=
      Finset.sum_comm
    _ = ∑ i, input.weight i * ∑ o,
          if f o = a then (channel i).weight o else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      by_cases ho : f o = a <;> simp [ho]

/-- The second marginal of a finite joint law is its channel mixture.

Proof sketch: sum the joint weights over the unused first coordinate. -/
@[simp] theorem pushforward_joint_snd
    {I : Type u} {O : Type v} [Fintype I] [Fintype O] [DecidableEq O]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) :
    (input.joint channel).pushforward Prod.snd = input.mixture channel := by
  classical
  ext o
  rw [pushforward_weight, Fintype.sum_prod_type]
  simp only [joint_weight, mixture_weight]
  apply Finset.sum_congr rfl
  intro i _
  simp

end ProbabilityVector

end AlgebraicComplexity
