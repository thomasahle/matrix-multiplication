/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.FiniteCoreDefs

/-!
# Finite probability vectors

This file provides a small optimizer-independent type for probability vectors on a finite type.
It is useful for type distributions, regional weights, and randomized constructions throughout
algebraic complexity.

The point-mass construction is the formal version of a one-hot choice.  In particular, it makes
zero weights first-class legal data rather than a boundary case hidden in side conditions.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ProbabilityVector

variable {ι : Type u} [Fintype ι]

/-- A full-support probability vector remains full-support after pushforward along a surjection. -/
theorem pushforward_weight_pos_of_surjective {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p : ProbabilityVector ι)
    (hp : ∀ i, 0 < p.weight i) (hf : Function.Surjective f) (k : κ) :
    0 < (p.pushforward f).weight k := by
  obtain ⟨i, rfl⟩ := hf k
  exact Finset.sum_pos' (fun j _ ↦ by
    by_cases h : f j = f i
    · simpa [h] using p.nonneg j
    · simp [h]) ⟨i, Finset.mem_univ i, by simp [hp i]⟩

/-- One source coordinate is bounded by the mass of its pushforward fiber. -/
theorem weight_le_pushforward_weight
    {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq J]
    (f : I → J) (p : ProbabilityVector I) (i : I) :
    p.weight i ≤ (p.pushforward f).weight (f i) := by
  classical
  rw [pushforward_weight]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset I),
      0 ≤ if f j = f i then p.weight j else 0 := by
    intro j _
    split_ifs
    · exact p.nonneg j
    · exact le_rfl
  have h := Finset.single_le_sum hnonneg (Finset.mem_univ i)
  simpa using h

/-- Transport a finite probability vector along an equivalence of sample spaces. -/
def reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (p : ProbabilityVector ι) : ProbabilityVector κ where
  weight k := p.weight (e.symm k)
  nonneg k := p.nonneg (e.symm k)
  total := by
    classical
    rw [e.symm.sum_comp p.weight, p.total]

@[simp] theorem reindex_weight {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (p : ProbabilityVector ι) (k : κ) :
    (p.reindex e).weight k = p.weight (e.symm k) :=
  rfl

/-- Independent product of two finite probability vectors. -/
def product {κ : Type*} [Fintype κ]
    (p : ProbabilityVector ι) (q : ProbabilityVector κ) : ProbabilityVector (ι × κ) where
  weight x := p.weight x.1 * q.weight x.2
  nonneg x := mul_nonneg (p.nonneg x.1) (q.nonneg x.2)
  total := by
    classical
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, q.total, mul_one]
    exact p.total

@[simp] theorem product_weight {κ : Type*} [Fintype κ]
    (p : ProbabilityVector ι) (q : ProbabilityVector κ) (i : ι) (k : κ) :
    (p.product q).weight (i, k) = p.weight i * q.weight k :=
  rfl

@[simp] theorem joint_weight {κ : Type*} [Fintype κ]
    (p : ProbabilityVector ι) (family : ι → ProbabilityVector κ)
    (i : ι) (k : κ) :
    (p.joint family).weight (i, k) = p.weight i * (family i).weight k :=
  rfl

/-- A finite mixture of probability vectors.  The outer probability vector supplies the mixture
weights and the family supplies the conditional distributions. -/
def mixture {κ : Type*} [Fintype κ]
    (mix : ProbabilityVector κ) (family : κ → ProbabilityVector ι) : ProbabilityVector ι where
  weight i := ∑ k, mix.weight k * (family k).weight i
  nonneg i := Finset.sum_nonneg fun k _ ↦ mul_nonneg (mix.nonneg k) ((family k).nonneg i)
  total := by
    classical
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (family _).total, mul_one]
    exact mix.total

@[simp] theorem mixture_weight {κ : Type*} [Fintype κ]
    (mix : ProbabilityVector κ) (family : κ → ProbabilityVector ι) (i : ι) :
    (mix.mixture family).weight i = ∑ k, mix.weight k * (family k).weight i :=
  rfl

/-- Pointwise `L∞` closeness of two finite probability vectors.  For a finite sample space this
is equivalent to saying that their maximum absolute coordinate difference is at most `ε`, while
avoiding an arbitrary choice of a maximizing coordinate. -/
def LinftyClose (p q : ProbabilityVector ι) (ε : ℝ) : Prop :=
  ∀ i, |p.weight i - q.weight i| ≤ ε

theorem linftyClose_refl (p : ProbabilityVector ι) {ε : ℝ} (hε : 0 ≤ ε) :
    LinftyClose p p ε := by
  intro i
  simpa using hε

theorem LinftyClose.symm {p q : ProbabilityVector ι} {ε : ℝ}
    (h : LinftyClose p q ε) : LinftyClose q p ε := by
  intro i
  simpa [abs_sub_comm] using h i

theorem LinftyClose.mono {p q : ProbabilityVector ι} {ε δ : ℝ}
    (h : LinftyClose p q ε) (hεδ : ε ≤ δ) : LinftyClose p q δ :=
  fun i ↦ (h i).trans hεδ

@[simp] theorem pointMass_weight [DecidableEq ι] (i j : ι) :
    (pointMass i).weight j = if j = i then 1 else 0 := rfl

@[simp] theorem pointMass_weight_self [DecidableEq ι] (i : ι) :
    (pointMass i).weight i = 1 := by
  simp

@[simp] theorem pointMass_weight_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) :
    (pointMass i).weight j = 0 := by
  simp [h]

/-- Expectation of a real statistic under a finite probability vector. -/
def expectation (p : ProbabilityVector ι) (f : ι → ℝ) : ℝ :=
  ∑ i, p.weight i * f i

theorem expectation_congr (p : ProbabilityVector ι) {f g : ι → ℝ}
    (h : ∀ i, f i = g i) :
    p.expectation f = p.expectation g := by
  unfold expectation
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (p.weight i * ·) (h i)

/-- The expectation of the zero statistic vanishes. -/
@[simp] theorem expectation_zero (p : ProbabilityVector ι) :
    p.expectation 0 = 0 := by
  simp [expectation]

theorem expectation_add (p : ProbabilityVector ι) (f g : ι → ℝ) :
    p.expectation (fun i ↦ f i + g i) = p.expectation f + p.expectation g := by
  unfold expectation
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

theorem expectation_const (p : ProbabilityVector ι) (c : ℝ) :
    p.expectation (fun _ ↦ c) = c := by
  unfold expectation
  rw [← Finset.sum_mul, p.total, one_mul]

/-- Expectations commute with finite pushforward. -/
theorem pushforward_expectation {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p : ProbabilityVector ι) (g : κ → ℝ) :
    (p.pushforward f).expectation g = p.expectation (g ∘ f) := by
  classical
  unfold expectation
  simp_rw [pushforward_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Function.comp_apply]

/-- Equal pushforwards give equal expectations of every statistic on the target. -/
theorem expectation_comp_eq_of_pushforward_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p q : ProbabilityVector ι)
    (h : p.pushforward f = q.pushforward f) (g : κ → ℝ) :
    p.expectation (g ∘ f) = q.expectation (g ∘ f) := by
  rw [← pushforward_expectation, h, pushforward_expectation]

@[simp] theorem pointMass_expectation [DecidableEq ι] (i : ι) (f : ι → ℝ) :
    (pointMass i).expectation f = f i := by
  classical
  simp [expectation, pointMass]

/-- A family of point masses that selects the same slot for every term.  This is the legal
constituent-stage specialization used when all terms of one outer region must remain together
before taking the minimum of their branch totals. -/
def constantPointMass {κ : Type*} [DecidableEq ι] (i : ι) : κ → ProbabilityVector ι :=
  fun _ ↦ pointMass i

@[simp] theorem constantPointMass_apply {κ : Type*} [DecidableEq ι] (i : ι) (k : κ) :
    constantPointMass (κ := κ) i k = pointMass i := rfl

/-- The uniform probability vector on a nonempty finite type. -/
noncomputable def uniformVector (ι : Type u) [Fintype ι] [Nonempty ι] : ProbabilityVector ι where
  weight _ := (Fintype.card ι : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hq : (Fintype.card ι : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hq]

@[simp] theorem uniformVector_weight [Nonempty ι] (i : ι) :
    (uniformVector ι).weight i = (Fintype.card ι : ℝ)⁻¹ := rfl

/-- The uniform vector has full support. -/
theorem uniformVector_weight_pos [Nonempty ι] (i : ι) : 0 < (uniformVector ι).weight i := by
  rw [uniformVector_weight]
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

/-! ## A uniform lower bound caps every single coordinate

If every coordinate of a probability vector carries mass at least `c`, then no coordinate can
carry much more than `c` either, because the remaining `|ι| - 1` coordinates already use up
`(|ι| - 1)·c` of the total mass.  This is the dual half of a "near-uniform window" and is the
step that turns a one-sided window into a two-sided one. -/

/-- **A uniform lower bound on the coordinates caps each of them from above.**  If `c ≤ v(b)` for
every `b`, then `v(a) ≤ 1 - (|ι| - 1)·c` for every `a`.

Proof sketch: the total mass `1` splits as `v(a)` plus the mass of the other `|ι| - 1`
coordinates, and the latter is at least `(|ι| - 1)·c`. -/
theorem weight_le_one_sub_of_forall_le (v : ProbabilityVector ι) {c : ℝ}
    (h : ∀ b, c ≤ v.weight b) (a : ι) :
    v.weight a ≤ 1 - ((Fintype.card ι : ℝ) - 1) * c := by
  classical
  have hone : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨a⟩
  have hcard : (((Finset.univ : Finset ι).erase a).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Nat.cast_sub hone, Nat.cast_one]
  have hrest := Finset.card_nsmul_le_sum ((Finset.univ : Finset ι).erase a) v.weight c
    fun b _ ↦ h b
  rw [nsmul_eq_mul, hcard] at hrest
  have hsplit : v.weight a + ∑ b ∈ (Finset.univ : Finset ι).erase a, v.weight b = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    exact v.total
  have hrw : v.weight a = 1 - ∑ b ∈ (Finset.univ : Finset ι).erase a, v.weight b :=
    eq_sub_of_add_eq hsplit
  rw [hrw]
  exact sub_le_sub_left hrest 1

/-! ## Event masses

The mass of a finite *event* — a `Finset` of sample points — and the two facts that make it a
usable bookkeeping device: it is monotone, and pairwise disjoint events cannot together carry
more than the total mass `1`. -/

/-- The total mass a probability vector assigns to a finite event. -/
def eventMass (v : ProbabilityVector ι) (A : Finset ι) : ℝ := ∑ a ∈ A, v.weight a

@[simp] theorem eventMass_empty (v : ProbabilityVector ι) : v.eventMass ∅ = 0 := rfl

@[simp] theorem eventMass_univ (v : ProbabilityVector ι) :
    v.eventMass Finset.univ = 1 := v.total

/-- Event masses are nonnegative. -/
theorem eventMass_nonneg (v : ProbabilityVector ι) (A : Finset ι) : 0 ≤ v.eventMass A :=
  Finset.sum_nonneg fun a _ ↦ v.nonneg a

/-- Event masses are monotone in the event. -/
theorem eventMass_mono (v : ProbabilityVector ι) {A B : Finset ι} (h : A ⊆ B) :
    v.eventMass A ≤ v.eventMass B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun a _ _ ↦ v.nonneg a

/-- Every event has mass at most `1`. -/
theorem eventMass_le_one (v : ProbabilityVector ι) (A : Finset ι) : v.eventMass A ≤ 1 := by
  simpa using v.eventMass_mono (Finset.subset_univ A)

/-- **Pairwise disjoint events carry at most the total mass.**  This is the finite additivity
bound used whenever several disjoint families of sample points are counted separately.

Proof sketch: the sum of the masses of pairwise disjoint events is the mass of their union
(`Finset.sum_biUnion`), which is at most the mass of the whole space. -/
theorem sum_eventMass_le_one {J : Type*} [Fintype J] (v : ProbabilityVector ι) (A : J → Finset ι)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (A j) (A j')) :
    ∑ j, v.eventMass (A j) ≤ 1 := by
  classical
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset J)) A :=
    fun j _ j' _ hne ↦ hdisj j j' hne
  have hsum : ∑ j, v.eventMass (A j) = v.eventMass (Finset.univ.biUnion A) := by
    rw [eventMass, Finset.sum_biUnion hpair]
    rfl
  rw [hsum]
  exact v.eventMass_le_one _

end ProbabilityVector

end AlgebraicComplexity
