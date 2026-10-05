/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingPower

/-!
# Segmented split restrictions

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `RestrictedSplittingPower.lean:108` fixes
**one** empirical type per leg for the whole word.  `[DuanWuZhou2022]`'s `hole_lemma.tex:40` instead
fixes a type **per component**: an available small `Z`-block is one for which, *for each `t`
separately*, the empirical distribution over segment `t` equals `alphatilde_t`.  A single pooled
type is strictly weaker, and `sum_segmentMultiplicity` below is exactly why:

`sum over t of (segment-t multiplicity) = (pooled multiplicity)`,

so pinning the pooled type pins only the *sum* of the segment types.  The committed engine can
therefore express `[DuanWuZhou2022]`'s standard-form tensor at `m = 1` and not at `m = 15`.

This module is the segmented analogue, laid down **beside** `RestrictedSplittingPower.lean`, which
is milestone machinery and is not edited here.  A repoint is proposed to its owners in the report.

## Conservativity

`segmentedKeeps_one_iff` proves that at `m = 1` the segmented keep predicate *is* the committed
`SplitRestriction.Keeps`.  So nothing downstream of the engine changes meaning; the generalisation
only adds reach.

## Design note: the segmentation is a labelling, not a partition

`seg : Fin (n + 1) -> Fin m` rather than `segment : Fin m -> Finset (Fin (n + 1))`.  A labelling is
automatically a partition, needs no disjointness or covering side conditions, and makes
`segmentMultiplicity` a single `Finset.filter` on a conjunction rather than a filter of a filter.
The fibres `{i // seg i = t}` are what the shuffling group acts on.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## Segmented multiplicities -/

section SegmentMultiplicity

variable {I : Type w} [DecidableEq I] {n m : ℕ}

/-- **The empirical type of the sub-word on one segment.**  `[DuanWuZhou2022]`'s
`alphatilde_t`. -/
def segmentMultiplicity (seg : Fin n → Fin m) (word : Fin n → I) (t : Fin m) : I → ℕ :=
  fun a ↦ (Finset.univ.filter fun i ↦ seg i = t ∧ word i = a).card

/-- **The pooled type is the sum of the segment types.**

This is the precise sense in which the committed single-type `SplitRestriction` is weaker than the
segmented one: it constrains this sum and nothing more, so it cannot separate a word that is
`alphatilde_t`-typical on every segment from one that is merely typical on average. -/
theorem sum_segmentMultiplicity (seg : Fin n → Fin m) (word : Fin n → I) (a : I) :
    ∑ t : Fin m, segmentMultiplicity seg word t a =
      (Finset.univ.filter fun i ↦ word i = a).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := seg) (t := (Finset.univ : Finset (Fin m))) fun i _ ↦ Finset.mem_univ (seg i)]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  unfold segmentMultiplicity
  congr 1
  ext i
  simp [Finset.mem_filter, and_comm]

/-- At one segment the segmented multiplicity is the pooled one. -/
theorem segmentMultiplicity_one (word : Fin n → I) :
    segmentMultiplicity (fun _ ↦ (0 : Fin 1)) word 0 = WordType.multiplicity word := by
  funext a
  unfold segmentMultiplicity WordType.multiplicity
  congr 1
  ext i
  simp

end SegmentMultiplicity

/-! ## Segmented split restrictions -/

section Segmented

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w}

/-- **A segmented split restriction**: for every leg and every segment, either no constraint or a
prescribed empirical type for that segment's sub-word.  `[DuanWuZhou2022]`'s
`(alphatilde_1, ..., alphatilde_m)` on the restricted leg. -/
abbrev SegmentedSplitRestriction (A : Leg → Type w) (m : ℕ) := ∀ c, Fin m → Option (A c → ℕ)

namespace SegmentedSplitRestriction

/-- The segmented restriction constraining only the leg `c₀`, by the per-segment types `α`. -/
def ofLeg {m : ℕ} (c₀ : Leg) (α : Fin m → A c₀ → ℕ) : SegmentedSplitRestriction A m :=
  fun c ↦ if h : c₀ = c then fun t ↦ some (h ▸ α t) else fun _ ↦ none

@[simp] theorem ofLeg_self {m : ℕ} (c₀ : Leg) (α : Fin m → A c₀ → ℕ) (t : Fin m) :
    ofLeg (A := A) c₀ α c₀ t = some (α t) := by
  simp [ofLeg]

theorem ofLeg_of_ne {m : ℕ} {c₀ c : Leg} (α : Fin m → A c₀ → ℕ) (h : c₀ ≠ c) (t : Fin m) :
    ofLeg (A := A) c₀ α c t = none := by
  simp [ofLeg, h]

variable [∀ c, DecidableEq (A c)]

/-- **The segmented keep predicate.**  A block word on leg `c` survives when, for every segment,
that segment is unconstrained or the sub-word on it has exactly the prescribed empirical type.
This is `hole_lemma.tex:40`'s per-component condition. -/
def Keeps {m : ℕ} (profile : SegmentedSplitRestriction A m) (n : ℕ)
    (seg : Fin (n + 1) → Fin m) : ∀ c, PositiveWord (A c) n → Prop :=
  fun c word ↦ ∀ t : Fin m,
    match profile c t with
    | none => True
    | some α => segmentMultiplicity seg (positiveWordEquiv (A c) n word) t = α

theorem keeps_of_all_none {m : ℕ} {profile : SegmentedSplitRestriction A m} {n : ℕ}
    {seg : Fin (n + 1) → Fin m} {c : Leg} (h : ∀ t, profile c t = none)
    (word : PositiveWord (A c) n) : profile.Keeps n seg c word := by
  intro t
  rw [h t]
  trivial

theorem keeps_iff_of_some {m : ℕ} {profile : SegmentedSplitRestriction A m} {n : ℕ}
    {seg : Fin (n + 1) → Fin m} {c : Leg} {α : Fin m → A c → ℕ}
    (h : ∀ t, profile c t = some (α t)) (word : PositiveWord (A c) n) :
    profile.Keeps n seg c word ↔
      ∀ t, segmentMultiplicity seg (positiveWordEquiv (A c) n word) t = α t := by
  constructor
  · intro hkeep t
    have hk := hkeep t
    rw [h t] at hk
    exact hk
  · intro hall t
    rw [h t]
    exact hall t

/-- Decidability, noncomputable exactly as `SplitRestriction.decidableKeeps` is. -/
noncomputable instance decidableKeeps {m : ℕ} (profile : SegmentedSplitRestriction A m) (n : ℕ)
    (seg : Fin (n + 1) → Fin m) (c : Leg) (word : PositiveWord (A c) n) :
    Decidable (profile.Keeps n seg c word) := by
  classical
  exact Classical.dec _

end SegmentedSplitRestriction

/-- **The committed engine is the case `m = 1`.**  With one segment the segmented keep predicate is
the committed `SplitRestriction.Keeps`, so `[DuanWuZhou2022]`'s standard-form tensor at `m = 1` is
already expressed by the existing machinery and this module changes nothing about it.  Stated at
`ofLeg`, which is the only form a client uses. -/
theorem segmentedKeeps_ofLeg_one_iff [∀ c, DecidableEq (A c)]
    (c₀ : Leg) (α : A c₀ → ℕ) (n : ℕ) (word : PositiveWord (A c₀) n) :
    SegmentedSplitRestriction.Keeps
        (SegmentedSplitRestriction.ofLeg (A := A) c₀ (fun _ : Fin 1 ↦ α)) n
        (fun _ ↦ (0 : Fin 1)) c₀ word ↔
      SplitRestriction.Keeps (SplitRestriction.ofLeg (A := A) c₀ α) n c₀ word := by
  rw [SegmentedSplitRestriction.keeps_iff_of_some
      (α := fun _ : Fin 1 ↦ α) (fun t ↦ SegmentedSplitRestriction.ofLeg_self c₀ _ t) word,
    SplitRestriction.keeps_some_iff (SplitRestriction.ofLeg_self (A := A) c₀ α) word]
  constructor
  · intro h
    rw [← segmentMultiplicity_one (positiveWordEquiv (A c₀) n word)]
    exact h 0
  · intro h t
    have ht : t = 0 := Subsingleton.elim t 0
    subst ht
    rw [segmentMultiplicity_one]
    exact h

/-! ## The segmented restricted-splitting power -/

variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The segmented restricted-splitting power.**  The `(n+1)`-fold partitioned power with every
address zeroed out whose word fails, on some restricted leg and some segment, to have the
prescribed empirical type on that segment. -/
noncomputable def Tensor.PartitionedTensor.segmentedRestrictedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m) :
    PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n)
      (PositivePowerBlockSpace K V n) :=
  (P.positivePower n).select (profile.Keeps n seg)

@[simp] theorem Tensor.PartitionedTensor.mem_segmentedRestrictedSplittingPower_support
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    address ∈ (P.segmentedRestrictedSplittingPower n m seg profile).support ↔
      address ∈ (P.positivePower n).support ∧ ∀ c, profile.Keeps n seg c (address c) :=
  PartitionedTensor.mem_select_support _ _ _

/-- The segmented power is a selection, so its constituents are unchanged. -/
@[simp] theorem Tensor.PartitionedTensor.segmentedRestrictedSplittingPower_constituent
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m) :
    (P.segmentedRestrictedSplittingPower n m seg profile).constituent =
      (P.positivePower n).constituent := rfl

/-- **The segmented cut is a zero-out, hence an exact restriction.** -/
theorem Tensor.Restricts.partitionedPositivePower_segmentedRestrictedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m) :
    Restricts (P.positivePower n).realize
      (P.segmentedRestrictedSplittingPower n m seg profile).realize :=
  Tensor.Restricts.partitionedSelect (P.positivePower n) (profile.Keeps n seg)

end Segmented

end AlgebraicComplexity
