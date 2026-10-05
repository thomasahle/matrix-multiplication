/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradEasy
import AlgebraicComplexity.Examples.CoppersmithWinogradHashEncoding
import AlgebraicComplexity.Combinatorics.BalancedMultinomial
import AlgebraicComplexity.Combinatorics.ProgressionFree
import AlgebraicComplexity.Analysis.Log
import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerSelection
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeExtraction
import Mathlib.NumberTheory.Bertrand

/-!
# Equal-type hashing for the easy Coppersmith--Winograd tensor

This file is the combinatorial extraction client for the three-constituent tensor from Section
4.1 of He and Williams's CS 6810 notes.  The base tensor and border-rank certificate stay in
`CoppersmithWinogradEasy`; this downstream module supplies the field encoding, equal-multiplicity
word family, type-selection zero-out, and affine-hashing targets.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-- The easy CW support is a legal constant-sum support over every field of odd characteristic.

It uses the same block encoding and target weight `2` as the full six-address encoding
`cwPartitionHashEncoding`, so legality is inherited: the easy support is a subset of the full
CW support, and constant-sum legality is a pointwise condition on addresses. -/
def easyPartitionHashEncoding {R : Type*} [Field R] [NeZero (2 : R)] :
    PartitionHashEncoding (R := R) easyBlockSupport where
  encode _ := cwBlockFieldValue
  target := 2
  support_nonempty := ⟨cw011, by decide⟩
  encode_injective _ := cwBlockFieldValue_injective
  legal s hs :=
    (cwPartitionHashEncoding (R := R)).legal s
      (easyBlockSupport_subset_cwBlockSupport hs)

/-- Equal multiplicity `k` for each of the three easy constituents. -/
def easyEqualType (k : ℕ) : easyBlockSupport → ℕ := fun _ ↦ k

/-- `3k-1` is the positive-word depth representing a tensor power with `3k` factors. -/
def easyEqualTypeDepth (k : ℕ) : ℕ := 3 * k - 1

/-- Positive equal-type depth really represents `3k` tensor factors. -/
theorem easyEqualTypeDepth_add_one {k : ℕ} (hk : 0 < k) :
    easyEqualTypeDepth k + 1 = 3 * k := by
  unfold easyEqualTypeDepth
  omega

/-- The equal three-way multiplicity vector has the required total size. -/
theorem easyEqualType_mem_types {k : ℕ} (hk : 0 < k) :
    easyEqualType k ∈ WordType.types easyBlockSupport (easyEqualTypeDepth k + 1) := by
  rw [WordType.mem_types]
  simp only [easyEqualType, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    card_easyBlockSupport, nsmul_eq_mul]
  unfold easyEqualTypeDepth
  omega

/-- Equal-type supported-address words in the `3k`-fold easy tensor power. -/
noncomputable def easyEqualTypeWords (k : ℕ) :
    Finset (PositiveWord easyBlockSupport (easyEqualTypeDepth k)) :=
  positiveTypeClass easyBlockSupport (easyEqualTypeDepth k) (easyEqualType k)

/-- Exact multinomial size of the equal-type word family. -/
theorem card_easyEqualTypeWords {k : ℕ} (hk : 0 < k) :
    (easyEqualTypeWords k).card = Nat.multinomial Finset.univ (easyEqualType k) := by
  exact card_positiveTypeClass_eq_multinomial _ _ (easyEqualType_mem_types hk)

/-- The equal easy-CW word family is the canonical balanced three-letter multinomial class. -/
theorem card_easyEqualTypeWords_eq_balancedMultinomial {k : ℕ} (hk : 0 < k) :
    (easyEqualTypeWords k).card = WordType.balancedMultinomial 3 k := by
  rw [card_easyEqualTypeWords hk]
  exact WordType.multinomial_const_eq_balanced 3 k (by simp)

/-- Explicit polynomial-loss form of the `27^k` equal-type word growth. -/
theorem easyEqualTypeWords_exponential_lower {k : ℕ} (hk : 0 < k) :
    2 * 27 ^ k ≤ 9 * k ^ 2 * (easyEqualTypeWords k).card := by
  rw [card_easyEqualTypeWords_eq_balancedMultinomial hk]
  exact WordType.two_mul_twentySeven_pow_le_nine_mul_sq_mul_balancedMultinomial_three k hk

/-- First matrix-multiplication dimension of an easy constituent. -/
abbrev easyConstituentM (q : ℕ) (s : easyBlockSupport) : ℕ :=
  (cwConstituentDimensions q s.1).1

/-- Second matrix-multiplication dimension of an easy constituent. -/
abbrev easyConstituentN (q : ℕ) (s : easyBlockSupport) : ℕ :=
  (cwConstituentDimensions q s.1).2.1

/-- Third matrix-multiplication dimension of an easy constituent. -/
abbrev easyConstituentP (q : ℕ) (s : easyBlockSupport) : ℕ :=
  (cwConstituentDimensions q s.1).2.2

/-- In an equal-type word, the first rectangular dimension multiplies to `q^k`. -/
theorem easyEqualType_positiveWordProduct_m (q k : ℕ)
    (word : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hword : word ∈ easyEqualTypeWords k) :
    positiveWordProduct (easyConstituentM q) (easyEqualTypeDepth k) word = q ^ k := by
  rw [positiveWordProduct_eq_prod_pow (a := easyEqualType k)
    (easyConstituentM q) hword]
  change (∏ s : easyBlockSupport,
    (cwConstituentDimensions q s.1).1 ^ k) = q ^ k
  classical
  calc
    (∏ s : easyBlockSupport, (cwConstituentDimensions q s.1).1 ^ k) =
        ∏ s ∈ easyBlockSupport, (cwConstituentDimensions q s).1 ^ k :=
      (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).1 ^ k)).symm
    _ = q ^ k := by
      rw [prod_easyBlockSupport]
      simp [cwConstituentDimensions]

/-- In an equal-type word, the second rectangular dimension multiplies to `q^k`. -/
theorem easyEqualType_positiveWordProduct_n (q k : ℕ)
    (word : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hword : word ∈ easyEqualTypeWords k) :
    positiveWordProduct (easyConstituentN q) (easyEqualTypeDepth k) word = q ^ k := by
  rw [positiveWordProduct_eq_prod_pow (a := easyEqualType k)
    (easyConstituentN q) hword]
  change (∏ s : easyBlockSupport,
    (cwConstituentDimensions q s.1).2.1 ^ k) = q ^ k
  classical
  calc
    (∏ s : easyBlockSupport, (cwConstituentDimensions q s.1).2.1 ^ k) =
        ∏ s ∈ easyBlockSupport, (cwConstituentDimensions q s).2.1 ^ k :=
      (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.1 ^ k)).symm
    _ = q ^ k := by
      rw [prod_easyBlockSupport]
      simp [cwConstituentDimensions]

/-- In an equal-type word, the third rectangular dimension multiplies to `q^k`. -/
theorem easyEqualType_positiveWordProduct_p (q k : ℕ)
    (word : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hword : word ∈ easyEqualTypeWords k) :
    positiveWordProduct (easyConstituentP q) (easyEqualTypeDepth k) word = q ^ k := by
  rw [positiveWordProduct_eq_prod_pow (a := easyEqualType k)
    (easyConstituentP q) hword]
  change (∏ s : easyBlockSupport,
    (cwConstituentDimensions q s.1).2.2 ^ k) = q ^ k
  classical
  calc
    (∏ s : easyBlockSupport, (cwConstituentDimensions q s.1).2.2 ^ k) =
        ∏ s ∈ easyBlockSupport, (cwConstituentDimensions q s).2.2 ^ k :=
      (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.2 ^ k)).symm
    _ = q ^ k := by
      rw [prod_easyBlockSupport]
      simp [cwConstituentDimensions]

/-- Legal affine-hashing targets representing the equal-type easy CW words. -/
noncomputable def easyEqualTypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (k : ℕ) :
    Finset (ProgressionHash.LegalTriple R (Fin (easyEqualTypeDepth k + 1)) 2) :=
  (easyPartitionHashEncoding (R := R)).legalTargets
    (easyEqualTypeDepth k) (easyEqualTypeWords k)

@[simp] theorem card_easyEqualTypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (k : ℕ) :
    (easyEqualTypeTargets (R := R) k).card = (easyEqualTypeWords k).card := by
  exact PartitionHashEncoding.card_legalTargets _ _ _

/-- The supported address whose zero block occurs on a specified leg. -/
def easyZeroAddress : Leg → easyBlockSupport
  | .X => ⟨cw011, by decide⟩
  | .Y => ⟨cw101, by decide⟩
  | .Z => ⟨cw110, by decide⟩

/-- Within the easy support, a zero label on `c` identifies `easyZeroAddress c`. -/
theorem easyAddress_leg_eq_zero_iff (s : easyBlockSupport) (c : Leg) :
    s.1 c = .zero ↔ s = easyZeroAddress c := by
  cases c <;> decide +revert

/-- No address in the easy support uses the final CW block. -/
theorem easyAddress_leg_ne_last (s : easyBlockSupport) (c : Leg) : s.1 c ≠ .last := by
  intro h
  rcases s with ⟨s, hs⟩
  simp only [easyBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;>
    cases c <;> simp [cw011, cw101, cw110, cwBlockAddress] at h

/-- On a fixed leg, every easy address other than the unique zero address carries the middle
block. -/
theorem easyAddress_leg_eq_middle_iff (s : easyBlockSupport) (c : Leg) :
    s.1 c = .middle ↔ s ≠ easyZeroAddress c := by
  constructor
  · intro hm heq
    subst s
    cases c <;>
      simp [easyZeroAddress, cw011, cw101, cw110, cwBlockAddress] at hm
  · intro hne
    cases hb : s.1 c with
    | zero => exact (hne ((easyAddress_leg_eq_zero_iff s c).mp hb)).elim
    | middle => rfl
    | last => exact (easyAddress_leg_ne_last s c hb).elim

theorem easyLegLetterFiber_zero (c : Leg) :
    WordType.letterFiber (fun s : easyBlockSupport ↦ s.1 c) .zero =
      {easyZeroAddress c} := by
  classical
  ext s
  simp [easyAddress_leg_eq_zero_iff]

theorem easyLegLetterFiber_middle (c : Leg) :
    WordType.letterFiber (fun s : easyBlockSupport ↦ s.1 c) .middle =
      (Finset.univ.erase (easyZeroAddress c) : Finset easyBlockSupport) := by
  classical
  ext s
  simp [easyAddress_leg_eq_middle_iff]

theorem easyLegLetterFiber_last (c : Leg) :
    WordType.letterFiber (fun s : easyBlockSupport ↦ s.1 c) .last = ∅ := by
  classical
  ext s
  simp [easyAddress_leg_ne_last]

/-- On any leg, the projection from the three easy support addresses has fiber sizes `1,2,0`
over the zero, middle, and final CW blocks respectively. -/
theorem card_easyLegLetterFiber (c : Leg) (b : CWBlock) :
    (WordType.letterFiber (fun s : easyBlockSupport ↦ s.1 c) b).card =
      match b with
      | .zero => 1
      | .middle => 2
      | .last => 0 := by
  classical
  cases b with
  | zero => simp [easyLegLetterFiber_zero]
  | middle =>
      rw [easyLegLetterFiber_middle,
        Finset.card_erase_of_mem (Finset.mem_univ (easyZeroAddress c))]
      simp
  | last => simp [easyLegLetterFiber_last]

/-- A leg projection of an equal-type source word contains `k` zero labels and `2k` middle
labels (and no final labels). -/
theorem easyLegProjection_multiplicity (k : ℕ)
    (q : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hq : q ∈ easyEqualTypeWords k) (c : Leg) (b : CWBlock) :
    WordType.multiplicity
        (fun i ↦
          (positiveWordEquiv easyBlockSupport (easyEqualTypeDepth k) q i).1 c) b =
      match b with
      | .zero => k
      | .middle => 2 * k
      | .last => 0 := by
  change WordType.multiplicity
    ((fun s : easyBlockSupport ↦ s.1 c) ∘
      positiveWordEquiv easyBlockSupport (easyEqualTypeDepth k) q) b = _
  rw [WordType.multiplicity_comp_eq_sum_letterFiber]
  have htype := mem_positiveTypeClass.mp hq
  simp_rw [htype]
  cases b <;> simp [easyEqualType, card_easyLegLetterFiber]

/-- There are at most—and in the ambient unrestricted word fiber exactly—`4^k` source words
above a fixed leg word of an equal-type easy-CW source word. -/
theorem card_easyLegWordMapFiber (k : ℕ)
    (q : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hq : q ∈ easyEqualTypeWords k) (c : Leg) :
    (WordType.wordMapFiber (fun s : easyBlockSupport ↦ s.1 c)
      (positiveWordEquiv CWBlock (easyEqualTypeDepth k)
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport)
          (easyEqualTypeDepth k) q c))).card = 4 ^ k := by
  rw [WordType.card_wordMapFiber]
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport)
    (easyEqualTypeDepth k) q c]
  rw [WordType.prod_word_eq_prod_pow
    (x := fun b : CWBlock ↦
      (WordType.letterFiber (fun s : easyBlockSupport ↦ s.1 c) b).card)
    (word := fun i ↦
      (positiveWordEquiv easyBlockSupport (easyEqualTypeDepth k) q i).1 c)]
  rw [show (Finset.univ : Finset CWBlock) = {.zero, .middle, .last} by decide]
  simp [card_easyLegLetterFiber, easyLegProjection_multiplicity k q hq c, pow_mul]

/-- Every fixed-leg fiber of equal-type easy-CW hashing targets has at most `4^k` elements. -/
theorem card_easyEqualTypeTarget_legFiber_le
    {R : Type*} [Field R] [NeZero (2 : R)] (k : ℕ)
    {triple : ProgressionHash.LegalTriple R (Fin (easyEqualTypeDepth k + 1)) 2}
    (htriple : triple ∈ easyEqualTypeTargets (R := R) k) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (easyEqualTypeTargets (R := R) k) triple c).card ≤ 4 ^ k := by
  classical
  change triple ∈ (easyEqualTypeWords k).image
    ((easyPartitionHashEncoding (R := R)).legalTriple (easyEqualTypeDepth k)) at htriple
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp htriple
  have hlegal : (easyPartitionHashEncoding (R := R)).legalTriple
      (easyEqualTypeDepth k) q ∈ easyEqualTypeTargets (R := R) k := by
    unfold easyEqualTypeTargets PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  apply ((easyPartitionHashEncoding (R := R)).card_legFiber_legalTargets_le_card_wordMapFiber
    (easyEqualTypeDepth k) (easyEqualTypeWords k) hlegal c).trans_eq
  simpa using card_easyLegWordMapFiber k q hq c

/-- The all-leg competitor list for an equal-type easy-CW target has size at most `3·4^k`. -/
theorem card_easyEqualTypeTarget_legwiseCompetitors_le
    {R : Type*} [Field R] [NeZero (2 : R)] (k : ℕ)
    {triple : ProgressionHash.LegalTriple R (Fin (easyEqualTypeDepth k + 1)) 2}
    (htriple : triple ∈ easyEqualTypeTargets (R := R) k) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (easyEqualTypeTargets (R := R) k) triple).card ≤ 3 * 4 ^ k := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  intro c
  exact card_easyEqualTypeTarget_legFiber_le k htriple c

/-- A hashing field of size at least `12·4^k` automatically satisfies the exact quarter-degree
condition used by the one-pass all-leg isolation theorem. -/
theorem easyEqualType_competitorQuarter_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)] (k : ℕ)
    (hcard : 12 * 4 ^ k ≤ Fintype.card R) :
    ∀ triple ∈ easyEqualTypeTargets (R := R) k,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyEqualTypeTargets (R := R) k) triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyEqualTypeTargets (R := R) k) triple).card ≤ 4 * (3 * 4 ^ k) :=
      Nat.mul_le_mul_left 4
        (card_easyEqualTypeTarget_legwiseCompetitors_le k htriple)
    _ = 12 * 4 ^ k := by ring
    _ ≤ Fintype.card R := hcard

/-- Convert the exact hashing count and balanced-multinomial estimate into the clean finite copy
lower bound used by the asymptotic calculation. -/
theorem easyCopies_lower_of_hashingCount {k M copies : ℕ} {B : Type*} [Fintype B]
    (hk : 0 < k)
    (hcount : 3 * (easyEqualTypeWords k).card * Fintype.card B ≤
      4 * (M * M) * copies) :
    27 ^ k * Fintype.card B ≤ 6 * k ^ 2 * (M * M) * copies := by
  have hwords := easyEqualTypeWords_exponential_lower hk
  have hscaledWords := Nat.mul_le_mul_left (3 * Fintype.card B) hwords
  have hscaledCount := Nat.mul_le_mul_left (9 * k ^ 2) hcount
  apply Nat.le_of_mul_le_mul_left (c := 6) ?_ (by norm_num)
  calc
    6 * (27 ^ k * Fintype.card B) =
        (3 * Fintype.card B) * (2 * 27 ^ k) := by ring
    _ ≤ (3 * Fintype.card B) *
        (9 * k ^ 2 * (easyEqualTypeWords k).card) := hscaledWords
    _ = (9 * k ^ 2) *
        (3 * (easyEqualTypeWords k).card * Fintype.card B) := by ring
    _ ≤ (9 * k ^ 2) * (4 * (M * M) * copies) := hscaledCount
    _ = 6 * (6 * k ^ 2 * (M * M) * copies) := by ring

/-- Multiplicity of the source address distinguished by a leg equals the zero-label multiplicity
of that transposed leg word. -/
theorem easySourceMultiplicity_eq_legZero (k : ℕ)
    (q : PositiveWord easyBlockSupport (easyEqualTypeDepth k)) (c : Leg) :
    WordType.multiplicity
        (positiveWordEquiv easyBlockSupport (easyEqualTypeDepth k) q)
        (easyZeroAddress c) =
      WordType.multiplicity
        (positiveWordEquiv CWBlock (easyEqualTypeDepth k)
          (PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport)
            (easyEqualTypeDepth k) q c)) .zero := by
  classical
  unfold WordType.multiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hword := congrFun
    (PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport)
      (easyEqualTypeDepth k) q c) i
  rw [hword]
  exact (easyAddress_leg_eq_zero_iff _ c).symm

/-- Keep block words having exactly `k` zero labels. -/
noncomputable def easyEqualTypeKeepBlock (k : ℕ) (_c : Leg)
    (word : PositiveWord CWBlock (easyEqualTypeDepth k)) : Prop :=
  WordType.multiplicity
    (positiveWordEquiv CWBlock (easyEqualTypeDepth k) word) .zero = k

noncomputable instance easyEqualTypeKeepBlock_decidable (k : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (easyEqualTypeDepth k)) :
    Decidable (easyEqualTypeKeepBlock k c word) := by
  classical
  unfold easyEqualTypeKeepBlock
  infer_instance

/-- Equal joint multiplicity is exactly the conjunction of the three leg-local zero counts. -/
theorem mem_easyEqualTypeWords_iff_keepBlocks (k : ℕ)
    (q : PositiveWord easyBlockSupport (easyEqualTypeDepth k)) :
    q ∈ easyEqualTypeWords k ↔
      ∀ c, easyEqualTypeKeepBlock k c
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport)
          (easyEqualTypeDepth k) q c) := by
  rw [easyEqualTypeWords, mem_positiveTypeClass]
  constructor
  · intro htype c
    unfold easyEqualTypeKeepBlock
    rw [← easySourceMultiplicity_eq_legZero k q c, htype]
    rfl
  · intro hkeep
    funext s
    have hs : s = easyZeroAddress .X ∨ s = easyZeroAddress .Y ∨
        s = easyZeroAddress .Z := by
      decide +revert
    rcases hs with rfl | rfl | rfl
    · rw [easySourceMultiplicity_eq_legZero k q .X]
      exact hkeep .X
    · rw [easySourceMultiplicity_eq_legZero k q .Y]
      exact hkeep .Y
    · rw [easySourceMultiplicity_eq_legZero k q .Z]
      exact hkeep .Z

section TensorPower

variable (K : Type u) [CommRing K]
variable (q k : ℕ)

/-- First constituent dimension, indexed by the support type carried by the easy partitioned
tensor.  The explicit wrapper prevents elaboration from repeatedly unfolding support subtypes in
dependent word products. -/
abbrev easyTensorConstituentM
    (s : (easyPartitionedTensor K q).support) : ℕ :=
  (cwConstituentDimensions q s.1).1

/-- Second constituent dimension on the easy partitioned tensor's support type. -/
abbrev easyTensorConstituentN
    (s : (easyPartitionedTensor K q).support) : ℕ :=
  (cwConstituentDimensions q s.1).2.1

/-- Third constituent dimension on the easy partitioned tensor's support type. -/
abbrev easyTensorConstituentP
    (s : (easyPartitionedTensor K q).support) : ℕ :=
  (cwConstituentDimensions q s.1).2.2

/-- Typed-support version of the equal-word product formula on the first leg. -/
theorem easyTensorEqualType_positiveWordProduct_m
    (word : PositiveWord (easyPartitionedTensor K q).support (easyEqualTypeDepth k))
    (hword : word ∈ positiveTypeClass (easyPartitionedTensor K q).support
      (easyEqualTypeDepth k) (fun _ ↦ k)) :
    positiveWordProduct (easyTensorConstituentM K q)
      (easyEqualTypeDepth k) word = q ^ k := by
  change PositiveWord easyBlockSupport (easyEqualTypeDepth k) at word
  change word ∈ easyEqualTypeWords k at hword
  exact easyEqualType_positiveWordProduct_m q k word hword

/-- Typed-support version of the equal-word product formula on the second leg. -/
theorem easyTensorEqualType_positiveWordProduct_n
    (word : PositiveWord (easyPartitionedTensor K q).support (easyEqualTypeDepth k))
    (hword : word ∈ positiveTypeClass (easyPartitionedTensor K q).support
      (easyEqualTypeDepth k) (fun _ ↦ k)) :
    positiveWordProduct (easyTensorConstituentN K q)
      (easyEqualTypeDepth k) word = q ^ k := by
  change PositiveWord easyBlockSupport (easyEqualTypeDepth k) at word
  change word ∈ easyEqualTypeWords k at hword
  exact easyEqualType_positiveWordProduct_n q k word hword

/-- Typed-support version of the equal-word product formula on the third leg. -/
theorem easyTensorEqualType_positiveWordProduct_p
    (word : PositiveWord (easyPartitionedTensor K q).support (easyEqualTypeDepth k))
    (hword : word ∈ positiveTypeClass (easyPartitionedTensor K q).support
      (easyEqualTypeDepth k) (fun _ ↦ k)) :
    positiveWordProduct (easyTensorConstituentP K q)
      (easyEqualTypeDepth k) word = q ^ k := by
  change PositiveWord easyBlockSupport (easyEqualTypeDepth k) at word
  change word ∈ easyEqualTypeWords k at hword
  exact easyEqualType_positiveWordProduct_p q k word hword

/-- The equal-type subpartition of the `3k`-fold easy tensor power. -/
noncomputable def easyEqualTypePartitionedPower :
    PartitionedTensor (K := K)
      (A := fun _ ↦ PositiveWord CWBlock (easyEqualTypeDepth k))
      (PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
        (easyEqualTypeDepth k)) :=
  ((easyPartitionedTensor K q).positivePower (easyEqualTypeDepth k)).select
    (easyEqualTypeKeepBlock k)

/-- The selected partition support is exactly the modeled equal-type legal-target family. -/
theorem easyEqualTypePartitionedPower_support
    {R : Type*} [Field R] [NeZero (2 : R)] :
    (easyEqualTypePartitionedPower K q k).support =
      (easyPartitionHashEncoding (R := R)).modeledAddresses
        (easyEqualTypeDepth k) (easyEqualTypeTargets (R := R) k) := by
  classical
  unfold easyEqualTypePartitionedPower easyEqualTypeTargets
  exact PartitionHashEncoding.select_positivePower_support
    (easyPartitionedTensor K q) (easyPartitionHashEncoding (R := R))
    (easyEqualTypeDepth k) (easyEqualTypeKeepBlock k) (easyEqualTypeWords k)
    (mem_easyEqualTypeWords_iff_keepBlocks k)

/-- Every constituent retained by equal-type selection restricts to the same square
matrix-multiplication tensor `⟨q^k,q^k,q^k⟩`.  This is the algebraic content of the easy
laser construction before independent copies are counted by hashing. -/
theorem easyEqualTypePartitionedPower_constituent_restricts_square
    (s : (easyEqualTypePartitionedPower K q k).support) :
    Restricts ((easyEqualTypePartitionedPower K q k).constituent s.1)
      (matrixMultiplication (K := K) (q ^ k) (q ^ k) (q ^ k)) := by
  refine Tensor.Restricts.select_positivePower_constituent
    (easyPartitionedTensor K q) (easyEqualTypeDepth k) (easyEqualTypeKeepBlock k)
    (easyEqualTypeWords k) (mem_easyEqualTypeWords_iff_keepBlocks k) ?_ s
  intro word hword
  have hwordTensor : word ∈ positiveTypeClass
      (easyPartitionedTensor K q).support (easyEqualTypeDepth k) (fun _ ↦ k) := hword
  have hrestrict := Tensor.Restricts.positiveSupportWordTensor_matrixMultiplication
    (easyPartitionedTensor K q)
    (easyTensorConstituentM K q) (easyTensorConstituentN K q)
    (easyTensorConstituentP K q)
    (easySupportedConstituent_restricts K q)
    (easyEqualTypeDepth k) word
  rwa [easyTensorEqualType_positiveWordProduct_m K q k word hwordTensor,
    easyTensorEqualType_positiveWordProduct_n K q k word hwordTensor,
    easyTensorEqualType_positiveWordProduct_p K q k word hwordTensor] at hrestrict

/-- Canonical `3k`-fold tensor power restricts to the equal-type partition before hashing. -/
theorem easyPower_restricts_equalTypePartitionedPower :
    Restricts
      (Tensor.power (easyPartitionedTensor K q).realize (easyEqualTypeDepth k + 1))
      (easyEqualTypePartitionedPower K q k).realize := by
  exact (Tensor.Restricts.power_partitionedPositivePower
      (easyPartitionedTensor K q) (easyEqualTypeDepth k)).trans
    (Tensor.Restricts.partitionedSelect
      ((easyPartitionedTensor K q).positivePower (easyEqualTypeDepth k))
      (easyEqualTypeKeepBlock k))

/-- For a fixed hash seed, the equal-type easy tensor power restricts to a genuine indexed direct
sum whose addresses are isolated on all three legs. -/
theorem easyPower_restricts_legwiseIsolatedIndexedDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1))) :
    Restricts
      (Tensor.power (easyPartitionedTensor K q).realize (easyEqualTypeDepth k + 1))
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (easyEqualTypeDepth k))
          ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed))
        (fun s : (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed ↦
          (easyEqualTypePartitionedPower K q k).constituent s.1)) := by
  apply (easyPower_restricts_equalTypePartitionedPower K q k).trans
  apply Tensor.Restricts.modeledTargets_to_legwiseIsolatedIndexedDirectSum
    (easyPartitionHashEncoding (R := R)) (easyEqualTypeWords k) B hB seed
      (easyEqualTypePartitionedPower K q k)
  exact easyEqualTypePartitionedPower_support K q k

/-- The legwise-isolated constituent sum restricts componentwise to identical square
matrix-multiplication tensors. -/
theorem easyLegwiseIsolatedIndexedDirectSum_restricts_squareDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1))) :
    Restricts
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (easyEqualTypeDepth k))
          ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed))
        (fun s : (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed ↦
          (easyEqualTypePartitionedPower K q k).constituent s.1))
      (matrixMultiplicationDirectSum
        (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed)
        K (fun _ ↦ q ^ k) (fun _ ↦ q ^ k) (fun _ ↦ q ^ k)) :=
  Tensor.Restricts.legwiseIsolatedIndexedDirectSum_const
    (easyPartitionHashEncoding (R := R)) (easyEqualTypeWords k) B seed
    (easyEqualTypePartitionedPower K q k)
    (easyEqualTypePartitionedPower_support (R := R) K q k)
    (easyEqualTypePartitionedPower_constituent_restricts_square K q k)

/-- A fixed successful hash seed therefore extracts independent copies of
`⟨q^k,q^k,q^k⟩` from the canonical `3k`-fold easy tensor power. -/
theorem easyPower_restricts_legwiseIsolatedSquareDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1))) :
    Restricts
      (Tensor.power (easyPartitionedTensor K q).realize (easyEqualTypeDepth k + 1))
      (matrixMultiplicationDirectSum
        (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed)
        K (fun _ ↦ q ^ k) (fun _ ↦ q ^ k) (fun _ ↦ q ^ k)) :=
  (easyPower_restricts_legwiseIsolatedIndexedDirectSum K q k B hB seed).trans
    (easyLegwiseIsolatedIndexedDirectSum_restricts_squareDirectSum K q k B seed)

/-- Finite equal-type extraction with the exact division-free hashing count. -/
theorem exists_easyPower_legwiseIsolatedExtraction
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ easyEqualTypeTargets (R := R) k,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyEqualTypeTargets (R := R) k) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1)),
      3 * (easyEqualTypeWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card ∧
        Restricts
          (Tensor.power (easyPartitionedTensor K q).realize (easyEqualTypeDepth k + 1))
          (indexedDirectSum
            (V := SelectedBlockFamily
              (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
                (easyEqualTypeDepth k))
              ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
                (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed))
            (fun s : (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
                (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed ↦
              (easyEqualTypePartitionedPower K q k).constituent s.1)) := by
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets
      (easyEqualTypeTargets (R := R) k) B hB hquarter
  refine ⟨seed, ?_, easyPower_restricts_legwiseIsolatedIndexedDirectSum K q k B hB seed⟩
  rw [(easyPartitionHashEncoding (R := R)).card_legwiseIsolatedPowerAddresses
    (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed]
  change 3 * ((easyPartitionHashEncoding (R := R)).legalTargets
      (easyEqualTypeDepth k) (easyEqualTypeWords k)).card * B.card ≤ _ at hcount
  rw [PartitionHashEncoding.card_legalTargets] at hcount
  exact hcount

/-- Finite easy-CW extraction in the exact form consumed by Schönhage's asymptotic sum
inequality: a large all-leg-independent family of identical square matrix-multiplication
tensors. -/
theorem exists_easyPower_squareExtraction
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ easyEqualTypeTargets (R := R) k,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyEqualTypeTargets (R := R) k) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1)),
      3 * (easyEqualTypeWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card ∧
        Restricts
          (Tensor.power (easyPartitionedTensor K q).realize
            (easyEqualTypeDepth k + 1))
          (matrixMultiplicationDirectSum
            (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed)
            K (fun _ ↦ q ^ k) (fun _ ↦ q ^ k) (fun _ ↦ q ^ k)) := by
  obtain ⟨seed, hcount, _hrestrict⟩ :=
    exists_easyPower_legwiseIsolatedExtraction K q k B hB hquarter
  exact ⟨seed, hcount,
    easyPower_restricts_legwiseIsolatedSquareDirectSum K q k B hB seed⟩

/-- Concrete finite easy-CW extraction with the abstract competitor hypothesis discharged by the
support-fiber count.  Only the explicit field-size and progression-free-set inputs remain. -/
theorem exists_easyPower_squareExtraction_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * 4 ^ k ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1)),
      3 * (easyEqualTypeWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card ∧
        Restricts
          (Tensor.power (easyPartitionedTensor K q).realize
            (easyEqualTypeDepth k + 1))
          (matrixMultiplicationDirectSum
            (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed)
            K (fun _ ↦ q ^ k) (fun _ ↦ q ^ k) (fun _ ↦ q ^ k)) :=
  exists_easyPower_squareExtraction K q k B hB
    (easyEqualType_competitorQuarter_of_fieldCard k hcard)

end TensorPower

section FiniteAsymptoticSum

variable (K : Type u) [Field K]
variable (q k : ℕ)

/-- The explicit non-exponential loss left by balanced type counting, prime-field hashing, and
the Behrend construction in the easy CW extraction. -/
noncomputable def easyCWSubexponentialLoss (k : ℕ) : ℝ :=
  432 * (k : ℝ) ^ 2 * Real.exp (16 * √((k + 1 : ℕ) : ℝ))

/-- The loss in the finite easy-CW extraction is genuinely subexponential. -/
theorem easyCWSubexponentialLoss_subexponential :
    Growth.Subexponential easyCWSubexponentialLoss := by
  change Growth.Subexponential
    (fun k : ℕ ↦ 432 * (k : ℝ) ^ 2 * Real.exp (16 * √((k + 1 : ℕ) : ℝ)))
  exact
    Growth.Subexponential.const_mul_natCast_pow_mul_exp_sqrt_succ
      (c := (432 : ℝ)) (a := (16 : ℝ)) (by positivity) (by positivity) 2

/-- Normalize the square constituent's volume term in the asymptotic sum inequality.  This is
the generic identity `cubeVolume_rpow_omega_div_three` at the easy-CW power schedule `n = k`. -/
theorem easyCubeVolume_rpow_omega_div_three (hq : 0 < q) :
    ((((q ^ k) * (q ^ k) * (q ^ k) : ℕ) : ℝ) ^ (omega K / 3)) =
      (((q : ℝ) ^ omega K) ^ k) :=
  cubeVolume_rpow_omega_div_three K q k hq

/-- The finite numerical inequality obtained by feeding the easy-CW square extraction directly
to the proved asymptotic sum inequality.  The two remaining classical asymptotic tasks are kept
visible in the hypotheses/data: bound the competitor lists uniformly and choose large
progression-free `B` in a suitable finite field. -/
theorem exists_easyPower_asymptoticSum_bound
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (hq : 0 < q)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ easyEqualTypeTargets (R := R) k,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyEqualTypeTargets (R := R) k) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1)),
      3 * (easyEqualTypeWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card ∧
        (((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card : ℝ) *
            (((q ^ k) * (q ^ k) * (q ^ k) : ℕ) : ℝ) ^ (omega K / 3) ≤
          (((q + 2) ^ (easyEqualTypeDepth k + 1) : ℕ) : ℝ) := by
  obtain ⟨seed, hcount, hrestrict⟩ :=
    exists_easyPower_squareExtraction K q k B hB hquarter
  refine ⟨seed, hcount, ?_⟩
  have hdeg := PolynomialDegenerates.of_restricts hrestrict
  have hasi := asymptoticSum_le_of_borderRankLE
    (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
      (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed)
    K (fun _ ↦ q ^ k) (fun _ ↦ q ^ k) (fun _ ↦ q ^ k)
    ((easyPartitionedTensor_borderRankLE K q).power (easyEqualTypeDepth k + 1))
    (fun _ ↦ pow_pos hq k) (fun _ ↦ pow_pos hq k) (fun _ ↦ pow_pos hq k)
    hdeg
  simpa only [asymptoticSum_const, Fintype.card_coe] using hasi

/-- The finite easy-CW/Schönhage inequality with competitor counting fully internalized. -/
theorem exists_easyPower_asymptoticSum_bound_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (hq : 0 < q)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * 4 ^ k ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1)),
      3 * (easyEqualTypeWords k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card ∧
        (((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card : ℝ) *
            (((q ^ k) * (q ^ k) * (q ^ k) : ℕ) : ℝ) ^ (omega K / 3) ≤
          (((q + 2) ^ (easyEqualTypeDepth k + 1) : ℕ) : ℝ) :=
  exists_easyPower_asymptoticSum_bound K q k hq B hB
    (easyEqualType_competitorQuarter_of_fieldCard k hcard)

/-- Fully instantiated finite easy-CW extraction over a prime cyclic field.  The progression-free
set is the canonical half-interval Behrend witness; the output is reduced to its numeric copy count
so the theorem no longer exposes a chosen hash seed or block-address representation. -/
theorem exists_easyPower_asymptoticSum_bound_zmod (M : ℕ) [Fact M.Prime]
    (hq : 0 < q) (hcard : 12 * 4 ^ k ≤ M) :
    ∃ B : Finset (ZMod M),
      B.card = rothNumberNat (M / 2) ∧ ThreeAPFree (B : Set (ZMod M)) ∧
      ∃ copies : ℕ,
        3 * (easyEqualTypeWords k).card * B.card ≤ 4 * (M * M) * copies ∧
          (copies : ℝ) * (((q ^ k) * (q ^ k) * (q ^ k) : ℕ) : ℝ) ^
              (omega K / 3) ≤
            (((q + 2) ^ (easyEqualTypeDepth k + 1) : ℕ) : ℝ) := by
  have hM : 3 ≤ M := by
    have hpow : 0 < 4 ^ k := pow_pos (by norm_num) k
    omega
  letI : NeZero (2 : ZMod M) := neZero_two_zmod_of_three_le hM
  obtain ⟨B, hBcard, hB⟩ := exists_threeAPFree_zmod_half M
  obtain ⟨seed, hcount, hasi⟩ :=
    exists_easyPower_asymptoticSum_bound_of_fieldCard K q k hq B hB (by
      simpa [ZMod.card] using hcard)
  let copies := ((easyPartitionHashEncoding (R := ZMod M)).legwiseIsolatedPowerAddresses
    (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card
  exact ⟨B, hBcard, hB, copies, by simpa [ZMod.card, copies] using hcount,
    by simpa [copies] using hasi⟩

/-- Prime-field finite output in rate-ready form: the copy count has the correct `27/4`
exponential numerator up to the explicit polynomial and modulus factors. -/
theorem exists_easyPower_asymptoticSum_rate_bound_zmod (M : ℕ) [Fact M.Prime]
    (hq : 0 < q) (hk : 0 < k) (hcard : 12 * 4 ^ k ≤ M) :
    ∃ B : Finset (ZMod M),
      B.card = rothNumberNat (M / 2) ∧ ThreeAPFree (B : Set (ZMod M)) ∧
      ∃ copies : ℕ,
        27 ^ k * B.card ≤ 6 * k ^ 2 * (M * M) * copies ∧
          (copies : ℝ) * (((q ^ k) * (q ^ k) * (q ^ k) : ℕ) : ℝ) ^
              (omega K / 3) ≤
            (((q + 2) ^ (easyEqualTypeDepth k + 1) : ℕ) : ℝ) := by
  obtain ⟨B, hBcard, hB, copies, hcount, hasi⟩ :=
    exists_easyPower_asymptoticSum_bound_zmod K q k M hq hcard
  refine ⟨B, hBcard, hB, copies, ?_, hasi⟩
  have hcount' : 3 * (easyEqualTypeWords k).card * Fintype.card B ≤
      4 * (M * M) * copies := by
    simpa using hcount
  simpa using easyCopies_lower_of_hashingCount
    (k := k) (M := M) (copies := copies) (B := B) hk hcount'

/-- Purely numerical finite output after choosing a prime hashing modulus by Bertrand's
postulate.  This is the final finite theorem needed before taking the classical easy-CW limit. -/
theorem exists_prime_easyPower_asymptoticSum_rate_bound
    (hq : 0 < q) (hk : 0 < k) :
    ∃ M copies : ℕ,
      M.Prime ∧ 12 * 4 ^ k < M ∧ M ≤ 24 * 4 ^ k ∧
        27 ^ k * rothNumberNat (M / 2) ≤ 6 * k ^ 2 * (M * M) * copies ∧
          (copies : ℝ) * (((q ^ k) * (q ^ k) * (q ^ k) : ℕ) : ℝ) ^
              (omega K / 3) ≤
            (((q + 2) ^ (easyEqualTypeDepth k + 1) : ℕ) : ℝ) := by
  have hn : 12 * 4 ^ k ≠ 0 := by positivity
  obtain ⟨M, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (12 * 4 ^ k) hn
  letI : Fact M.Prime := ⟨hprime⟩
  obtain ⟨B, hBcard, _hB, copies, hcopies, hasi⟩ :=
    exists_easyPower_asymptoticSum_rate_bound_zmod K q k M hq hk hlower.le
  refine ⟨M, copies, hprime, hlower, ?_, ?_, hasi⟩
  · calc
      M ≤ 2 * (12 * 4 ^ k) := hupper
      _ = 24 * 4 ^ k := by ring
  · rwa [hBcard] at hcopies

/-- Finite rate inequality with every combinatorial and progression-free loss collected into an
explicit subexponential factor. -/
theorem easyPower_rate_inequality (hq : 0 < q) (hk : 0 < k) :
    (((27 : ℝ) / 4 * (q : ℝ) ^ omega K) ^ k) ≤
      easyCWSubexponentialLoss k * ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k) := by
  obtain ⟨M, copies, _hprime, hlower, hupper, hcopies, hasi⟩ :=
    exists_prime_easyPower_asymptoticSum_rate_bound K q k hq hk
  have hM : 3 ≤ M := by
    have hpow : 0 < 4 ^ k := pow_pos (by norm_num) k
    omega
  have hMUpper : (M : ℝ) ≤ 24 * (4 : ℝ) ^ k := by exact_mod_cast hupper
  have hhalfPos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    have hpos : 0 < M / 2 := by omega
    exact_mod_cast hpos
  have hhalfUpper : ((M / 2 : ℕ) : ℝ) ≤ 12 * (4 : ℝ) ^ (1 * k) := by
    have hnat : M / 2 ≤ 12 * 4 ^ k := by omega
    calc
      ((M / 2 : ℕ) : ℝ) ≤ ((12 * 4 ^ k : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = 12 * (4 : ℝ) ^ (1 * k) := by rw [one_mul]; push_cast; ring
  have hsqrt := Growth.sqrt_log_le_mul_sqrt_succ (x := ((M / 2 : ℕ) : ℝ)) (c := 12)
    (G := 4) (s := 4) (m := 1) (k := k) hhalfPos (by norm_num) (by norm_num)
    (by norm_num) hhalfUpper (by norm_num) (by norm_num)
  have ht : 4 * √(Real.log ((M / 2 : ℕ) : ℝ)) ≤ 16 * √(((k + 1 : ℕ) : ℝ)) := by
    linarith
  have hcopiesReal : (27 : ℝ) ^ k * (rothNumberNat (M / 2) : ℝ) ≤
      6 * (k : ℝ) ^ 2 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    exact_mod_cast hcopies
  have hasiReal : (copies : ℝ) * (((q : ℝ) ^ omega K) ^ k) ≤
      ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k) := by
    simpa only [easyCubeVolume_rpow_omega_div_three K q k hq,
      easyEqualTypeDepth_add_one hk, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
      pow_mul] using hasi
  have hcnt : (27 : ℝ) ^ k * (((q : ℝ) ^ omega K) ^ k) *
      (rothNumberNat (M / 2) : ℝ) ≤
        6 * (k : ℝ) ^ 2 * ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k) * ((M : ℝ) * (M : ℝ)) := by
    calc
      (27 : ℝ) ^ k * (((q : ℝ) ^ omega K) ^ k) * (rothNumberNat (M / 2) : ℝ)
          = (27 : ℝ) ^ k * (rothNumberNat (M / 2) : ℝ) *
              (((q : ℝ) ^ omega K) ^ k) := by ring
      _ ≤ 6 * (k : ℝ) ^ 2 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) *
              (((q : ℝ) ^ omega K) ^ k) :=
        mul_le_mul_of_nonneg_right hcopiesReal (by positivity)
      _ = 6 * (k : ℝ) ^ 2 * ((M : ℝ) * (M : ℝ)) *
              ((copies : ℝ) * (((q : ℝ) ^ omega K) ^ k)) := by ring
      _ ≤ 6 * (k : ℝ) ^ 2 * ((M : ℝ) * (M : ℝ)) *
              ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k) :=
        mul_le_mul_of_nonneg_left hasiReal (by positivity)
      _ = 6 * (k : ℝ) ^ 2 * ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k) *
              ((M : ℝ) * (M : ℝ)) := by ring
  have hrate := Growth.le_mul_exp_of_mul_rothNumberNat_le (M := M)
    (a := (27 : ℝ) ^ k * (((q : ℝ) ^ omega K) ^ k))
    (b := 6 * (k : ℝ) ^ 2 * ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k))
    (U := 24 * (4 : ℝ) ^ k) (t := 16 * √(((k + 1 : ℕ) : ℝ)))
    (by omega) (by positivity) (by positivity) hMUpper ht hcnt
  rw [mul_pow, div_pow, div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) k)).mpr
  calc
    (27 : ℝ) ^ k * (((q : ℝ) ^ omega K) ^ k) ≤
        3 * (6 * (k : ℝ) ^ 2 * ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k)) *
          (24 * (4 : ℝ) ^ k) * Real.exp (16 * √(((k + 1 : ℕ) : ℝ))) := hrate
    _ = easyCWSubexponentialLoss k * ((((q + 2 : ℕ) : ℝ) ^ 3) ^ k) *
          (4 : ℝ) ^ k := by
      unfold easyCWSubexponentialLoss
      ring

/-- The limiting scalar inequality of the first (three-constituent) Coppersmith--Winograd
construction.  No asymptotic notation remains: the explicit polynomial and Behrend losses are
removed by the reusable subexponential-rate lemma. -/
theorem easyCW_base_inequality (hq : 0 < q) :
    (27 : ℝ) / 4 * (q : ℝ) ^ omega K ≤ (((q + 2 : ℕ) : ℝ) ^ 3) := by
  apply Growth.le_of_pow_succ_le_subexponential_mul_pow_succ
    (show 0 ≤ (((q + 2 : ℕ) : ℝ) ^ 3) by positivity)
    easyCWSubexponentialLoss_subexponential
  intro n
  exact easyPower_rate_inequality K q (n + 1) hq (by omega)

/-- Logarithmic form of the easy-CW rate inequality. -/
theorem easyCW_omega_le_log (hq : 1 < q) :
    omega K ≤
      Real.log ((4 / 27 : ℝ) * (((q + 2 : ℕ) : ℝ) ^ 3)) / Real.log q := by
  have hbase := easyCW_base_inequality K q (by omega)
  have hrpow : (q : ℝ) ^ omega K ≤
      (4 / 27 : ℝ) * (((q + 2 : ℕ) : ℝ) ^ 3) := by
    linarith
  have hqReal : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hlog := Real.le_log_of_rpow_le hqReal hrpow
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hq))).mpr hlog

/-- The historical rounded target in Cornell CS 6810, Theorem 4.1. -/
noncomputable def easyCWTarget : ℝ := 241 / 100

private def easyCWLogSteps : ℕ := 1

private noncomputable def easyCWLogRatioUpper : ℝ :=
  Analysis.logRatioUpper (17 / 233) easyCWLogSteps

private theorem easyCWLogRatio_le_upper :
    Real.log (125 / 108 : ℝ) ≤ easyCWLogRatioUpper := by
  have h := Analysis.le_logRatioUpper (x := (17 / 233 : ℝ))
    (by norm_num) (by norm_num) easyCWLogSteps
  convert h using 1 <;> norm_num [easyCWLogRatioUpper]

private theorem easyCW_rational_log_separation :
    easyCWLogRatioUpper < (23 / 100 : ℝ) * (693147 / 1000000 : ℝ) := by
  norm_num [easyCWLogRatioUpper, easyCWLogSteps,
    Analysis.logRatioUpper, Analysis.atanhPartial,
    Analysis.atanhRemainder]

/-- Floating-point-free scalar certificate for the rounded `2.41` target. -/
theorem log_fourThousand_div_twentySeven_lt_target_mul_log_eight :
    Real.log (4000 / 27 : ℝ) < easyCWTarget * Real.log 8 := by
  have hratio : Real.log (125 / 108 : ℝ) < (23 / 100 : ℝ) * Real.log 2 :=
    easyCWLogRatio_le_upper.trans_lt
      (easyCW_rational_log_separation.trans_le
        (mul_le_mul_of_nonneg_left Analysis.log_two_ge (by norm_num)))
  have hdecomp : Real.log (4000 / 27 : ℝ) =
      7 * Real.log 2 + Real.log (125 / 108 : ℝ) := by
    calc
      Real.log (4000 / 27 : ℝ) =
          Real.log (((2 : ℝ) ^ 7) * (125 / 108 : ℝ)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 7) + Real.log (125 / 108 : ℝ) := by
        rw [Real.log_mul (by positivity) (by norm_num)]
      _ = 7 * Real.log 2 + Real.log (125 / 108 : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hlogEight : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [hdecomp, hlogEight]
  norm_num [easyCWTarget]
  linarith

/-- End-to-end formalization of the first Coppersmith--Winograd construction: over every field,
the matrix-multiplication exponent is strictly below `2.41`. -/
theorem coppersmithWinograd_easy_omega_lt : omega K < easyCWTarget := by
  apply (easyCW_omega_le_log K 8 (by norm_num)).trans_lt
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 8))).mpr
  norm_num
  exact log_fourThousand_div_twentySeven_lt_target_mul_log_eight

theorem easyCWTarget_eq_decimal : easyCWTarget = 2.41 := by
  norm_num [easyCWTarget]

end FiniteAsymptoticSum

end AlgebraicComplexity.Examples
