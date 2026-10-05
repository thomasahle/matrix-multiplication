/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradEasyRectangularType

/-!
# Rectangular-type hashing extraction for the easy Coppersmith--Winograd tensor

This module is the `r`-generalization of the extraction half of
`Examples/CoppersmithWinogradEasyHashing.lean`.  Where that file selects the *equal*
multiplicity type `easyEqualType k` and extracts many independent copies of the square product
`⟨q^k, q^k, q^k⟩`, this one selects Huang--Pan's rectangular profile `easyRectType a b`
(`Examples/CoppersmithWinogradEasyRectangularType.lean`) and extracts many independent copies of
the *rectangular* product `⟨q^b, q^b, q^a⟩`, which is `⟨n, n, n^r⟩` for `n = q^b` and `r = a/b`.

Two things change relative to the equal-type pipeline and nothing else does:

* the keep-block predicate is **leg-dependent** — `a` zero labels on the `x` leg, `b` on the other
  two — which `PartitionedTensor.select` and
  `PartitionHashEncoding.filter_modeledLegalTargets_eq_of_mem_iff` already support;
* the hashing competitor list is bounded by the leg fiber `2 ^ easyRectLegMiddleCount a b c`
  of `card_easyRectLegWordMapFiber` rather than by the equal-type `4 ^ k`; the uniform bound over
  the three legs is `easyRectFiberBound a b = 2 ^ max (2 * b) (a + b)`.

## Main results

* `mem_easyRectTypeWords_iff_keepBlocks` -- the rectangular type class is exactly the conjunction
  of the three leg-local zero counts;
* `easyRectTypePartitionedPower_constituent_restricts_rectangular` -- every surviving constituent
  restricts to `⟨q^b, q^b, q^a⟩`;
* `exists_easyPower_rectangularExtraction_of_fieldCard` -- the finite extraction statement: a
  hashing field of size at least `12 · 2 ^ max (2b, a+b)` and a progression-free set `B` produce a
  seed whose isolated address family is large and carries a direct sum of identical rectangular
  products;
* `easyRectTypedFiberBound`, `card_easyRectTypeTarget_legFiber_le_typed`,
  `exists_easyPower_rectangularExtraction_of_fieldCard_typed` -- the same extraction with
  Huang--Pan's sharper *type-restricted* competitor count `max (binom(2b, b), binom(a+b, a))`,
  which is what (6.1) needs for `r ≥ 1`.

At `a = b = k` every statement here reduces to its equal-type counterpart; the `*_self`
regressions are collected at the end of the file.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299, Section 6.1.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## Leg-local selection at the rectangular type -/

/-- Depth-generic form of `easySourceMultiplicity_eq_legZero`: the multiplicity of the address
distinguished by a leg equals the zero-label multiplicity of that transposed leg word.  The
equal-type statement fixes the depth to `easyEqualTypeDepth k`, which is never of the form
`easyRectTypeDepth a b` for a general `(a, b)`. -/
theorem easySourceMultiplicity_eq_legZeroAt (d : ℕ)
    (w : PositiveWord easyBlockSupport d) (c : Leg) :
    WordType.multiplicity
        (positiveWordEquiv easyBlockSupport d w) (easyZeroAddress c) =
      WordType.multiplicity
        (positiveWordEquiv CWBlock d
          (PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) d w c)) .zero := by
  classical
  unfold WordType.multiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hword := congrFun
    (PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) d w c) i
  rw [hword]
  exact (easyAddress_leg_eq_zero_iff _ c).symm


/-- Keep the words having exactly `easyRectLegZeroCount a b c` zero labels on leg `c`.

Unlike `easyEqualTypeKeepBlock` the threshold genuinely depends on the leg: Huang--Pan's zeroing
keeps `rN` zeros on the `x` leg and `N` zeros on the other two. -/
noncomputable def easyRectTypeKeepBlock (a b : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (easyRectTypeDepth a b)) : Prop :=
  WordType.multiplicity
    (positiveWordEquiv CWBlock (easyRectTypeDepth a b) word) .zero =
      easyRectLegZeroCount a b c

noncomputable instance easyRectTypeKeepBlock_decidable (a b : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (easyRectTypeDepth a b)) :
    Decidable (easyRectTypeKeepBlock a b c word) := by
  classical
  unfold easyRectTypeKeepBlock
  infer_instance

/-- The rectangular joint multiplicity type is exactly the conjunction of the three leg-local
zero counts. -/
theorem mem_easyRectTypeWords_iff_keepBlocks (a b : ℕ)
    (w : PositiveWord easyBlockSupport (easyRectTypeDepth a b)) :
    w ∈ easyRectTypeWords a b ↔
      ∀ c, easyRectTypeKeepBlock a b c
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport)
          (easyRectTypeDepth a b) w c) := by
  rw [easyRectTypeWords, mem_positiveTypeClass]
  constructor
  · intro htype c
    unfold easyRectTypeKeepBlock
    rw [← easySourceMultiplicity_eq_legZeroAt (easyRectTypeDepth a b) w c, htype]
    rfl
  · intro hkeep
    funext s
    have hs : s = easyZeroAddress .X ∨ s = easyZeroAddress .Y ∨
        s = easyZeroAddress .Z := by
      decide +revert
    rcases hs with rfl | rfl | rfl
    · rw [easySourceMultiplicity_eq_legZeroAt (easyRectTypeDepth a b) w .X]
      exact hkeep .X
    · rw [easySourceMultiplicity_eq_legZeroAt (easyRectTypeDepth a b) w .Y]
      exact hkeep .Y
    · rw [easySourceMultiplicity_eq_legZeroAt (easyRectTypeDepth a b) w .Z]
      exact hkeep .Z

/-! ## Hashing targets and competitor counting -/

/-- Legal affine-hashing targets representing the rectangular-type easy CW words. -/
noncomputable def easyRectTypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (a b : ℕ) :
    Finset (ProgressionHash.LegalTriple R (Fin (easyRectTypeDepth a b + 1)) 2) :=
  (easyPartitionHashEncoding (R := R)).legalTargets
    (easyRectTypeDepth a b) (easyRectTypeWords a b)

@[simp] theorem card_easyRectTypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (a b : ℕ) :
    (easyRectTypeTargets (R := R) a b).card = (easyRectTypeWords a b).card :=
  PartitionHashEncoding.card_legalTargets _ _ _

/-- The uniform-over-legs competitor bound for the rectangular type: `2 ^ max (2b, a+b)`.

By `card_easyRectLegWordMapFiber` the exact leg fiber has size `2 ^ (2b)` on the `x` leg and
`2 ^ (a+b)` on the other two, so this is the maximum of the three.  At `a = b` it is `4 ^ b`,
the equal-type value. -/
def easyRectFiberBound (a b : ℕ) : ℕ := 2 ^ max (2 * b) (a + b)

theorem easyRectLegMiddleCount_le_max (a b : ℕ) (c : Leg) :
    easyRectLegMiddleCount a b c ≤ max (2 * b) (a + b) := by
  cases c <;> simp only [easyRectLegMiddleCount] <;> omega

/-- Every fixed-leg fiber of rectangular-type easy-CW hashing targets is bounded by
`easyRectFiberBound a b`. -/
theorem card_easyRectTypeTarget_legFiber_le
    {R : Type*} [Field R] [NeZero (2 : R)] (a b : ℕ)
    {triple : ProgressionHash.LegalTriple R (Fin (easyRectTypeDepth a b + 1)) 2}
    (htriple : triple ∈ easyRectTypeTargets (R := R) a b) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (easyRectTypeTargets (R := R) a b) triple c).card ≤ easyRectFiberBound a b := by
  classical
  change triple ∈ (easyRectTypeWords a b).image
    ((easyPartitionHashEncoding (R := R)).legalTriple (easyRectTypeDepth a b)) at htriple
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp htriple
  have hlegal : (easyPartitionHashEncoding (R := R)).legalTriple
      (easyRectTypeDepth a b) w ∈ easyRectTypeTargets (R := R) a b := by
    unfold easyRectTypeTargets PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  refine ((easyPartitionHashEncoding (R := R)).card_legFiber_legalTargets_le_card_wordMapFiber
    (easyRectTypeDepth a b) (easyRectTypeWords a b) hlegal c).trans ?_
  unfold easyRectFiberBound
  refine le_trans (le_of_eq ?_)
    (Nat.pow_le_pow_right (by norm_num) (easyRectLegMiddleCount_le_max a b c))
  simpa using card_easyRectLegWordMapFiber a b (easyRectTypeDepth a b) w hw c

/-- The all-leg competitor list for a rectangular-type easy-CW target has size at most
`3 · easyRectFiberBound a b`. -/
theorem card_easyRectTypeTarget_legwiseCompetitors_le
    {R : Type*} [Field R] [NeZero (2 : R)] (a b : ℕ)
    {triple : ProgressionHash.LegalTriple R (Fin (easyRectTypeDepth a b + 1)) 2}
    (htriple : triple ∈ easyRectTypeTargets (R := R) a b) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (easyRectTypeTargets (R := R) a b) triple).card ≤ 3 * easyRectFiberBound a b := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  intro c
  exact card_easyRectTypeTarget_legFiber_le a b htriple c

/-- A hashing field of size at least `12 · 2 ^ max (2b, a+b)` satisfies the quarter-degree
condition of the one-pass all-leg isolation theorem. -/
theorem easyRectType_competitorQuarter_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)] (a b : ℕ)
    (hcard : 12 * easyRectFiberBound a b ≤ Fintype.card R) :
    ∀ triple ∈ easyRectTypeTargets (R := R) a b,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyRectTypeTargets (R := R) a b) triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyRectTypeTargets (R := R) a b) triple).card ≤ 4 * (3 * easyRectFiberBound a b) :=
      Nat.mul_le_mul_left 4 (card_easyRectTypeTarget_legwiseCompetitors_le a b htriple)
    _ = 12 * easyRectFiberBound a b := by ring
    _ ≤ Fintype.card R := hcard

/-! ## Huang--Pan's sharp competitor bound

The bound above uses the whole leg fiber.  Huang--Pan's `M` is the fiber *restricted to the
selected type class*, counted exactly by `card_easyRectTypedWordMapFiber`; the uniform bound over
the three legs is the larger of the two binomial coefficients that occur.  For `b ≤ a` — the
regime `r ≥ 1` of (6.1) — the maximum is `binom(a+b, a)`, which is smaller than the whole-fiber
`2^(a+b)` as soon as `a ≠ 0 ≠ b`. -/

/-- The uniform-over-legs *type-restricted* competitor bound: `max (binom(2b, b), binom(a+b, a))`.

By `card_easyRectTypedWordMapFiber` the exact typed leg fiber is `binom(2b, b)` on the `x` leg and
`binom(a+b, a)` on the other two. -/
def easyRectTypedFiberBound (a b : ℕ) : ℕ :=
  max (Nat.choose (2 * b) b) (Nat.choose (a + b) a)

theorem easyRectTypedFiberBound_pos (a b : ℕ) : 0 < easyRectTypedFiberBound a b :=
  lt_of_lt_of_le (Nat.choose_pos (by omega)) (le_max_left _ _)

theorem easyRectLegTypedFiber_le_bound (a b : ℕ) (c : Leg) :
    easyRectLegTypedFiber a b c ≤ easyRectTypedFiberBound a b := by
  cases c <;>
    simp only [easyRectLegTypedFiber, easyRectTypedFiberBound, le_max_left, le_max_right]

/-- For `b ≤ a` the maximum is attained on the `y` and `z` legs: `binom(2b, b) ≤ binom(a+b, a)`
because `binom(a+b, a) = binom(a+b, b)` and `binom(·, b)` is monotone. -/
theorem easyRectTypedFiberBound_eq_of_le {a b : ℕ} (hba : b ≤ a) :
    easyRectTypedFiberBound a b = Nat.choose (a + b) a := by
  unfold easyRectTypedFiberBound
  refine max_eq_right ?_
  have hsymm : Nat.choose (a + b) a = Nat.choose (a + b) b := by
    have h := Nat.choose_symm (show a ≤ a + b by omega)
    rw [show a + b - a = b from by omega] at h
    exact h.symm
  rw [hsymm]
  exact Nat.choose_le_choose b (by omega)

/-- The type-restricted bound never exceeds the whole-fiber bound `2 ^ max (2b, a+b)`. -/
theorem easyRectTypedFiberBound_le (a b : ℕ) :
    easyRectTypedFiberBound a b ≤ easyRectFiberBound a b := by
  unfold easyRectTypedFiberBound easyRectFiberBound
  refine max_le ?_ ?_
  · exact (Nat.choose_le_two_pow (2 * b) b).trans
      (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  · exact (Nat.choose_le_two_pow (a + b) a).trans
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- Every fixed-leg fiber of rectangular-type easy-CW hashing targets is bounded by Huang--Pan's
type-restricted competitor count. -/
theorem card_easyRectTypeTarget_legFiber_le_typed
    {R : Type*} [Field R] [NeZero (2 : R)] {a b : ℕ} (hab : 0 < a + 2 * b)
    {triple : ProgressionHash.LegalTriple R (Fin (easyRectTypeDepth a b + 1)) 2}
    (htriple : triple ∈ easyRectTypeTargets (R := R) a b) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (easyRectTypeTargets (R := R) a b) triple c).card ≤ easyRectTypedFiberBound a b := by
  classical
  change triple ∈ (easyRectTypeWords a b).image
    ((easyPartitionHashEncoding (R := R)).legalTriple (easyRectTypeDepth a b)) at htriple
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp htriple
  have hlegal : (easyPartitionHashEncoding (R := R)).legalTriple
      (easyRectTypeDepth a b) w ∈ easyRectTypeTargets (R := R) a b := by
    unfold easyRectTypeTargets PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  refine ((easyPartitionHashEncoding (R := R)).card_legFiber_legalTargets_le_card_typedWordMapFiber
    (easyRectTypeDepth a b) (easyRectTypeWords a b) (easyRectType a b)
    (fun word hword ↦ mem_positiveTypeClass.mp hword) hlegal c).trans ?_
  refine le_trans (le_of_eq ?_) (easyRectLegTypedFiber_le_bound a b c)
  refine card_easyRectTypedWordMapFiber (easyRectTypeDepth_add_one hab) c _ ?_
  simpa using easyRectLegWord_multiplicity a b (easyRectTypeDepth a b) w hw c

/-- The all-leg competitor list for a rectangular-type easy-CW target has size at most
`3 · easyRectTypedFiberBound a b`. -/
theorem card_easyRectTypeTarget_legwiseCompetitors_le_typed
    {R : Type*} [Field R] [NeZero (2 : R)] {a b : ℕ} (hab : 0 < a + 2 * b)
    {triple : ProgressionHash.LegalTriple R (Fin (easyRectTypeDepth a b + 1)) 2}
    (htriple : triple ∈ easyRectTypeTargets (R := R) a b) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (easyRectTypeTargets (R := R) a b) triple).card ≤ 3 * easyRectTypedFiberBound a b := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  intro c
  exact card_easyRectTypeTarget_legFiber_le_typed hab htriple c

/-- A hashing field of size at least `12 · max (binom(2b, b), binom(a+b, a))` satisfies the
quarter-degree condition of the one-pass all-leg isolation theorem. -/
theorem easyRectType_competitorQuarter_of_fieldCard_typed
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)] {a b : ℕ} (hab : 0 < a + 2 * b)
    (hcard : 12 * easyRectTypedFiberBound a b ≤ Fintype.card R) :
    ∀ triple ∈ easyRectTypeTargets (R := R) a b,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyRectTypeTargets (R := R) a b) triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyRectTypeTargets (R := R) a b) triple).card ≤
          4 * (3 * easyRectTypedFiberBound a b) :=
      Nat.mul_le_mul_left 4 (card_easyRectTypeTarget_legwiseCompetitors_le_typed hab htriple)
    _ = 12 * easyRectTypedFiberBound a b := by ring
    _ ≤ Fintype.card R := hcard

/-! ## The rectangular-type tensor power -/

section TensorPower

variable (K : Type u) [CommRing K]
variable (q a b : ℕ)

/-- The rectangular-type subpartition of the `(a + 2b)`-fold easy tensor power. -/
noncomputable def easyRectTypePartitionedPower :
    PartitionedTensor (K := K)
      (A := fun _ ↦ PositiveWord CWBlock (easyRectTypeDepth a b))
      (PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
        (easyRectTypeDepth a b)) :=
  ((easyPartitionedTensor K q).positivePower (easyRectTypeDepth a b)).select
    (easyRectTypeKeepBlock a b)

/-- The selected partition support is exactly the modeled rectangular-type legal-target family. -/
theorem easyRectTypePartitionedPower_support
    {R : Type*} [Field R] [NeZero (2 : R)] :
    (easyRectTypePartitionedPower K q a b).support =
      (easyPartitionHashEncoding (R := R)).modeledAddresses
        (easyRectTypeDepth a b) (easyRectTypeTargets (R := R) a b) := by
  classical
  unfold easyRectTypePartitionedPower easyRectTypeTargets
  change ((easyPartitionedTensor K q).positivePower (easyRectTypeDepth a b)).support.filter
      (fun s ↦ ∀ c, easyRectTypeKeepBlock a b c (s c)) = _
  rw [(easyPartitionHashEncoding (R := R)).positivePower_support_eq_modeledLegalTargets
    (easyPartitionedTensor K q) (easyRectTypeDepth a b)]
  exact (easyPartitionHashEncoding (R := R)).filter_modeledLegalTargets_eq_of_mem_iff
    (easyRectTypeDepth a b) (easyRectTypeWords a b) (easyRectTypeKeepBlock a b)
      (mem_easyRectTypeWords_iff_keepBlocks a b)

/-- Every constituent retained by rectangular-type selection restricts to the same rectangular
matrix-multiplication tensor `⟨q^b, q^b, q^a⟩`.  For `a = rb` this is `⟨n, n, n^r⟩` with
`n = q^b`, exactly Huang--Pan's block product. -/
theorem easyRectTypePartitionedPower_constituent_restricts_rectangular
    (s : (easyRectTypePartitionedPower K q a b).support) :
    Restricts ((easyRectTypePartitionedPower K q a b).constituent s.1)
      (matrixMultiplication (K := K) (q ^ b) (q ^ b) (q ^ a)) := by
  have hsSelected := (PartitionedTensor.mem_select_support
    ((easyPartitionedTensor K q).positivePower (easyRectTypeDepth a b))
    (easyRectTypeKeepBlock a b) s.1).mp s.2
  obtain ⟨hsPower, hsKeep⟩ := hsSelected
  obtain ⟨word, haddress⟩ :=
    (easyPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support
      (easyRectTypeDepth a b) hsPower
  change PositiveWord easyBlockSupport (easyRectTypeDepth a b) at word
  change positiveSupportWordBlockAddress easyBlockSupport
    (easyRectTypeDepth a b) word = s.1 at haddress
  have hsKeepWord : ∀ c, easyRectTypeKeepBlock a b c
      (PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport)
        (easyRectTypeDepth a b) word c) := by
    intro c
    unfold PartitionHashEncoding.supportWordAddress
    have hc := congrFun haddress c
    rw [hc]
    exact hsKeep c
  have hword : word ∈ easyRectTypeWords a b :=
    (mem_easyRectTypeWords_iff_keepBlocks a b word).mpr hsKeepWord
  have hwordTensor : word ∈ positiveTypeClass
      (easyPartitionedTensor K q).support (easyRectTypeDepth a b) (easyRectType a b) := hword
  have hrestrict := Tensor.Restricts.positivePower_constituent_matrixMultiplication
    (easyPartitionedTensor K q)
    (easyTensorConstituentM K q) (easyTensorConstituentN K q)
    (easyTensorConstituentP K q)
    (easySupportedConstituent_restricts K q)
    (easyRectTypeDepth a b) word
  change Restricts
    (((easyPartitionedTensor K q).positivePower (easyRectTypeDepth a b)).constituent
      (positiveSupportWordBlockAddress easyBlockSupport
        (easyRectTypeDepth a b) word)) _ at hrestrict
  rw [haddress] at hrestrict
  have hm := easyTensorRectType_positiveWordProduct_m K q a b
    (easyRectTypeDepth a b) word hwordTensor
  have hn := easyTensorRectType_positiveWordProduct_n K q a b
    (easyRectTypeDepth a b) word hwordTensor
  have hp := easyTensorRectType_positiveWordProduct_p K q a b
    (easyRectTypeDepth a b) word hwordTensor
  rw [hm, hn, hp] at hrestrict
  simpa only [easyRectTypePartitionedPower, PartitionedTensor.select] using hrestrict

/-- The canonical `(a + 2b)`-fold tensor power restricts to the rectangular-type partition. -/
theorem easyPower_restricts_rectTypePartitionedPower :
    Restricts
      (Tensor.power (easyPartitionedTensor K q).realize (easyRectTypeDepth a b + 1))
      (easyRectTypePartitionedPower K q a b).realize :=
  (Tensor.Restricts.power_partitionedPositivePower
      (easyPartitionedTensor K q) (easyRectTypeDepth a b)).trans
    (Tensor.Restricts.partitionedSelect
      ((easyPartitionedTensor K q).positivePower (easyRectTypeDepth a b))
      (easyRectTypeKeepBlock a b))

/-- For a fixed hash seed the rectangular-type easy tensor power restricts to a genuine indexed
direct sum whose addresses are isolated on all three legs. -/
theorem easyPower_restricts_rectLegwiseIsolatedIndexedDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (easyRectTypeDepth a b + 1))) :
    Restricts
      (Tensor.power (easyPartitionedTensor K q).realize (easyRectTypeDepth a b + 1))
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (easyRectTypeDepth a b))
          ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed))
        (fun s : (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed ↦
          (easyRectTypePartitionedPower K q a b).constituent s.1)) := by
  apply (easyPower_restricts_rectTypePartitionedPower K q a b).trans
  apply Tensor.Restricts.modeledTargets_to_legwiseIsolatedIndexedDirectSum
    (easyPartitionHashEncoding (R := R)) (easyRectTypeWords a b) B hB seed
      (easyRectTypePartitionedPower K q a b)
  exact easyRectTypePartitionedPower_support K q a b

/-- The legwise-isolated constituent sum restricts componentwise to identical rectangular
matrix-multiplication tensors. -/
theorem easyRectLegwiseIsolatedIndexedDirectSum_restricts_rectangularDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (easyRectTypeDepth a b + 1))) :
    Restricts
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q)
            (easyRectTypeDepth a b))
          ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed))
        (fun s : (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed ↦
          (easyRectTypePartitionedPower K q a b).constituent s.1))
      (matrixMultiplicationDirectSum
        (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed)
        K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) := by
  apply Tensor.Restricts.indexedDirectSum
  intro s
  have hsModeled : s.1 ∈
      (easyPartitionHashEncoding (R := R)).modeledAddresses
        (easyRectTypeDepth a b) (easyRectTypeTargets (R := R) a b) := by
    apply (easyPartitionHashEncoding (R := R)).filteredPowerAddresses_subset_modeledAddresses
      (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed
    apply PartitionHashEncoding.legwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
      (easyPartitionHashEncoding (R := R))
      (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed
    exact s.2
  let selected : (easyRectTypePartitionedPower K q a b).support :=
    ⟨s.1, by
      rw [easyRectTypePartitionedPower_support (R := R) K q a b]
      exact hsModeled⟩
  simpa only [selected] using
    easyRectTypePartitionedPower_constituent_restricts_rectangular K q a b selected

/-- A fixed successful hash seed extracts independent copies of `⟨q^b, q^b, q^a⟩` from the
canonical `(a + 2b)`-fold easy tensor power. -/
theorem easyPower_restricts_rectLegwiseIsolatedRectangularDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (easyRectTypeDepth a b + 1))) :
    Restricts
      (Tensor.power (easyPartitionedTensor K q).realize (easyRectTypeDepth a b + 1))
      (matrixMultiplicationDirectSum
        (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed)
        K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) :=
  (easyPower_restricts_rectLegwiseIsolatedIndexedDirectSum K q a b B hB seed).trans
    (easyRectLegwiseIsolatedIndexedDirectSum_restricts_rectangularDirectSum K q a b B seed)

/-- Finite rectangular-type extraction with the exact division-free hashing count. -/
theorem exists_easyPower_rectangularExtraction
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ easyRectTypeTargets (R := R) a b,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (easyRectTypeTargets (R := R) a b) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyRectTypeDepth a b + 1)),
      3 * (easyRectTypeWords a b).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed).card ∧
        Restricts
          (Tensor.power (easyPartitionedTensor K q).realize (easyRectTypeDepth a b + 1))
          (matrixMultiplicationDirectSum
            (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed)
            K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) := by
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets
      (easyRectTypeTargets (R := R) a b) B hB hquarter
  refine ⟨seed, ?_,
    easyPower_restricts_rectLegwiseIsolatedRectangularDirectSum K q a b B hB seed⟩
  rw [(easyPartitionHashEncoding (R := R)).card_legwiseIsolatedPowerAddresses
    (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed]
  change 3 * ((easyPartitionHashEncoding (R := R)).legalTargets
      (easyRectTypeDepth a b) (easyRectTypeWords a b)).card * B.card ≤ _ at hcount
  rw [PartitionHashEncoding.card_legalTargets] at hcount
  exact hcount

/-- Finite rectangular-type extraction with competitor counting internalized: only the explicit
field-size and progression-free-set inputs remain. -/
theorem exists_easyPower_rectangularExtraction_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * easyRectFiberBound a b ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyRectTypeDepth a b + 1)),
      3 * (easyRectTypeWords a b).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed).card ∧
        Restricts
          (Tensor.power (easyPartitionedTensor K q).realize (easyRectTypeDepth a b + 1))
          (matrixMultiplicationDirectSum
            (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed)
            K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) :=
  exists_easyPower_rectangularExtraction K q a b B hB
    (easyRectType_competitorQuarter_of_fieldCard a b hcard)

/-- Finite rectangular-type extraction with Huang--Pan's *type-restricted* competitor count: the
hashing field only has to have size at least `12 · max (binom(2b, b), binom(a+b, a))`, which for
`b ≤ a` is `12 · binom(a+b, a)` rather than the whole-fiber `12 · 2^(a+b)`.

This is the only change needed to upgrade the `r ≥ 1` branch of Huang--Pan Section 6 to the sharp
(6.1); everything downstream is the same schedule. -/
theorem exists_easyPower_rectangularExtraction_of_fieldCard_typed
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)] (hab : 0 < a + 2 * b)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * easyRectTypedFiberBound a b ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (easyRectTypeDepth a b + 1)),
      3 * (easyRectTypeWords a b).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed).card ∧
        Restricts
          (Tensor.power (easyPartitionedTensor K q).realize (easyRectTypeDepth a b + 1))
          (matrixMultiplicationDirectSum
            (ι := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (easyRectTypeDepth a b) (easyRectTypeWords a b) B seed)
            K (fun _ ↦ q ^ b) (fun _ ↦ q ^ b) (fun _ ↦ q ^ a)) :=
  exists_easyPower_rectangularExtraction K q a b B hB
    (easyRectType_competitorQuarter_of_fieldCard_typed hab hcard)

end TensorPower

end AlgebraicComplexity.Examples
