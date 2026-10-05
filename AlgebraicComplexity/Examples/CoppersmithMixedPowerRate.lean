/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithMixedPowerHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularRate

/-!
# The mixed `CW_7`/`CW_6` extraction and rate inequality

This module completes stage 2 of Coppersmith's [Cop97] `α > 0.294`.  On top of the hashing layer
of `Examples/CoppersmithMixedPowerHashing.lean` it assembles

* the finite extraction `exists_cwMixedPower_rectangularExtraction_of_fieldCard`;
* `cwMixed_scheduleExtraction`, the extraction in the exact shape
  `RectangularScheduleExtraction` consumed by `MatrixMultiplication/RectangularSchedule.lean`;
* the Huang--Pan schedule run at that extraction, `cwMixed_rate_inequality_of_fiberGrowth` and
  `cwMixed_master_inequality_of_fiberGrowth`.

## The four schedule parameters, in the mixed instance

1. *The extraction* is `cwMixed_scheduleExtraction`.
2. *The entropy base* is `cwMixedEntropyBase`, the **product** of the two halves' six-fold
   multinomial growth bases, and its loss `cwMixedMultinomialLoss` is the product of the two
   halves' `WordType.proportionalMultinomialLoss` factors.  A product of two subexponential losses
   is subexponential, so nothing in `Analysis/BinomialEntropyEnvelope.lean` changes; this is the
   "entropy envelope used twice, multiplicatively" that stage 1 anticipated.
3. *The word length* enters only through the border-rank bound
   `R = (q₇+2)^{T₇}·(q₆+2)^{T₆}`.
4. *The geometric data* are `A = q₇^{b₇}q₆^{b₆}` and `C = q₇^{a₇}q₆^{a₆}`.

## The aspect ratio is a parameter here

For a single-`q` tower the constituent `⟨q^m, q^m, q^p⟩` has the rational aspect ratio `p/m`, and
`rectAspectRatio` computes it.  A mixed constituent `⟨7^{b₇}6^{b₆}, 7^{b₇}6^{b₆}, 7^{a₇}6^{a₆}⟩`
has aspect ratio `log C / log A`, which is irrational in general.  The schedule only needs
`A ^ κ ≤ C`, so `κ` is left as a hypothesis-bearing parameter of the two rate theorems; stage 3
chooses it.

## What stage 3 still needs

The two inequalities below are the mixed analogues of
`cwRect_rate_inequality_of_fiberGrowth` and `cwRect_master_inequality_of_fiberGrowth`.  What is
missing for [Cop97, Theorem 1] is purely numeric: a geometric envelope `Φ` for
`cwMixedTypedFiberBound` (a product of two binomial-coefficient products, so a product of two
single-`q` envelopes), Coppersmith's four-parameter selection
`coppersmithLeftType`/`coppersmithRightType` of `Examples/CoppersmithMixedPowerType.lean` plugged
into `(a₇, b₇, e₇, f₇, a₆, b₆, e₆, f₆)`, the near-equality `R ≤ N·M^{2+ε}`, and the optimization
of `α` over `(a : b, s/a, t/b)`.

## References

* [Cop97] D. Coppersmith, *Rectangular matrix multiplication revisited*, J. Complexity **13**
  (1997), 42--49; Sections 4--5 and Theorem 1.
* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299, Sections 5--7.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Growth

universe u

/-! ## The finite extraction -/

section Extraction

variable (K : Type u) [CommRing K]
variable (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ)

/-- The mixed external product restricts to the mixed-type subpartition.  The two steps are the
faithful reindexing of block addresses (`Isomorphic.partitionedReindex`) and the leg-local type
selection. -/
theorem cwMixedExternal_restricts_typeAppendPower :
    Restricts
      (Tensor.external
        (Tensor.power (cwPartitionedTensor K q₇).realize (cwRectDepth a₇ b₇ e₇ f₇ + 1))
        (Tensor.power (cwPartitionedTensor K q₆).realize (cwRectDepth a₆ b₆ e₆ f₆ + 1)))
      (cwMixedTypeAppendPower K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).realize :=
  (((cwMixedPower_realize_isomorphic K q₇ q₆
      (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).trans
    (Isomorphic.partitionedReindex _ _ _)).restricts).trans
    (Tensor.Restricts.partitionedSelect _ (cwMixedKeepBlock a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆))

/-- For a fixed hash seed the mixed power restricts to a genuine indexed direct sum whose
addresses are isolated on all three legs.  This is the pruning step of [Cop97, p. 47], applied
verbatim in its single-alphabet form. -/
theorem cwMixedExternal_restricts_legwiseIsolatedIndexedDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1))) :
    Restricts
      (Tensor.external
        (Tensor.power (cwPartitionedTensor K q₇).realize (cwRectDepth a₇ b₇ e₇ f₇ + 1))
        (Tensor.power (cwPartitionedTensor K q₆).realize (cwRectDepth a₆ b₆ e₆ f₆ + 1)))
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := fun c w ↦ ProductBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₇) (cwRectDepth a₇ b₇ e₇ f₇))
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₆) (cwRectDepth a₆ b₆ e₆ f₆)) c
            ((positiveWordAppendEquiv CWBlock
              (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm w))
          ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
            (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed))
        (fun s : (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
            (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed ↦
          (cwMixedTypeAppendPower K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).constituent s.1)) := by
  apply (cwMixedExternal_restricts_typeAppendPower K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).trans
  apply Tensor.Restricts.modeledTargets_to_legwiseIsolatedIndexedDirectSum
    (cwPartitionHashEncoding (R := R)) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B hB seed
    (cwMixedTypeAppendPower K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
  exact cwMixedTypeAppendPower_support K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆

/-- The legwise-isolated constituent sum restricts componentwise to identical mixed rectangular
matrix-multiplication tensors. -/
theorem cwMixedLegwiseIsolatedIndexedDirectSum_restricts_rectangularDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1))) :
    Restricts
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := fun c w ↦ ProductBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₇) (cwRectDepth a₇ b₇ e₇ f₇))
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₆) (cwRectDepth a₆ b₆ e₆ f₆)) c
            ((positiveWordAppendEquiv CWBlock
              (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm w))
          ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
            (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed))
        (fun s : (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
            (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
            (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed ↦
          (cwMixedTypeAppendPower K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).constituent s.1))
      (matrixMultiplicationDirectSum
        (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
          (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed)
        K (fun _ ↦ q₇ ^ b₇ * q₆ ^ b₆) (fun _ ↦ q₇ ^ b₇ * q₆ ^ b₆)
        (fun _ ↦ q₇ ^ a₇ * q₆ ^ a₆)) := by
  classical
  apply Tensor.Restricts.indexedDirectSum
  intro s
  have hs : s.1 ∈ (cwPartitionHashEncoding (R := R)).modeledAddresses
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
      (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) := by
    apply (cwPartitionHashEncoding (R := R)).filteredPowerAddresses_subset_modeledAddresses
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed
    apply (cwPartitionHashEncoding
      (R := R)).legwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed
    exact s.2
  obtain ⟨word, hword, haddress⟩ :=
    (cwPartitionHashEncoding (R := R)).exists_sourceWord_of_mem_modeledAddresses_legalTargets
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) hs
  have hrestrict := cwMixedAppendPower_constituent_restricts_rectangular
    K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ hword
  change Restricts ((cwMixedAppendPower K q₇ q₆ (cwRectDepth a₇ b₇ e₇ f₇)
    (cwRectDepth a₆ b₆ e₆ f₆)).constituent
      (PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
        (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) word)) _ at hrestrict
  rw [haddress] at hrestrict
  exact hrestrict

/-- A fixed successful hash seed extracts independent copies of
`⟨q₇^{b₇}q₆^{b₆}, q₇^{b₇}q₆^{b₆}, q₇^{a₇}q₆^{a₆}⟩` from the mixed external product. -/
theorem cwMixedExternal_restricts_legwiseIsolatedRectangularDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1))) :
    Restricts
      (Tensor.external
        (Tensor.power (cwPartitionedTensor K q₇).realize (cwRectDepth a₇ b₇ e₇ f₇ + 1))
        (Tensor.power (cwPartitionedTensor K q₆).realize (cwRectDepth a₆ b₆ e₆ f₆ + 1)))
      (matrixMultiplicationDirectSum
        (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
          (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
          (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed)
        K (fun _ ↦ q₇ ^ b₇ * q₆ ^ b₆) (fun _ ↦ q₇ ^ b₇ * q₆ ^ b₆)
        (fun _ ↦ q₇ ^ a₇ * q₆ ^ a₆)) :=
  (cwMixedExternal_restricts_legwiseIsolatedIndexedDirectSum
      K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ B hB seed).trans
    (cwMixedLegwiseIsolatedIndexedDirectSum_restricts_rectangularDirectSum
      K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ B seed)

/-- **Finite mixed rectangular extraction.**  A hashing field of size at least
`12 · cwMixedTypedFiberBound` and a progression-free set `B` produce a seed whose isolated address
family is large and carries a direct sum of identical mixed rectangular products. -/
theorem exists_cwMixedPower_rectangularExtraction_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hcard : 12 * cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1)),
      3 * (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
              (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed).card ∧
        Restricts
          (Tensor.external
            (Tensor.power (cwPartitionedTensor K q₇).realize (cwRectDepth a₇ b₇ e₇ f₇ + 1))
            (Tensor.power (cwPartitionedTensor K q₆).realize (cwRectDepth a₆ b₆ e₆ f₆ + 1)))
          (matrixMultiplicationDirectSum
            (ι := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
              (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
              (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed)
            K (fun _ ↦ q₇ ^ b₇ * q₆ ^ b₆) (fun _ ↦ q₇ ^ b₇ * q₆ ^ b₆)
            (fun _ ↦ q₇ ^ a₇ * q₆ ^ a₆)) := by
  classical
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets
      (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B hB
      (cwMixedType_competitorQuarter_of_fieldCard h₇ h₆ hcard)
  refine ⟨seed, ?_,
    cwMixedExternal_restricts_legwiseIsolatedRectangularDirectSum
      K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ B hB seed⟩
  rw [(cwPartitionHashEncoding (R := R)).card_legwiseIsolatedPowerAddresses
    (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) B seed]
  change 3 * ((cwPartitionHashEncoding (R := R)).legalTargets
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
      (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)).card * B.card ≤ _ at hcount
  rw [PartitionHashEncoding.card_legalTargets] at hcount
  exact hcount

end Extraction

/-! ## The extraction in the shape the Huang--Pan schedule consumes -/

section Schedule

variable (K : Type u) [Field K]

/-- **The deliverable of stage 2.**  Coppersmith's mixed `CW_{q₇}`/`CW_{q₆}` extraction, in the
exact shape `RectangularScheduleExtraction` of `MatrixMultiplication/RectangularSchedule.lean`,
with the geometric data

`A = q₇^{b₇}·q₆^{b₆}`, `C = q₇^{a₇}·q₆^{a₆}`, `R = (q₇+2)^{T₇}·(q₆+2)^{T₆}`,
`T_j = a_j + 2b_j + 2e_j + f_j`,

word count the *product* of the two multinomials, and competitor count the *product* of the two
single-`q` type-restricted fibers.  From here `rectSchedule_rate_inequality` and
`rectSchedule_master_inequality` apply with no further work; what remains for stage 3 is the
entropy input `E ^ N ≤ loss N * words N` (a product of two `cwRectType` Stirling estimates), the
geometric envelope `Φ`, and the numeric optimization. -/
theorem cwMixed_scheduleExtraction (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ)
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆) :
    RectangularScheduleExtraction K (q₇ ^ b₇ * q₆ ^ b₆) (q₇ ^ a₇ * q₆ ^ a₆)
      ((q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) * (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆))
      (fun N ↦ (cwMixedTypeAppendWords (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)
        (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)).card)
      (fun N ↦ cwMixedTypedFiberBound (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)
        (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)) := by
  classical
  intro N hN F _ _ _ hcard B hB
  have hmass₇ : 0 < a₇ * N + 2 * (b₇ * N) + 2 * (e₇ * N) + f₇ * N := by
    have : 0 < (a₇ + 2 * b₇ + 2 * e₇ + f₇) * N := Nat.mul_pos h₇ hN
    nlinarith [this]
  have hmass₆ : 0 < a₆ * N + 2 * (b₆ * N) + 2 * (e₆ * N) + f₆ * N := by
    have : 0 < (a₆ + 2 * b₆ + 2 * e₆ + f₆) * N := Nat.mul_pos h₆ hN
    nlinarith [this]
  obtain ⟨seed, hcount, hrestrict⟩ :=
    exists_cwMixedPower_rectangularExtraction_of_fieldCard K q₇ q₆
      (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N) (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)
      hmass₇ hmass₆ B hB hcard
  refine ⟨↥((cwPartitionHashEncoding (R := F)).legwiseIsolatedPowerAddresses
      (cwMixedDepth (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N) (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N))
      (cwMixedTypeAppendWords (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)
        (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)) B seed),
    inferInstance, ?_, ?_⟩
  · simpa [Fintype.card_coe] using hcount
  · have hd₇ : cwRectDepth (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N) + 1 =
        a₇ * N + 2 * (b₇ * N) + 2 * (e₇ * N) + f₇ * N := cwRectDepth_add_one hmass₇
    have hd₆ : cwRectDepth (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N) + 1 =
        a₆ * N + 2 * (b₆ * N) + 2 * (e₆ * N) + f₆ * N := cwRectDepth_add_one hmass₆
    have hborder₇ :
        BorderRankLE ((q₇ + 2) ^ (cwRectDepth (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N) + 1))
          (Tensor.power (cwPartitionedTensor K q₇).realize
            (cwRectDepth (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N) + 1)) :=
      (cwPartitionedTensor_borderRankLE K q₇).power _
    have hborder₆ :
        BorderRankLE ((q₆ + 2) ^ (cwRectDepth (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N) + 1))
          (Tensor.power (cwPartitionedTensor K q₆).realize
            (cwRectDepth (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N) + 1)) :=
      (cwPartitionedTensor_borderRankLE K q₆).power _
    have hborder := (hborder₇.external hborder₆).of_restricts hrestrict
    rw [hd₇, hd₆] at hborder
    have hAeq : (q₇ ^ b₇ * q₆ ^ b₆) ^ N = q₇ ^ (b₇ * N) * q₆ ^ (b₆ * N) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    have hCeq : (q₇ ^ a₇ * q₆ ^ a₆) ^ N = q₇ ^ (a₇ * N) * q₆ ^ (a₆ * N) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    have hReq : ((q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) *
          (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆)) ^ N =
        (q₇ + 2) ^ (a₇ * N + 2 * (b₇ * N) + 2 * (e₇ * N) + f₇ * N) *
          (q₆ + 2) ^ (a₆ * N + 2 * (b₆ * N) + 2 * (e₆ * N) + f₆ * N) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 2 <;> ring
    rw [hAeq, hCeq, hReq]
    exact hborder

end Schedule


/-! ## The mixed entropy base and its subexponential loss -/

/-- **The entropy base of a mixed type: a product of two single-`q` bases.**  The mixed word count
is a product of two multinomials, so the method-of-types estimate is needed twice,
multiplicatively. -/
noncomputable def cwMixedEntropyBase (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) : ℝ :=
  cwRectEntropyBase a₇ b₇ e₇ f₇ * cwRectEntropyBase a₆ b₆ e₆ f₆

theorem cwMixedEntropyBase_pos {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (ha₇ : 0 < a₇) (hb₇ : 0 < b₇) (he₇ : 0 < e₇) (hf₇ : 0 < f₇)
    (ha₆ : 0 < a₆) (hb₆ : 0 < b₆) (he₆ : 0 < e₆) (hf₆ : 0 < f₆) :
    0 < cwMixedEntropyBase a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ :=
  mul_pos (cwRectEntropyBase_pos ha₇ hb₇ he₇ hf₇) (cwRectEntropyBase_pos ha₆ hb₆ he₆ hf₆)

/-- The subexponential loss of the mixed Stirling estimate: the product of the two halves'
`WordType.proportionalMultinomialLoss` factors. -/
noncomputable def cwMixedMultinomialLoss (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) : ℕ → ℝ :=
  fun N ↦ WordType.proportionalMultinomialLoss (cwRectType a₇ b₇ e₇ f₇) N *
    WordType.proportionalMultinomialLoss (cwRectType a₆ b₆ e₆ f₆) N

/-- A product of two subexponential losses is subexponential, so the mixed loss cancels in the
schedule exactly as a single-`q` loss does. -/
theorem cwMixedMultinomialLoss_subexponential (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    Growth.Subexponential (cwMixedMultinomialLoss a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) :=
  (cwRectType_proportionalMultinomialLoss_subexponential a₇ b₇ e₇ f₇).mul
    (cwRectType_proportionalMultinomialLoss_subexponential a₆ b₆ e₆ f₆)

/-- **The mixed method of types.**  The entropy envelope of
`Analysis/BinomialEntropyEnvelope.lean` is applied once per half and the two estimates are
multiplied. -/
theorem cwMixedType_entropyBase_pow_le_loss_mul_card {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (ha₇ : 0 < a₇) (hb₇ : 0 < b₇) (he₇ : 0 < e₇) (hf₇ : 0 < f₇)
    (ha₆ : 0 < a₆) (hb₆ : 0 < b₆) (he₆ : 0 < e₆) (hf₆ : 0 < f₆)
    {N : ℕ} (hN : 0 < N) :
    cwMixedEntropyBase a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ ^ N ≤
      cwMixedMultinomialLoss a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ N *
        (((cwMixedTypeAppendWords (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)
          (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)).card : ℕ) : ℝ) := by
  have h₇ := cwRectType_entropyBase_pow_le_loss_mul_card ha₇ hb₇ he₇ hf₇ hN
  have h₆ := cwRectType_entropyBase_pow_le_loss_mul_card ha₆ hb₆ he₆ hf₆ hN
  have hbase₇ : (0 : ℝ) ≤ cwRectEntropyBase a₇ b₇ e₇ f₇ ^ N :=
    pow_nonneg (cwRectEntropyBase_pos ha₇ hb₇ he₇ hf₇).le N
  have hrhs₆ : (0 : ℝ) ≤ WordType.proportionalMultinomialLoss (cwRectType a₆ b₆ e₆ f₆) N *
      ((cwRectTypeWords (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)).card : ℝ) :=
    le_trans (pow_nonneg (cwRectEntropyBase_pos ha₆ hb₆ he₆ hf₆).le N) h₆
  rw [card_cwMixedTypeAppendWords, cwMixedEntropyBase, cwMixedMultinomialLoss, mul_pow]
  push_cast
  calc
    cwRectEntropyBase a₇ b₇ e₇ f₇ ^ N * cwRectEntropyBase a₆ b₆ e₆ f₆ ^ N ≤
        (WordType.proportionalMultinomialLoss (cwRectType a₇ b₇ e₇ f₇) N *
            ((cwRectTypeWords (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)).card : ℝ)) *
          (WordType.proportionalMultinomialLoss (cwRectType a₆ b₆ e₆ f₆) N *
            ((cwRectTypeWords (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)).card : ℝ)) :=
      mul_le_mul h₇ h₆ (pow_nonneg (cwRectEntropyBase_pos ha₆ hb₆ he₆ hf₆).le N)
        (le_trans hbase₇ h₇)
    _ = WordType.proportionalMultinomialLoss (cwRectType a₇ b₇ e₇ f₇) N *
          WordType.proportionalMultinomialLoss (cwRectType a₆ b₆ e₆ f₆) N *
          (((cwRectTypeWords (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)).card : ℝ) *
            ((cwRectTypeWords (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N)).card : ℝ)) := by ring

/-! ## The mixed rate and master inequalities -/

section Rate

variable (K : Type u) [Field K]

/-- **The mixed rate inequality at a fixed bootstrap exponent `τ` and competitor envelope `Φ`.**
This is `rectSchedule_rate_inequality` at the mixed extraction; the aspect ratio `κ` is a
parameter because a mixed constituent has an irrational one. -/
theorem cwMixed_rate_inequality_of_fiberGrowth (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ)
    (ha₇ : 0 < a₇) (hb₇ : 0 < b₇) (he₇ : 0 < e₇) (hf₇ : 0 < f₇)
    (ha₆ : 0 < a₆) (hb₆ : 0 < b₆) (he₆ : 0 < e₆) (hf₆ : 0 < f₆)
    (hA : 1 < q₇ ^ b₇ * q₆ ^ b₆)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hmid : (((q₇ ^ b₇ * q₆ ^ b₆ : ℕ)) : ℝ) ^ κ ≤ (((q₇ ^ a₇ * q₆ ^ a₆ : ℕ)) : ℝ))
    {Φ : ℝ} (hΦ : 1 ≤ Φ)
    (hfiber : ∀ N : ℕ,
      ((cwMixedTypedFiberBound (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)
        (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N) : ℕ) : ℝ) ≤ Φ ^ N)
    {τ : ℝ} (hτ : rectangularOmega K κ < τ) :
    (cwMixedEntropyBase a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ / Φ) ^ (rectangularOmega K κ / τ) *
        (((q₇ ^ b₇ * q₆ ^ b₆ : ℕ)) : ℝ) ^ (rectangularOmega K κ) ≤
      (((q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) *
        (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆) : ℕ) : ℝ) := by
  have hmass₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇ := by omega
  have hmass₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆ := by omega
  have hR : 1 ≤ (q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) *
      (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆) := by
    have h1 : 1 ≤ (q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆) := Nat.one_le_pow _ _ (by omega)
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul h1 h2
  exact rectSchedule_rate_inequality K hκ hA hR hmid
    (cwMixed_scheduleExtraction K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ hmass₇ hmass₆)
    (fun N _ ↦ cwMixedTypedFiberBound_pos _ _ _ _ _ _ _ _)
    (cwMixedEntropyBase_pos ha₇ hb₇ he₇ hf₇ ha₆ hb₆ he₆ hf₆)
    (cwMixedMultinomialLoss_subexponential a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
    (fun N hNpos ↦ cwMixedType_entropyBase_pow_le_loss_mul_card
      ha₇ hb₇ he₇ hf₇ ha₆ hb₆ he₆ hf₆ hNpos)
    hΦ hfiber hτ

/-- **The master scalar inequality of the mixed pipeline.**  Letting the bootstrap exponent
decrease to `ω(1, 1, κ)` gives Coppersmith's asymptotic sum inequality in denominator-free form,
with entropy base `E₇ · E₆` and border-rank bound `(q₇+2)^{T₇}·(q₆+2)^{T₆}`. -/
theorem cwMixed_master_inequality_of_fiberGrowth (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ)
    (ha₇ : 0 < a₇) (hb₇ : 0 < b₇) (he₇ : 0 < e₇) (hf₇ : 0 < f₇)
    (ha₆ : 0 < a₆) (hb₆ : 0 < b₆) (he₆ : 0 < e₆) (hf₆ : 0 < f₆)
    (hA : 1 < q₇ ^ b₇ * q₆ ^ b₆)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hmid : (((q₇ ^ b₇ * q₆ ^ b₆ : ℕ)) : ℝ) ^ κ ≤ (((q₇ ^ a₇ * q₆ ^ a₆ : ℕ)) : ℝ))
    {Φ : ℝ} (hΦ : 1 ≤ Φ)
    (hfiber : ∀ N : ℕ,
      ((cwMixedTypedFiberBound (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)
        (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N) : ℕ) : ℝ) ≤ Φ ^ N) :
    cwMixedEntropyBase a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ / Φ *
        (((q₇ ^ b₇ * q₆ ^ b₆ : ℕ)) : ℝ) ^ (rectangularOmega K κ) ≤
      (((q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) *
        (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆) : ℕ) : ℝ) := by
  have hmass₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇ := by omega
  have hmass₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆ := by omega
  have hR : 1 ≤ (q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) *
      (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆) := by
    have h1 : 1 ≤ (q₇ + 2) ^ (a₇ + 2 * b₇ + 2 * e₇ + f₇) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ (q₆ + 2) ^ (a₆ + 2 * b₆ + 2 * e₆ + f₆) := Nat.one_le_pow _ _ (by omega)
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul h1 h2
  exact rectSchedule_master_inequality K hκ hA hR hmid
    (cwMixed_scheduleExtraction K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ hmass₇ hmass₆)
    (fun N _ ↦ cwMixedTypedFiberBound_pos _ _ _ _ _ _ _ _)
    (cwMixedEntropyBase_pos ha₇ hb₇ he₇ hf₇ ha₆ hb₆ he₆ hf₆)
    (cwMixedMultinomialLoss_subexponential a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
    (fun N hNpos ↦ cwMixedType_entropyBase_pow_le_loss_mul_card
      ha₇ hb₇ he₇ hf₇ ha₆ hb₆ he₆ hf₆ hNpos)
    hΦ hfiber

end Rate

end AlgebraicComplexity.Examples
