/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationSeedArith

set_option autoImplicit false

/-!
# One seed for the holes *and* for the copies

Layer 4 (`AlgebraicComplexity/Examples/`).  The section 6.3 hole side and count side were two
independent existentials.  `Examples/DuanWuZhouLevelTwoSeedSelection.lean`'s
`dwz63_exists_seed_retained_and_holeMass` chooses a seed by the joint averaging;
`Examples/DuanWuZhouLevelTwoPlainIntegration.lean`'s
`dwz63_exists_seed_plainCopyCount_at_sharpDegree` chooses one by the retention bound.  Nothing
joined them, and the stage needs *one* seed for both.  This module performs the join, on top of the
three arithmetic steps of `Examples/DuanWuZhouLevelTwoHoleIntegrationSeedArith.lean`.

## What the join delivers

At one seed: the retained lower bound `2 · dwz63GoodBatchSize n ≤ #retained` --- which is the
stage's `a₀`, and `hbatches` and `hfit` at once, through `dwz63GoodBatchCount_pos` and
`dwz63GoodBatchCount_fit` (`Examples/DuanWuZhouLevelTwoAggregateBatching.lean`) --- the aggregate
hole fraction for every hole family dominated by Additional Zeroing-Out Step 2's rule (i) plus the
rule-(ii) allowance, and the sixth power of the copy count.

`markedWords` and `hmarked` are **parameters**, and `#marked` enters only through them, exactly as
in `dwz63_exists_seed_plainCopyCount_at_sharpDegree`; the count side's move to the joint type class
therefore needs no restatement here.  `compat`, `V`, `hcompetitors`, `hzIndex`, `hmodulus`,
`useless` and `huseless` stay binders: they are the compatibility-cell inputs, supplied by
`Examples/DuanWuZhouLevelTwoSeedInputs.lean` and the alphabet bridge.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`
(`global_value.tex`), §6.3 and
`hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash
open scoped BigOperators

universe u v w x

/-! ## The join -/

section Join

variable {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]

omit [Fintype R] [NeZero (2 : R)] in
/-- **A retained family that clears the batch threshold is nonempty** --- the stage's `a₀`. -/
theorem dwz63_nonempty_plainJointRetainedSupport
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (hlarge : 2 * dwz63GoodBatchSize n ≤
      (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card) :
    Nonempty (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) := by
  have hk := dwz63GoodBatchSize_pos n
  have hpos : 0 < (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨⟨a, ha⟩⟩

/-- **One seed, good for the holes and for the copies.**

`markedWords`/`hmarked` are parameters and `#marked` enters only through them, so the count side's
move to the joint type class needs no restatement here.  The conclusion carries, at one seed:
the retained lower bound (which is `a₀`, `hbatches` and `hfit` at once), the aggregate hole
fraction for every hole family dominated by rule (i) plus the rule-(ii) allowance, and the sixth
power of the copy count. -/
theorem dwz63_exists_seed_holeFraction_and_copyCount
    {J : Type w} [Fintype J] [DecidableEq J] {mseg : ℕ}
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (seg : Fin (n + 1) → Fin mseg) (α : Fin mseg → J → ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R)
    (compat : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target →
      SegmentedAvailableWord seg α →
      LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target → Prop)
    (V : ℕ)
    (hquarter : ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      4 * (LegalTriple.xyCompetitorYIndices
        ((cwSquarePartitionHashEncoding hinj).legalTargets n
          (dwz63PlainMarginalWords K n t)) a).card ≤ Fintype.card R)
    (hzIndex : ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      ∀ w : SegmentedAvailableWord seg α,
      ∀ c ∈ dwz63FineCompetitors
        ((cwSquarePartitionHashEncoding hinj).legalTargets n
          (dwz63PlainMarginalWords K n t)) compat a w, c.zIndex = a.zIndex)
    (hcompetitors : ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      ∀ w : SegmentedAvailableWord seg α,
      (dwz63FineCompetitors
        ((cwSquarePartitionHashEncoding hinj).legalTargets n
          (dwz63PlainMarginalWords K n t)) compat a w).card ≤ V)
    (hmodulus : 256 * V ≤ 3 * Fintype.card R)
    (hA : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (useless : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target → ℕ)
    (huseless : ∀ a, 32 * useless a ≤ Fintype.card (SegmentedAvailableWord seg α))
    (hlarge : 2 * dwz63GoodBatchSize n ≤
      dwz63JointSeedCount markedWords.card B.card (Fintype.card R))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hbranch : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      2 * dwz63GoodBatchSize n ≤
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card ∧
        (∀ holes : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) →
            Finset (SegmentedAvailableWord seg α),
          (∀ (a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
              (c : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target),
            c ∈ LegalTriple.markedXYIsolatedTargets
                ((cwSquarePartitionHashEncoding hinj).legalTargets n
                  (dwz63PlainMarginalWords K n t))
                ((cwSquarePartitionHashEncoding hinj).legalTargets n markedWords) B seed →
              (cwSquarePartitionHashEncoding hinj).modeledAddress n c = a.1 →
              (holes a).card ≤
                (dwz63SeedSharedHoles
                  ((cwSquarePartitionHashEncoding hinj).legalTargets n
                    (dwz63PlainMarginalWords K n t)) compat seed c
                  (dwz63IsolatedBucket
                    ((cwSquarePartitionHashEncoding hinj).legalTargets n
                      (dwz63PlainMarginalWords K n t))
                    ((cwSquarePartitionHashEncoding hinj).legalTargets n markedWords)
                    B seed c)).card + useless c) →
            Dwz63AggregateHoleFraction seg α
              (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) holes) ∧
        dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
          (4 * lossHash) ^ 6 *
            ((Fintype.card
              (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) : ℝ) ^ 6) := by
  classical
  set ambient := (cwSquarePartitionHashEncoding hinj).legalTargets n
    (dwz63PlainMarginalWords K n t) with hambient
  set marked := (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords with hmk
  set count := dwz63JointSeedCount markedWords.card B.card (Fintype.card R) with hcount
  have hcardMarked : marked.card = markedWords.card :=
    (cwSquarePartitionHashEncoding hinj).card_legalTargets n markedWords
  have hcountBound : 8 * (Fintype.card R * Fintype.card R) * count ≤
      3 * (marked.card * B.card) := by
    rw [hcardMarked]
    exact dwz63_jointSeedCount_hcount _ _ _
  obtain ⟨seed, hcnt, hmass⟩ := dwz63_exists_seed_retained_and_holeMass ambient marked B
    compat V count hquarter hzIndex hcompetitors hmodulus hcountBound hA
  refine ⟨seed, ?_, ?_, ?_⟩
  · have hcards : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card =
        (LegalTriple.markedXYIsolatedTargets ambient marked B seed).card :=
      (cwSquarePartitionHashEncoding hinj).card_markedXYIsolatedPowerAddresses n
        (dwz63PlainMarginalWords K n t) markedWords hmarked B seed
    omega
  · intro holes hholes
    have hcards : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card =
        (LegalTriple.markedXYIsolatedTargets ambient marked B seed).card :=
      (cwSquarePartitionHashEncoding hinj).card_markedXYIsolatedPowerAddresses n
        (dwz63PlainMarginalWords K n t) markedWords hmarked B seed
    refine dwz63AggregateHoleFraction_image_of_injOn seg α
      ((cwSquarePartitionHashEncoding hinj).modeledAddress n)
      (LegalTriple.markedXYIsolatedTargets ambient marked B seed)
      (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) ?_ hcards holes
      (fun x ↦ (dwz63SeedSharedHoles ambient compat seed x
        (dwz63IsolatedBucket ambient marked B seed x)).card + useless x)
      (fun a c hc hca ↦ hholes a c hc hca) ?_
    · intro y hy
      obtain ⟨c, hc, hcy⟩ := Finset.mem_image.mp hy
      exact ⟨c, hc, hcy⟩
    · exact dwz63_sum_seedSharedHoles_add_useless_le ambient marked B compat seed useless
        hmass huseless
  · have hcards : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card =
        (LegalTriple.markedXYIsolatedTargets ambient marked B seed).card :=
      (cwSquarePartitionHashEncoding hinj).card_markedXYIsolatedPowerAddresses n
        (dwz63PlainMarginalWords K n t) markedWords hmarked B seed
    have hk := dwz63GoodBatchSize_pos n
    have hcpos : 0 < count := by omega
    have hq : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨(0 : R)⟩
    have hret : 3 * (markedWords.card * B.card) ≤
        16 * (Fintype.card R * Fintype.card R) *
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card := by
      have hstep := dwz63_three_mul_le_sixteen_mul_jointSeedCount (marked := markedWords.card)
        (buckets := B.card) hq hcpos
      rw [← hcount] at hstep
      have hmono : 16 * (Fintype.card R * Fintype.card R) * count ≤
          16 * (Fintype.card R * Fintype.card R) *
            (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    exact dwz63_plainCopyCount_pow_six_fintype_of_joint K hinj n t markedWords B seed
      hlossHash hret hbranch

end Join

end AlgebraicComplexity.Examples
