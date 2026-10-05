/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainOpenIntegration

set_option autoImplicit false

/-!
# The endpoint against a batched stage

Layer 4 (`AlgebraicComplexity/Examples/`).  `omega_lt_2374631_of_plainStageAndLeaf`
(`Examples/DuanWuZhouLevelTwoPlainOpenIntegration.lean`) indexes its leaf sum by the retained
family itself.  `Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s stage does not: the Hole Lemma
repairs **one leaf per batch**, so it lands on `⊕_{β⁶}` for the batch index `β`.  At `batch := id`
the two agree only vacuously --- every batch fibre is then a singleton, `hbudget` reads
`|avail| · |holes a| < |avail|`, and the holes are forced empty.

This module closes that seam.  `omega_lt_2374631_of_plainBatchedStageAndLeaf` takes an arbitrary
batch index `β` and one extra hypothesis,

`#retained ≤ batchLoss (n+1) · #β`  with  `batchLoss` subexponential,

and feeds the factor through `loss`: the endpoint's loss becomes
`(dwz63PlainMarkedLossHash · batchLoss) ^ 6`, subexponential because
`Growth.Subexponential` is closed under products and `subexponential_pow_six` absorbs the sixth
power.  Everything else --- the Behrend set, `hbranch`, the modulus, the seed and the copy count
--- is discharged exactly as in `omega_lt_2374631_of_plainStageAndLeaf`.

`Examples/DuanWuZhouLevelTwoPlainUniformBatch.lean` supplies the batching: `uniformBatch k hbatches`
with `k = ⌈8(L+1)/7⌉` and `batches = #retained / k` satisfies `hbatch` and `hbudget`, and
`dwz63_card_le_two_mul_mul_div` gives `#retained ≤ 2k · batches`, i.e. `batchLoss = 2k = O(n)`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u y

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`omega < 2.374631` from a batched stage, its leaf value, and the batching loss.**

The count side is complete: `hbranch` is `exists_behrend_dwz63_plainHashBranch`, the modulus is
`dwz63SharpHashModulus_requirement`, the seed and the copy count are
`dwz63_exists_seed_plainCopyCount_at_sharpDegree`.  What remains are the stage, the leaf's value,
and the batching bound. -/
theorem omega_lt_2374631_of_plainBatchedStageAndLeaf
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {β : ℕ → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j)) (weight : ℕ → ℝ)
    (batchLoss : ℕ → ℝ) (hbatchLoss : Growth.Subexponential batchLoss)
    (hstage : ∀ (j : ℕ)
        (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (_seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) →
        Restricts
          (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (len j + 1))
          (Tensor.indexedDirectSum
            (fun _ : dwz63SymSixIndex (β j) ↦ symSix K (leaf j))))
    (hbatchCard : ∀ (j : ℕ)
        (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) →
        (((dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
            B seed).card : ℝ)) ≤
          batchLoss (len j + 1) * (Fintype.card (β j) : ℝ))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ, Real.exp dwz63LogVal ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  choose B hBfree hbr using fun j : ℕ ↦ exists_behrend_dwz63_plainHashBranch K (hlen j)
  choose seed hseed using fun j : ℕ ↦
    dwz63_exists_seed_plainCopyCount_at_sharpDegree K
      (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K (len j) (scale j)))
      (hlen j) (dwz63PlainMarginalWords K (len j) (scale j)) (Finset.Subset.refl _)
      (B j) (hBfree j)
      (by rw [card_dwz63SharpHashField]; exact dwz63SharpHashModulus_requirement _)
      (dwz63PlainMarkedLossHash_nonneg K (len j + 1)) (hbr j)
  refine omega_lt_2374631_of_plainSymSixStage len hcofinal leaf weight
    (fun N ↦ (dwz63PlainMarkedLossHash K N * batchLoss N) ^ 6)
    (subexponential_pow_six ((subexponential_dwz63PlainMarkedLossHash K).mul hbatchLoss))
    (fun j ↦ hstage j (B j) (seed j) (hBfree j)) hleafWeight hleafValue ?_
  intro j
  have hcard := hbatchCard j (B j) (seed j) (hBfree j)
  have hlossnn : (0 : ℝ) ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 :=
    pow_nonneg (dwz63PlainMarkedLossHash_nonneg K _) 6
  have h6 : ((Fintype.card (dwz63PlainJointRetainedSupport K
        (dwz63_cwSquareFieldValue_sharpHashField_injective
          (dwz63PlainSharpDegree K (len j) (scale j)))
        (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
        (B j) (seed j)) : ℝ)) ^ 6 ≤
      batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6 := by
    rw [Fintype.card_coe, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 6
  calc dwz63TrueCopyRate ^ (6 * (len j + 1))
      ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 *
          ((Fintype.card (dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
            (B j) (seed j)) : ℝ)) ^ 6 := hseed j
    _ ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 *
          (batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left h6 hlossnn
    _ = (dwz63PlainMarkedLossHash K (len j + 1) * batchLoss (len j + 1)) ^ 6 *
          (Fintype.card (β j) : ℝ) ^ 6 := by
        rw [mul_pow]; ring

end AlgebraicComplexity.Examples
