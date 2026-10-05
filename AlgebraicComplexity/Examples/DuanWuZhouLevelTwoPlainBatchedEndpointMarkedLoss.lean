/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMarked
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedHashBranch

set_option autoImplicit false

/-!
# The batched endpoint with the hash loss freed, and the joint-class instance

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/DuanWuZhouLevelTwoPlainBatchedEndpointMarked.lean` frees the marked family but keeps the
hash loss hard-coded at `dwz63PlainMarkedLossHash`.  That is exactly one binder too few: the
hashing branch at the **joint** type class holds only at the enlarged
`dwz63PlainMarkedLossHashJoint` (`Examples/DuanWuZhouLevelTwoMarkedHashJointLoss.lean`, with the
branch itself in `Examples/DuanWuZhouLevelTwoMarkedHashBranch.lean`), because the
marginal-to-joint passage costs `typeCountLoss · loss_alpha`.  This module frees the loss too.

## What changed

Three binders are added — `lossHash`, `hlossNonneg`, `hlossSub` — and `hbranch` is stated at
`lossHash (len j + 1)`.  Nothing else moves: the underlying
`dwz63_exists_seed_plainCopyCount_at_sharpDegree` already takes its `lossHash` as a free variable,
so the loss occurs in only three places in the proof, and all three now read the binder.

## The two instances

* `lossHash := dwz63PlainMarkedLossHash K` returns image 126 verbatim (the composition test, run
  as a scratch `example` and deleted);
* `lossHash := dwz63PlainMarkedLossHashJoint K` gives
  `omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_joint`, the endpoint at the joint type
  class, with `hbranch` supplied by `exists_behrend_dwz63_plainHashBranch_marked` and `hmarked` by
  `dwz63_markedWords_subset_plainMarginalWords`.  **Neither binder survives**: what the assembly
  lane must still supply is the stage, the batch count and the leaf data, all at
  `markedWords j = dwz63MarkedWords (len j) (proportionalCounts dwz63Alpha (scale j))`.

## Status of what this module rests on

Both endpoints below are conditional statements and are proved as such; nothing here asserts that
their hypotheses hold.  The joint instance consumes
`Examples/DuanWuZhouLevelTwoMarkedHashJointLoss.lean` and
`Examples/DuanWuZhouLevelTwoMarkedHashBranch.lean`, whose exact bytes are the reissue of the image
C2 returned module-hygiene-RED on 2026-09-02 18:13 and are not themselves accepted at the time of
writing.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173.  The hashing branch and the modulus the
`hbranch` binder tracks are `papers/sources/2210.10173/hashing.tex:7-28` and
`papers/sources/2210.10173/global_value.tex:130-140`; the level-two instance whose constants the
statements carry is section 6.3, `papers/sources/2210.10173/global_value.tex:332-348` with Table 2
at `:354-378`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricGlobal Tensor

universe u v y

/-! ## The endpoint, with the loss freed -/

set_option maxRecDepth 8000 in
/-- **The batched endpoint at the margin, over an arbitrary marked family and an arbitrary
subexponential hash loss.**

Image 126 with the loss freed as well.  Everything else is byte-identical to it; the loss appears
in exactly three places in the proof (the `hlossHash` argument of
`dwz63_exists_seed_plainCopyCount_at_sharpDegree`, the stage's subexponential envelope, and the
final `calc`), and all three now read the binder.

Proof sketch: the same proof as the fixed-loss endpoint, with `lossHash` in place of the constant.
`hbranch` is destructured per `j` into the progression-free set `B j` and its branch inequality at
`lossHash (len j + 1)`; `dwz63_exists_seed_plainCopyCount_at_sharpDegree` is run at the marked
family with `hlossNonneg` supplying the nonnegative multiplier it requires, producing a seed and
the sixth-power copy-count bound.  The stage endpoint
`omega_lt_2374631_of_plainSymSixStageMargin` is applied at the envelope
`(lossHash · batchLoss) ^ 6`, subexponential by `subexponential_pow_six` at `hlossSub.mul
hbatchLoss`; its remaining obligation is the `calc` that chains the seed bound with `hbatchCard`
raised to the sixth power and regroups by `mul_pow`.  Freeing the loss changes no stage, leaf-value
or sixth-power inequality. -/
theorem omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_markedLoss
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {β : ℕ → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j)) (weight : ℕ → ℝ)
    (batchLoss : ℕ → ℝ) (hbatchLoss : Growth.Subexponential batchLoss)
    (lossHash : ℕ → ℝ) (hlossNonneg : ∀ N : ℕ, 0 ≤ lossHash N)
    (hlossSub : Growth.Subexponential lossHash)
    (markedWords : ∀ j : ℕ,
      Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) (len j)))
    (hmarked : ∀ j : ℕ, markedWords j ⊆ dwz63PlainMarginalWords K (len j) (scale j))
    (hbranch : ∀ j : ℕ,
      ∃ B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) ∧
          dwz63HashingBranch ^ (len j + 1) *
              (4 * ((Fintype.card (dwz63SharpHashField
                    (dwz63PlainSharpDegree K (len j) (scale j))) : ℝ) *
                (Fintype.card (dwz63SharpHashField
                    (dwz63PlainSharpDegree K (len j) (scale j))) : ℝ))) ≤
            lossHash (len j + 1) *
              (3 * ((markedWords j).card : ℝ) * (B.card : ℝ)))
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
            (len j) (scale j) (markedWords j)
            B seed).card : ℝ)) ≤
          batchLoss (len j + 1) * (Fintype.card (β j) : ℝ))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ,
        Real.exp (dwz63LogVal - dwz63LeafMargin) ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  choose B hBfree hbr using hbranch
  choose seed hseed using fun j : ℕ ↦
    dwz63_exists_seed_plainCopyCount_at_sharpDegree K
      (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K (len j) (scale j)))
      (hlen j) (markedWords j) (hmarked j)
      (B j) (hBfree j)
      (by rw [card_dwz63SharpHashField]; exact dwz63SharpHashModulus_requirement _)
      (hlossNonneg (len j + 1)) (hbr j)
  refine omega_lt_2374631_of_plainSymSixStageMargin len hcofinal leaf weight
    (fun N ↦ (lossHash N * batchLoss N) ^ 6)
    (subexponential_pow_six (hlossSub.mul hbatchLoss))
    (fun j ↦ hstage j (B j) (seed j) (hBfree j)) hleafWeight hleafValue
    (fun j ↦ lt_of_lt_of_le (pow_pos (Real.exp_pos _) _) (hleafValue j)) ?_
  intro j
  have hcard := hbatchCard j (B j) (seed j) (hBfree j)
  have hlossnn : (0 : ℝ) ≤ lossHash (len j + 1) ^ 6 :=
    pow_nonneg (hlossNonneg _) 6
  have h6 : ((Fintype.card (dwz63PlainJointRetainedSupport K
        (dwz63_cwSquareFieldValue_sharpHashField_injective
          (dwz63PlainSharpDegree K (len j) (scale j)))
        (len j) (scale j) (markedWords j)
        (B j) (seed j)) : ℝ)) ^ 6 ≤
      batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6 := by
    rw [Fintype.card_coe, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 6
  calc dwz63TrueCopyRate ^ (6 * (len j + 1))
      ≤ lossHash (len j + 1) ^ 6 *
          ((Fintype.card (dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (markedWords j)
            (B j) (seed j)) : ℝ)) ^ 6 := hseed j
    _ ≤ lossHash (len j + 1) ^ 6 *
          (batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left h6 hlossnn
    _ = (lossHash (len j + 1) * batchLoss (len j + 1)) ^ 6 *
          (Fintype.card (β j) : ℝ) ^ 6 := by
        rw [mul_pow]; ring

/-! ## The joint-class endpoint -/

set_option maxRecDepth 8000 in
/-- **The batched endpoint at the joint type class.**

`omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_markedLoss` at
`markedWords j := dwz63MarkedWords (len j) (proportionalCounts dwz63Alpha (scale j))` and
`lossHash := dwz63PlainMarkedLossHashJoint K`.  The `hmarked` and `hbranch` binders are both
discharged; `hscale` is the only new hypothesis, and it is the positivity the branch already
needs.

Proof sketch: a single application of the theorem above, with each of its four loss- and
family-related binders supplied by a committed lemma --- `dwz63PlainMarkedLossHashJoint_nonneg`
and `subexponential_dwz63PlainMarkedLossHashJoint` for the loss,
`dwz63_markedWords_subset_plainMarginalWords` for `hmarked`, and
`exists_behrend_dwz63_plainHashBranch_marked K (hscale j) (hlen j)` for `hbranch`.  The stage,
batch-cardinality, leaf-weight and leaf-value binders are passed through untouched, and remain the
caller's obligations. -/
theorem omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_joint
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hscale : ∀ j : ℕ, 0 < scale j)
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
            (len j) (scale j)
            (dwz63MarkedWords (len j) (WordType.proportionalCounts dwz63Alpha (scale j)))
            B seed).card : ℝ)) ≤
          batchLoss (len j + 1) * (Fintype.card (β j) : ℝ))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ,
        Real.exp (dwz63LogVal - dwz63LeafMargin) ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_markedLoss len scale hlen hcofinal leaf
    weight batchLoss hbatchLoss (dwz63PlainMarkedLossHashJoint K)
    (dwz63PlainMarkedLossHashJoint_nonneg K) (subexponential_dwz63PlainMarkedLossHashJoint K)
    (fun j ↦ dwz63MarkedWords (len j) (WordType.proportionalCounts dwz63Alpha (scale j)))
    (fun j ↦ dwz63_markedWords_subset_plainMarginalWords K (len j) (scale j))
    (fun j ↦ exists_behrend_dwz63_plainHashBranch_marked K (hscale j) (hlen j))
    hstage hbatchCard hleafWeight hleafValue

end AlgebraicComplexity.Examples
