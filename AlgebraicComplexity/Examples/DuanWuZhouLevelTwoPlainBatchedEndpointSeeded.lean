/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMarked

set_option autoImplicit false

/-!
# The batched endpoint at a *chosen* seed

Layer 4 (`AlgebraicComplexity/Examples/`).
`omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_marked`
(`Examples/DuanWuZhouLevelTwoPlainBatchedEndpointMarked.lean:58`) binds `hstage` and `hbatchCard`
for **every** Behrend set and **every** seed, and then picks its own seed inside the proof.  That is
unsatisfiable on the hole side: the stage and the batching bound hold only at a *good* seed --- a
bad seed leaves a small retained family and a large shared-hole mass --- and the batch count
`batches` depends on the retained family, hence on the seed.

This module moves the choice into the hypothesis.  `hseeded` supplies, for each `j`, one Behrend
set, one seed and one batch count together with everything the endpoint's proof consumes at that
seed; `β j` is then `Fin (batches j)`, and the hashing-branch binder disappears because its only
role was to produce the seed and the copy count, both of which are now given.  The period equation
`hlen` also disappears: its only use was the same copy-count call, so the statement is left free of
it (a client that has it, such as the section 6.3 telescope, simply does not pass it).

The conjuncts are in the order and the exact spelling that
`dwz63_exists_seed_stage_marked` (`Examples/DuanWuZhouLevelTwoHoleIntegrationStage.lean`) concludes
in, so that the hole side composes by supplying its own output.  In particular the copy count is
stated at `4 * dwz63PlainMarkedLossHash`, the factor the joint seed selection pays.

## Relation to the unseeded form

`…_margin_marked` is **not** an instance of this theorem, nor conversely.  This one chooses the
index type (`β j := Fin (batches j)`), so it cannot produce the arbitrary `β` that one binds; and
that one's `hstage` holds at every seed, which is strictly stronger than what is available here.
The two are incomparable, and this is the one the hole side can supply.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u y

set_option maxRecDepth 8000 in
/-- **The batched endpoint at the margin, with the seed chosen by the hypothesis.** -/
theorem omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_seeded
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j)) (weight : ℕ → ℝ)
    (batchLoss : ℕ → ℝ) (hbatchLoss : Growth.Subexponential batchLoss)
    (markedWords : ∀ j : ℕ,
      Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) (len j)))
    (hseeded : ∀ j : ℕ,
      ∃ (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1)))
        (batches : ℕ),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) ∧
        Restricts
          (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (len j + 1))
          (Tensor.indexedDirectSum
            (fun _ : dwz63SymSixIndex (Fin batches) ↦ symSix K (leaf j))) ∧
        dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
          (4 * dwz63PlainMarkedLossHash K (len j + 1)) ^ 6 *
            ((Fintype.card (dwz63PlainJointRetainedSupport K
              (dwz63_cwSquareFieldValue_sharpHashField_injective
                (dwz63PlainSharpDegree K (len j) (scale j)))
              (len j) (scale j) (markedWords j) B seed) : ℝ) ^ 6) ∧
        ((dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (markedWords j) B seed).card : ℝ) ≤
          batchLoss (len j + 1) * (Fintype.card (Fin batches) : ℝ))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ,
        Real.exp (dwz63LogVal - dwz63LeafMargin) ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  choose B seed batches _hBfree hstage hcopy hcard using hseeded
  refine omega_lt_2374631_of_plainSymSixStageMargin len hcofinal leaf weight
    (fun N ↦ ((4 * dwz63PlainMarkedLossHash K N) * batchLoss N) ^ 6)
    (subexponential_pow_six
      (((subexponential_dwz63PlainMarkedLossHash K).const_mul (by norm_num)).mul hbatchLoss))
    hstage hleafWeight hleafValue
    (fun j ↦ lt_of_lt_of_le (pow_pos (Real.exp_pos _) _) (hleafValue j)) ?_
  intro j
  have hlossnn : (0 : ℝ) ≤ (4 * dwz63PlainMarkedLossHash K (len j + 1)) ^ 6 :=
    pow_nonneg (by
      have := dwz63PlainMarkedLossHash_nonneg K (len j + 1)
      linarith) 6
  have h6 : ((Fintype.card (dwz63PlainJointRetainedSupport K
        (dwz63_cwSquareFieldValue_sharpHashField_injective
          (dwz63PlainSharpDegree K (len j) (scale j)))
        (len j) (scale j) (markedWords j) (B j) (seed j)) : ℝ)) ^ 6 ≤
      batchLoss (len j + 1) ^ 6 * (Fintype.card (Fin (batches j)) : ℝ) ^ 6 := by
    rw [Fintype.card_coe, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard j) 6
  calc dwz63TrueCopyRate ^ (6 * (len j + 1))
      ≤ (4 * dwz63PlainMarkedLossHash K (len j + 1)) ^ 6 *
          ((Fintype.card (dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (markedWords j) (B j) (seed j)) : ℝ)) ^ 6 := hcopy j
    _ ≤ (4 * dwz63PlainMarkedLossHash K (len j + 1)) ^ 6 *
          (batchLoss (len j + 1) ^ 6 * (Fintype.card (Fin (batches j)) : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left h6 hlossnn
    _ = ((4 * dwz63PlainMarkedLossHash K (len j + 1)) * batchLoss (len j + 1)) ^ 6 *
          (Fintype.card (Fin (batches j)) : ℝ) ^ 6 := by
        rw [mul_pow]; ring

end AlgebraicComplexity.Examples
