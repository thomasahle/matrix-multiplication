/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMarginVariant

set_option autoImplicit false

/-!
# The batched endpoint at the margin, over an arbitrary marked family

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/DuanWuZhouLevelTwoPlainBatchedEndpointMarginVariant.lean`'s
`omega_lt_2374631_of_plainBatchedStageAndLeaf_margin` runs the batched endpoint over the *whole*
marginal-typical ambient `dwz63PlainMarginalWords`.  The assembly lane's `hwitness` is available
only at the **joint** type class `dwz63MarkedWords`, a subfamily; this module re-parameterises the
endpoint by an arbitrary marked family, so that the stage can be run at whichever subfamily the
frame residual is discharged for.

## What changed, and what did not

Two binders are added — `markedWords` and
`hmarked : markedWords j ⊆ dwz63PlainMarginalWords …` — and `hbatchCard` is stated at the
retained support of `markedWords j`.  Everything else is byte-identical to `…_margin`, and the
proof is the same one: the only edit inside it is that
`dwz63_exists_seed_plainCopyCount_at_sharpDegree` — which already takes a marked family and its
inclusion — is handed `(markedWords j) (hmarked j)` instead of
`(dwz63PlainMarginalWords …) (Finset.Subset.refl _)`.

## `hbranch` is a binder, and why

`exists_behrend_dwz63_plainHashBranch` produces the progression-free set `B` *together with* the
branch inequality, and it proves that inequality only at `#(dwz63PlainMarginalWords …)`.  At a
proper subfamily the inequality is a different statement — the `N_triple → N_α` loss has to
stay subexponential — so it is carried here as an explicit hypothesis, in exactly the shape the
Behrend lemma has and the `dwz63_exists_seed_plainCopyCount_at_sharpDegree` call consumes.  The
variant is therefore unconditional modulo that one binder, and instantiating it at
`markedWords := dwz63PlainMarginalWords` with `hbranch := exists_behrend_dwz63_plainHashBranch`
returns the posted `…_margin` verbatim.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173.  The separation between the
marginal-typical triples, the joint count `N_alpha` and the hash modulus that this module's
binders track is `papers/sources/2210.10173/hashing.tex:7-28`; the section 6.2 asymmetric-hashing
retention it feeds is `papers/sources/2210.10173/global_value.tex:130-140`, and the level-two
instance is section 6.3, `papers/sources/2210.10173/global_value.tex:332-348`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricGlobal Tensor

universe u v y

/-! ## The batched endpoint at the margin, over a marked family -/

set_option maxRecDepth 8000 in
/-- **The batched endpoint at the margin, over an arbitrary marked family.**

`…_margin` with `dwz63PlainMarginalWords` freed to a subfamily, and the hashing-branch input
carried as a binder.  See the module docstring.

Proof sketch: `hbranch` is destructured once per `j` (`choose`) into the progression-free set
`B j` and its branch inequality, and `dwz63_exists_seed_plainCopyCount_at_sharpDegree` is then run
at the *marked* family `markedWords j` with its inclusion `hmarked j` --- this is the only place
the subfamily enters --- producing a seed and the copy-count bound
`dwz63TrueCopyRate ^ (6 (len j + 1)) ≤ lossHash ^ 6 * #retained ^ 6`.  The stage endpoint
`omega_lt_2374631_of_plainSymSixStageMargin` is applied at the subexponential envelope
`(dwz63PlainMarkedLossHash · batchLoss) ^ 6`, whose subexponentiality is the committed
`subexponential_pow_six` of a product of two subexponential factors, and at the stage, leaf weight
and leaf value binders unchanged.  Its remaining obligation is discharged by a four-step `calc`:
the seed bound, then `hbatchCard j` raised to the sixth power (`pow_le_pow_left₀`, the loss factor
nonnegative), then `mul_pow` to regroup into `((loss · batchLoss) ^ 6) · (card (β j)) ^ 6`.  No
stage, leaf-value or sixth-power inequality is touched, and the branch bound is not claimed to be
proved here. -/
theorem omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_marked
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {β : ℕ → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j)) (weight : ℕ → ℝ)
    (batchLoss : ℕ → ℝ) (hbatchLoss : Growth.Subexponential batchLoss)
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
            dwz63PlainMarkedLossHash K (len j + 1) *
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
      (dwz63PlainMarkedLossHash_nonneg K (len j + 1)) (hbr j)
  refine omega_lt_2374631_of_plainSymSixStageMargin len hcofinal leaf weight
    (fun N ↦ (dwz63PlainMarkedLossHash K N * batchLoss N) ^ 6)
    (subexponential_pow_six ((subexponential_dwz63PlainMarkedLossHash K).mul hbatchLoss))
    (fun j ↦ hstage j (B j) (seed j) (hBfree j)) hleafWeight hleafValue
    (fun j ↦ lt_of_lt_of_le (pow_pos (Real.exp_pos _) _) (hleafValue j)) ?_
  intro j
  have hcard := hbatchCard j (B j) (seed j) (hBfree j)
  have hlossnn : (0 : ℝ) ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 :=
    pow_nonneg (dwz63PlainMarkedLossHash_nonneg K _) 6
  have h6 : ((Fintype.card (dwz63PlainJointRetainedSupport K
        (dwz63_cwSquareFieldValue_sharpHashField_injective
          (dwz63PlainSharpDegree K (len j) (scale j)))
        (len j) (scale j) (markedWords j)
        (B j) (seed j)) : ℝ)) ^ 6 ≤
      batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6 := by
    rw [Fintype.card_coe, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 6
  calc dwz63TrueCopyRate ^ (6 * (len j + 1))
      ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 *
          ((Fintype.card (dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (markedWords j)
            (B j) (seed j)) : ℝ)) ^ 6 := hseed j
    _ ≤ dwz63PlainMarkedLossHash K (len j + 1) ^ 6 *
          (batchLoss (len j + 1) ^ 6 * (Fintype.card (β j) : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left h6 hlossnn
    _ = (dwz63PlainMarkedLossHash K (len j + 1) * batchLoss (len j + 1)) ^ 6 *
          (Fintype.card (β j) : ℝ) ^ 6 := by
        rw [mul_pow]; ring

end AlgebraicComplexity.Examples
