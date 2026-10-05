/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpoint

set_option autoImplicit false

/-!
# The Hole-Lemma batching factor is absorbed by the loss

Layer 4 (`AlgebraicComplexity/Examples/`).  `omega_lt_2374631_of_plainBatchedStageAndLeaf` takes the
batching bound as `#retained ≤ batchLoss (n+1) · #β` with `batchLoss` subexponential.  The tensor
lane's batches have size `k₀ = ⌊log₈ |avail|⌋ + 1` --- the exact threshold the stage's `hbudget`
binder demands from the per-triple `1/8` bound --- so it supplies

`#retained ≤ 2 · k₀ · #β`  with  `k₀ ≤ 4 (n+1) + 1`,

the linear bound coming from `|avail| ≤ 9 ^ (n+1)`.  This module records that such a factor is
subexponential and gives the endpoint in that form directly, so the join
`dwz63_exists_seed_plainCopyCount_at_sharpDegree` --- which counts `#retained` --- composes with no
new hypothesis: the polynomial factor lands in `loss` through the committed closure lemmas
(`Growth.Subexponential.natCast_pow`, `.const_mul`, `.add`, `.mono`, then `subexponential_pow_six`).

Nothing here is about the Hole Lemma itself; it is the arithmetic that keeps the batching free.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u y

/-! ## A linearly bounded natural sequence is subexponential -/

/-- **An affine real sequence is subexponential.** -/
theorem dwz63_subexponential_affine {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Growth.Subexponential (fun N : ℕ ↦ a * (N : ℝ) + b) := by
  have hlin : Growth.Subexponential (fun N : ℕ ↦ a * (N : ℝ)) := by
    have h := (Growth.Subexponential.natCast_pow 1).const_mul ha
    simpa only [pow_one] using h
  simpa using hlin.add (Growth.Subexponential.const hb)

/-- **A natural sequence bounded by an affine one is subexponential.** -/
theorem dwz63_subexponential_natCast_le_affine (f : ℕ → ℕ) (a b : ℕ)
    (h : ∀ N : ℕ, f N ≤ a * N + b) :
    Growth.Subexponential (fun N : ℕ ↦ (f N : ℝ)) := by
  refine Growth.Subexponential.mono
    (dwz63_subexponential_affine (a := (a : ℝ)) (b := (b : ℝ))
      (Nat.cast_nonneg a) (Nat.cast_nonneg b))
    (fun N ↦ Nat.cast_nonneg _) (fun N ↦ ?_)
  have hcast : ((f N : ℕ) : ℝ) ≤ ((a * N + b : ℕ) : ℝ) := by exact_mod_cast h N
  push_cast at hcast
  linarith

/-- **The Hole-Lemma batching factor is subexponential.**  `k₀ ≤ 4 (n+1) + 1` is what
`|avail| ≤ 9 ^ (n+1)` gives for `k₀ = ⌊log₈ |avail|⌋ + 1`. -/
theorem dwz63_subexponential_batchLoss (k₀ : ℕ → ℕ) (hk₀ : ∀ N : ℕ, k₀ N ≤ 4 * N + 1) :
    Growth.Subexponential (fun N : ℕ ↦ 2 * (k₀ N : ℝ)) :=
  (dwz63_subexponential_natCast_le_affine k₀ 4 1 hk₀).const_mul (by norm_num)

/-! ## The endpoint at a linearly bounded batch size -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`omega < 2.374631` from a batched stage whose batches have linearly bounded size.**

`omega_lt_2374631_of_plainBatchedStageAndLeaf` with `batchLoss := 2 k₀`, and the batching bound
stated over `ℕ` in the shape the batch construction produces.  No new hypothesis: the polynomial
factor is absorbed into `loss`. -/
theorem omega_lt_2374631_of_plainLinearBatchedStageAndLeaf
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {β : ℕ → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j)) (weight : ℕ → ℝ)
    (k₀ : ℕ → ℕ) (hk₀ : ∀ N : ℕ, k₀ N ≤ 4 * N + 1)
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
        (dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
            B seed).card ≤ 2 * k₀ (len j + 1) * Fintype.card (β j))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ, Real.exp dwz63LogVal ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) := by
  refine omega_lt_2374631_of_plainBatchedStageAndLeaf len scale hlen hcofinal leaf weight
    (fun N ↦ 2 * (k₀ N : ℝ)) (dwz63_subexponential_batchLoss k₀ hk₀) hstage ?_
    hleafWeight hleafValue
  intro j B seed hB
  have h := hbatchCard j B seed hB
  have hcast : (((dwz63PlainJointRetainedSupport K
      (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K (len j) (scale j)))
      (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
      B seed).card : ℕ) : ℝ) ≤
      ((2 * k₀ (len j + 1) * Fintype.card (β j) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  linarith

end AlgebraicComplexity.Examples
