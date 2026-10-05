/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalSelect
import AlgebraicComplexity.MatrixMultiplication.SymSixDistribution

/-!
# The copy count at the plain partition, and its sixth power

Layer 4 (`AlgebraicComplexity/Examples/`).  The plain analogue of
`Examples/DuanWuZhouLevelTwoCopyCount.lean`'s chain, at the exponent the plain route actually
produces.

`[DuanWuZhou2022]` hashes `(CW_q^{⊗2^{ℓ-1}})^{⊗n}` (`global_value.tex:12`), one component per
position, so the hash delivers `m' ≈ dwz63TrueCopyRate ^ N` retained copies at word length
`N = n + 1` --- an exponent in `N`, not `6N`.  The sixth power appears only afterwards, when
`sym₆` is applied to the uniform direct sum: `sym₆(⊕_{ι} L) ≅ ⊕_{ι⁶} sym₆(L)`
(`Tensor/SymSixDistribution.lean:123`, `Isomorphic.symSix_indexedDirectSum_uniform`), so `m'`
copies of one leaf become `m'⁶` copies of the symmetrized leaf and the master theorem's
`dwz63TrueCopyRate ^ (6 N)` is met exactly.

That the leaf is **uniform** is what makes this work, and it is what the paper supplies: all
retained broken copies degenerate to the same standard-form tensor `𝒯*`
(`global_value.tex:110-113`), so every one of the `m'⁶` terms --- not merely the diagonal ones ---
is `sym₆(𝒯*)`.

## The losses

Both losses are polynomial, hence subexponential.  `p_comp` is *not* a second loss: it is already
inside `min(N_α·N_X/N_triple, N_Z/p_comp)` as the second branch (`global_value.tex:137,139`).  The
hole lemma contributes `m' ≥ N_retain·7/(8(nℓ+2)) = N_retain/O(n)` (`global_value.tex:277`), and
raising to the sixth power turns an `O(n)` loss into `O(n⁶)`.  `subexponential_pow_six` records
that `Growth.Subexponential` survives it.

Per position the arithmetic is exact: the retained rate is `H(α_X) − log K = 1.0891743499950`,
which is the same expression as `log dwz63TrueCopyRate`, with zero slack.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

/-! ## Raising a copy count to the sixth power -/

/-- **A copy count raised to the sixth power.**  Both sides are the count-side shape: a rate power
bounded by a loss times a nonnegative quantity. -/
theorem pow_six_of_copyCount {rate loss x : ℝ} (hrate : 0 ≤ rate) {m : ℕ}
    (h : rate ^ m ≤ loss * x) :
    rate ^ (6 * m) ≤ loss ^ 6 * x ^ 6 := by
  have h6 : (rate ^ m) ^ 6 ≤ (loss * x) ^ 6 :=
    pow_le_pow_left₀ (pow_nonneg hrate m) h 6
  calc rate ^ (6 * m) = (rate ^ m) ^ 6 := by rw [Nat.mul_comm, pow_mul]
    _ ≤ (loss * x) ^ 6 := h6
    _ = loss ^ 6 * x ^ 6 := by rw [mul_pow]

/-- **The sixth power keeps a loss subexponential.**  `O(n)` from the hole lemma becomes `O(n⁶)`,
which `Growth.Subexponential` absorbs. -/
theorem subexponential_pow_six {loss : ℕ → ℝ} (h : Growth.Subexponential loss) :
    Growth.Subexponential (fun m ↦ loss m ^ 6) := by
  have h6 := (((((h.mul h).mul h).mul h).mul h).mul h)
  have hfun : (fun m ↦ loss m ^ 6) =
      fun m ↦ loss m * loss m * loss m * loss m * loss m * loss m := by
    funext m; ring
  rw [hfun]
  exact h6

/-! ## The chain at the plain partition, per position -/

section Chain

variable {R : Type v} [Field R]

/-- **The hash step at the plain partition**, at word length `N = n + 1`.

`hmarked` is the count lane's residual estimate and `hseed` is
`exists_seed_dwz63PlainJointRetained`; the modulus factor `4|R|²` cancels exactly. -/
theorem dwz63_hashingBranch_pow_le_card_plainJointRetained [Fintype R]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    dwz63HashingBranch ^ (n + 1) ≤
      lossHash * ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card : ℝ) := by
  have hcardR : (0 : ℝ) < (Fintype.card R : ℝ) := by
    have hpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨(0 : R)⟩
    exact_mod_cast hpos
  refine dwz63_rate_le_loss_of_seed (M := 4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ)))
    (by positivity) hlossHash ?_ hmarked
  exact_mod_cast hseed

/-- **The copy count at the plain partition**, at the per-position exponent `N = n + 1`. -/
theorem dwz63_plainCopyCount_of_estimates [Fintype R]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    dwz63TrueCopyRate ^ (n + 1) ≤
      lossHash * ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card : ℝ) :=
  (dwz63TrueCopyRate_pow_le_hashingBranch_pow _).trans
    (dwz63_hashingBranch_pow_le_card_plainJointRetained K hinj n t markedWords B seed hlossHash
      hseed hmarked)

/-- **The sixth power of the plain copy count**, the exponent the master theorem consumes. -/
theorem dwz63_plainCopyCount_pow_six_of_estimates [Fintype R]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      lossHash ^ 6 *
        (((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card : ℝ) ^ 6) :=
  pow_six_of_copyCount dwz63TrueCopyRate_pos.le
    (dwz63_plainCopyCount_of_estimates K hinj n t markedWords B seed hlossHash hseed hmarked)

/-- The `Fintype.card` form, which is the shape
`HasTauWeight.symSix_indexedDirectSum_uniform` produces. -/
theorem dwz63_plainCopyCount_pow_six_fintype [Fintype R]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      lossHash ^ 6 *
        ((Fintype.card (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) : ℝ) ^ 6) := by
  have h := dwz63_plainCopyCount_pow_six_of_estimates K hinj n t markedWords B seed hlossHash
    hseed hmarked
  rwa [Fintype.card_coe]

end Chain

/-! ## The sixth power, wired to the symmetrized weight -/

section SymSix

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {U : Leg → Type v} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]

/-- **The per-position copy count meets the master theorem's `6 N` exponent.**

`m` copies of one uniform leaf carry `m⁶` times the leaf's `sym₆`-weight
(`HasTauWeight.symSix_indexedDirectSum_uniform`), and a copy count at exponent `N` becomes one at
exponent `6 N` against the sixth power of the loss.  Together: the plain route's per-position
count is exactly what the endpoint asks for. -/
theorem dwz63_symSix_weight_of_plainCopyCount {leaf : Tensor3 K U} {value lossHash : ℝ} {N : ℕ}
    (hleaf : HasTauWeight K (symSix K leaf) dwz63Tau value) (hvalue : 0 ≤ value)
    (hcount : dwz63TrueCopyRate ^ N ≤ lossHash * (Fintype.card ι : ℝ)) :
    HasTauWeight K (symSix K (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) fun _ ↦ leaf))
        dwz63Tau ((Fintype.card ι : ℝ) ^ 6 * value) ∧
      dwz63TrueCopyRate ^ (6 * N) * value ≤
        lossHash ^ 6 * ((Fintype.card ι : ℝ) ^ 6 * value) := by
  refine ⟨HasTauWeight.symSix_indexedDirectSum_uniform hleaf, ?_⟩
  have h6 := pow_six_of_copyCount (x := (Fintype.card ι : ℝ)) dwz63TrueCopyRate_pos.le hcount
  calc dwz63TrueCopyRate ^ (6 * N) * value
      ≤ lossHash ^ 6 * ((Fintype.card ι : ℝ) ^ 6) * value :=
        mul_le_mul_of_nonneg_right h6 hvalue
    _ = lossHash ^ 6 * ((Fintype.card ι : ℝ) ^ 6 * value) := by ring

end SymSix

end AlgebraicComplexity.Examples
