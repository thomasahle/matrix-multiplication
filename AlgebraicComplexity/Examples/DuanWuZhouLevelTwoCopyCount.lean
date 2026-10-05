/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoJointHashing
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedCancellation

/-!
# The copy count of `[DuanWuZhou2022]` section 6.3, assembled

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoIsolatedBypass.lean`
reduces the level-two endpoint `omega < 2.374631` to three lane inputs, of which the count lane
owns exactly one:

`hcount : dwz63TrueCopyRate ^ (6 * N) <= loss N * (copies : ℝ)`,

with `loss` `Growth.Subexponential`.  At the joint six-orientation hash of
`Examples/DuanWuZhouLevelTwoJointHashing.lean` the copies are the doubly compatibility-isolated
retained addresses `dwz63JointIsolatedSupport`, at word length `N = n + 1`.

## The chain, in the order the factors are lost

Writing `retained` for `dwz63JointRetainedSupport` and `isolated` for
`dwz63JointIsolatedSupport`, `PREP.md` section 4.3's chain (1)--(4) reads, at this instance:

```text
(i)   dwz63TrueCopyRate                <= exp(H_e(alpha_X)) / K          -- min_le_left
(ii)  (exp(H_e(alpha_X)) / K) ^ (6N)
        * (4 |R|^2)                    <= lossHash N * (3 |marked| |B|)  -- method of types
(iii) 3 |marked| |B|                   <= 4 |R|^2 * |retained|           -- one hashing seed
(iv)  |retained|                       <= lossCompat * |isolated|        -- the two zero-outs
```

Only `(i)` needs the `min`: the section 6.3 parameters make branch one --- the *hashing* branch
`exp(H_e(alpha_X)) / K` --- the binding one (`PREP.md` section 7's anti-vacuity check,
`2.97181937368752 < 2.97181970400509`), so proving the chain against that branch is proving it
against the minimum.  Nothing here has to know *which* branch binds: `min_le_left` is valid either
way, and using it can only make the count-side obligation harder, never vacuous.

`(iii)` is `exists_seed_dwz63JointRetained`, `[DuanWuZhou2022]`'s hash loss `4|R|^2 / (3|B|)`
under the modulus condition `8d <= |R|`.  `(iv)` is the isolation floor of the hashing module ---
currently `card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated`, at `lossCompat = 2`, once
the two competitor budgets consume at most half the retained family.  The floor is consumed here
only through the *real* inequality `(iv)`, and `card_le_ratio_mul_of_nat_le` converts any integer
floor `a * |retained| <= b * |isolated|` into it, so a change of constant on the hashing side
costs this module nothing.

Both `(iii)` and `(iv)` are already available, so the *whole* residual of the count lane is
`(ii)`, carried here as the named hypothesis `hmarked`: a single inequality relating the marked
typical-word count, the modulus and the progression-free set.  Its own decomposition ---
`PREP.md` section 4.3's estimates (a)--(d), Bertrand for the modulus and a Behrend set for `B` ---
is the next module's business.

The constants `lossCompat` and the seed's `4 |R|^2 / (3 |B|)` are absorbed into
`dwz63CopyCountLoss`, which is `Growth.Subexponential` as soon as `lossHash` is.

## What is deliberately abstract

`markedWords`, `B`, `seed`, `compat` and the ambient field `R` are all explicit arguments: the
level of the chain assembled here is exactly `PREP.md` section 4.3 step (4), and every
distribution-dependent estimate --- the `dwz63Alpha`-typical marked count, the ambient leg-fiber
degree behind the modulus, the Behrend size of `B` --- lives in `hmarked`, one real inequality.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## An integer floor, read as a real ratio -/

/-- **`a * r <= b * i` becomes `r <= (b / a) * i`.**  The count side states its losses as real
factors, while every finite floor in the hashing and isolation modules is an integer inequality;
this is the one conversion between them, kept separate so that a change of constants upstream
never reaches the chain below. -/
theorem card_le_ratio_mul_of_nat_le {a b r i : ℕ} (ha : 0 < a) (h : a * r ≤ b * i) :
    (r : ℝ) ≤ (b : ℝ) / (a : ℝ) * (i : ℝ) := by
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hcast : (a : ℝ) * (r : ℝ) ≤ (b : ℝ) * (i : ℝ) := by exact_mod_cast h
  rw [div_mul_eq_mul_div, le_div_iff₀ hapos]
  linarith

/-! ## The hashing branch of the true copy rate -/

/-- **The hashing branch of `dwz63TrueCopyRate`**, `alphabar_X / K`.  At the section 6.3
parameters this is the branch the `min` selects, so the count side may prove its chain against it
alone. -/
noncomputable def dwz63HashingBranch : ℝ :=
  Real.exp dwz63EntropyX / dwz63HashLossMultiplier

theorem dwz63HashingBranch_pos : 0 < dwz63HashingBranch := by
  unfold dwz63HashingBranch
  exact div_pos (Real.exp_pos _) dwz63HashLossMultiplier_pos

/-- **`min_le_left` at the section 6.3 rates.**  The true copy rate never exceeds its hashing
branch, so a count-side chain proved against `dwz63HashingBranch` proves the endpoint's
`hcount`. -/
theorem dwz63TrueCopyRate_le_hashingBranch :
    dwz63TrueCopyRate ≤ dwz63HashingBranch := by
  unfold dwz63TrueCopyRate dwz63HashingBranch
  exact min_le_left _ _

/-- The powerwise form of `dwz63TrueCopyRate_le_hashingBranch`. -/
theorem dwz63TrueCopyRate_pow_le_hashingBranch_pow (m : ℕ) :
    dwz63TrueCopyRate ^ m ≤ dwz63HashingBranch ^ m :=
  pow_le_pow_left₀ dwz63TrueCopyRate_pos.le dwz63TrueCopyRate_le_hashingBranch m

/-! ## The subexponential loss the chain accumulates -/

/-- **The count-side loss sequence**: the client's own hashing loss, times the constant factor the
two compatibility zero-outs cost. -/
noncomputable def dwz63CopyCountLoss (lossCompat : ℝ) (lossHash : ℕ → ℝ) : ℕ → ℝ :=
  fun N ↦ lossCompat * lossHash N

/-- **It is subexponential whenever the hashing loss is.**  A constant factor never leaves
`Growth.Subexponential`. -/
theorem subexponential_dwz63CopyCountLoss {lossCompat : ℝ} (hlossCompat : 0 ≤ lossCompat)
    {lossHash : ℕ → ℝ} (h : Growth.Subexponential lossHash) :
    Growth.Subexponential (dwz63CopyCountLoss lossCompat lossHash) :=
  h.const_mul hlossCompat

section Chain

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-! ## Step (iii): the hashing seed -/

/-- **The hash step of `PREP.md` section 4.3.**

`hmarked` is the count lane's single residual estimate --- the `dwz63Alpha`-typical marked count,
read against the modulus `|R|` and the progression-free set `B` --- and `hseed` is
`exists_seed_dwz63JointRetained`.  Together they push the hashing branch's power past the retained
family.  The modulus factor `4|R|^2` cancels exactly, which is why `hmarked` carries it. -/
theorem dwz63_hashingBranch_pow_le_card_jointRetained [Fintype R]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63JointRetainedSupport K hp n markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (6 * (n + 1)) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    dwz63HashingBranch ^ (6 * (n + 1)) ≤
      lossHash * ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ) := by
  have hcardR : (0 : ℝ) < (Fintype.card R : ℝ) := by
    have hpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨(0 : R)⟩
    exact_mod_cast hpos
  refine dwz63_rate_le_loss_of_seed (M := 4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ)))
    (by positivity) hlossHash ?_ hmarked
  exact_mod_cast hseed

/-! ## The assembled copy count -/

/-- **`hcount` of `[DuanWuZhou2022]` section 6.3, at the joint six-orientation hash.**

Every step of `PREP.md` section 4.3's chain is discharged except the marked-count estimate
`hmarked`, which is the count lane's residual and is stated on the four finite cardinalities it
actually relates.  `hseed` is `exists_seed_dwz63JointRetained` and `hclean` is the real form of
the hashing module's isolation floor; both are supplied there, so a client only has to produce
`markedWords`, `B` and the estimate. -/
theorem dwz63_copyCount_of_estimates [Fintype R]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (lossCompat : ℝ) (lossHash : ℕ → ℝ) (hlossHash : 0 ≤ lossHash (n + 1))
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63JointRetainedSupport K hp n markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (6 * (n + 1)) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash (n + 1) * (3 * (markedWords.card : ℝ) * (B.card : ℝ)))
    (hclean : ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ) ≤
      lossCompat * ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      dwz63CopyCountLoss lossCompat lossHash (n + 1) *
        ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ) := by
  have hretained := dwz63_hashingBranch_pow_le_card_jointRetained K hp n markedWords B seed
    hlossHash hseed hmarked
  calc dwz63TrueCopyRate ^ (6 * (n + 1))
      ≤ dwz63HashingBranch ^ (6 * (n + 1)) := dwz63TrueCopyRate_pow_le_hashingBranch_pow _
    _ ≤ lossHash (n + 1) *
          ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ) := hretained
    _ ≤ lossHash (n + 1) *
          (lossCompat *
            ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hclean hlossHash
    _ = dwz63CopyCountLoss lossCompat lossHash (n + 1) *
          ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ) := by
        unfold dwz63CopyCountLoss
        ring

/-- **The same count with the isolation floor in its integer form.**

`hclean` is exactly the shape the hashing module proves --- currently
`card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated` at `a = 1`, `b = 2`. -/
theorem dwz63_copyCount_of_estimates_natFloor [Fintype R]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    {a b : ℕ} (ha : 0 < a) (lossHash : ℕ → ℝ) (hlossHash : 0 ≤ lossHash (n + 1))
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63JointRetainedSupport K hp n markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (6 * (n + 1)) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash (n + 1) * (3 * (markedWords.card : ℝ) * (B.card : ℝ)))
    (hclean : a * (dwz63JointRetainedSupport K hp n markedWords B seed).card ≤
      b * (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      dwz63CopyCountLoss ((b : ℝ) / (a : ℝ)) lossHash (n + 1) *
        ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ) :=
  dwz63_copyCount_of_estimates K hp n markedWords B seed compat _ lossHash hlossHash hseed
    hmarked (card_le_ratio_mul_of_nat_le ha hclean)

/-- **The same count, read through `Fintype.card` of the coerced support.**

This is literally the `hcount` field of `dwzLevelTwoCountingStage_of_isolatedSum`, whose copy index
type is the isolated support coerced to a type. -/
theorem dwz63_copyCount_fintype_of_estimates [Fintype R]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (lossCompat : ℝ) (lossHash : ℕ → ℝ) (hlossHash : 0 ≤ lossHash (n + 1))
    (hseed : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (dwz63JointRetainedSupport K hp n markedWords B seed).card)
    (hmarked : dwz63HashingBranch ^ (6 * (n + 1)) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash (n + 1) * (3 * (markedWords.card : ℝ) * (B.card : ℝ)))
    (hclean : ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ) ≤
      lossCompat * ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      dwz63CopyCountLoss lossCompat lossHash (n + 1) *
        (Fintype.card (dwz63JointIsolatedSupport K hp n markedWords B seed compat) : ℝ) := by
  have h := dwz63_copyCount_of_estimates K hp n markedWords B seed compat lossCompat lossHash
    hlossHash hseed hmarked hclean
  rwa [Fintype.card_coe]

end Chain

/-! ## `hcards` is free -/

/-- **A copy count is automatically positive.**  `dwz63TrueCopyRate` is positive, so its powers
are, and an upper bound `loss N * count` with `count = 0` would be zero.  No hypothesis on `loss`
is needed: if it were negative the inequality would already be impossible.

This discharges the endpoint's `hcards` premise from its `hcount` premise, so a count-side client
never has to exhibit a copy. -/
theorem pos_of_copyCount_le {loss : ℝ} {N count : ℕ}
    (h : dwz63TrueCopyRate ^ (6 * N) ≤ loss * (count : ℝ)) : 0 < count := by
  by_contra hzero
  have hcount : count = 0 := Nat.le_zero.mp (Nat.not_lt.mp hzero)
  rw [hcount] at h
  simp only [Nat.cast_zero, mul_zero] at h
  exact absurd h (not_le.mpr (pow_pos dwz63TrueCopyRate_pos _))

section Cards

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-- **`hcards` at the joint six-orientation hash**, from `hcount` alone. -/
theorem card_dwz63JointIsolatedSupport_pos
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) {loss : ℝ}
    (hcount : dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      loss * ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :
    0 < (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card :=
  pos_of_copyCount_le hcount

/-- The `Fintype.card` form, which is what `dwzLevelTwoCountingStage_of_isolatedSum` asks for. -/
theorem fintype_card_dwz63JointIsolatedSupport_pos
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) {loss : ℝ}
    (hcount : dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      loss * (Fintype.card (dwz63JointIsolatedSupport K hp n markedWords B seed compat) : ℝ)) :
    0 < Fintype.card (dwz63JointIsolatedSupport K hp n markedWords B seed compat) :=
  pos_of_copyCount_le hcount

end Cards

end AlgebraicComplexity.Examples
