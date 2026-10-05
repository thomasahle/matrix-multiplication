/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedHashJointLoss

set_option autoImplicit false

/-!
# `hbranch` at the joint type class

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoPlainMarkedBranch.lean`'s
`exists_behrend_dwz63_plainHashBranch` proves the hashing-branch input at the **marginal-typical**
family `dwz63PlainMarginalWords`.  The assembly lane's `hwitness` is available only at the
**joint** type class `dwz63MarkedWords`, so the batched endpoint's `hbranch` binder has to be
discharged there.  This module does that, on top of the enlarged loss and the marginal-to-joint
passage of `Examples/DuanWuZhouLevelTwoMarkedHashJointLoss.lean`.

## Notation: the field type and the hash-loss multiplier

`K` is the **field type parameter** of every declaration below; `hashMult` is shorthand for the
committed real constant `dwz63HashLossMultiplier`.  What cancels in the three theorems below is
the *exponential power* `hashMult ^ (n+1)`; no definition here is syntactically independent of the
field type `K`, and `dwz63PlainMarkedLossHashJoint` takes `K` as an argument.

## Why the chain is run at `e ^ H(alpha_X)`

`dwz63_card_plainMarginalWords_le_marked` costs one factor `hashMult ^ (n+1)` on the right, and
`dwz63HashingBranch = e ^ H(alpha_X) / hashMult` carries `hashMult ^ -(n+1)`.  Running the whole
chain at `e ^ H(alpha_X)` and cancelling that one positive factor at the end therefore leaves the
branch against `dwz63PlainMarkedLossHashJoint`, a product of committed subexponential factors with
no `hashMult` in it.  Putting the factor in the loss instead would not be subexponential, so it is
not an option.  The final wrapper is the `4 |R|²` / Behrend form that
`dwz63_exists_seed_plainCopyCount_at_sharpDegree` consumes.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173.  The fixed-marginal count is
`papers/sources/2210.10173/hashing.tex:60-70` (`lem:numtriple_singledist` at `:63-70`), and its
use in the section 6.2 analysis is `papers/sources/2210.10173/global_value.tex:130-140,292-323`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u v

/-! ## The branch at the joint class -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch` in the retention-loss form, at the joint type class.**

The chain is run at `e ^ H(alpha_X)` rather than at the branch, so that the `hashMult ^ (n+1)` the
marginal-to-joint passage costs cancels against the `hashMult ^ -(n+1)` inside
`dwz63HashingBranch` instead of landing in the loss.  (`hashMult` is `dwz63HashLossMultiplier`;
`K` is the field type parameter.)

Proof sketch: multiply both sides by the positive `hashMult ^ (n+1)` (`le_of_mul_le_mul_right`)
and unfold the joint loss into its four factors.  A four-step `calc` then runs left to right:
`hbranchK` turns `dwz63HashingBranch ^ (n+1) * hashMult ^ (n+1)` into `e ^ (H(alpha_X)(n+1))`,
since `dwz63HashingBranch` is that exponential divided by `hashMult`; the committed X-marginal
Stirling bound `dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount` replaces it by
`loss_X * N_X`; the committed sharp-degree retention inequality
`dwz63_plainLegCount_mul_retentionLoss_le` replaces `N_X * retentionLoss` by
`125136 * behrendLoss * #(marginal family)`; and `dwz63_card_plainMarginalWords_le_marked` replaces
that cardinality by `typeCountLoss * hashMult ^ (n+1) * loss_alpha * #(joint class)`.  Each step is
a `mul_le_mul_of_nonneg_*` at an explicitly nonnegative factor, and the final `ring` regroups the
product so that the one `hashMult ^ (n+1)` sits on the right, where it is cancelled.  No
exponential loss is hidden: the only non-subexponential factor introduced is the one cancelled. -/
theorem dwz63_markedBranch_pow_mul_retentionLoss_le (K : Type u) [CommRing K] {n t : ℕ}
    (ht : 0 < t) (hn : n + 1 = 100000000 * t) :
    dwz63HashingBranch ^ (n + 1) * dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) ≤
      dwz63PlainMarkedLossHashJoint K (n + 1) *
        (((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ) := by
  have hdiv : (n + 1) / 100000000 = t := by omega
  have hKpos : (0 : ℝ) < dwz63HashLossMultiplier ^ (n + 1) :=
    pow_pos dwz63HashLossMultiplier_pos _
  have hlossEq : dwz63PlainMarkedLossHashJoint K (n + 1) =
      (125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
        WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
        WordType.typeCountLoss (Fin 15) (n + 1) *
        WordType.structuralZeroMultinomialLoss dwz63Alpha t := by
    unfold dwz63PlainMarkedLossHashJoint dwz63PlainMarkedLossHash dwz63PlainMarkedDegree
    rw [hdiv, show n + 1 - 1 = n from by omega]
  have hbranchK : Real.exp dwz63EntropyX ^ (n + 1) =
      dwz63HashingBranch ^ (n + 1) * dwz63HashLossMultiplier ^ (n + 1) := by
    rw [← mul_pow, dwz63HashingBranch, div_mul_cancel₀ _ dwz63HashLossMultiplier_pos.ne']
  have hretPos : (0 : ℝ) < dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) :=
    mul_pos (dwz63SharpModulusLoss_pos _) (dwz63SharpBehrendLoss_pos _)
  have hstirX : (0 : ℝ) ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t :=
    (WordType.structuralZeroMultinomialLoss_pos dwz63AlphaX t).le
  have hbeh : (0 : ℝ) ≤ 125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t) := by
    have := dwz63SharpBehrendLoss_pos (dwz63PlainSharpDegree K n t)
    positivity
  refine le_of_mul_le_mul_right ?_ hKpos
  rw [hlossEq]
  calc dwz63HashingBranch ^ (n + 1) *
        dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) *
        dwz63HashLossMultiplier ^ (n + 1)
      = Real.exp dwz63EntropyX ^ (n + 1) *
          dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) := by
        rw [hbranchK]; ring
    _ ≤ (WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
            ((dwz63PlainLegCount .X n t : ℕ) : ℝ)) *
          dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t) :=
        mul_le_mul_of_nonneg_right
          (dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount hn) hretPos.le
    _ = WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          (((dwz63PlainLegCount .X n t : ℕ) : ℝ) *
            dwz63SharpRetentionLoss (dwz63PlainSharpDegree K n t)) := by ring
    _ ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          ((125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
            (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (dwz63_plainLegCount_mul_retentionLoss_le K hn) hstirX
    _ ≤ WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          ((125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
            (WordType.typeCountLoss (Fin 15) (n + 1) * dwz63HashLossMultiplier ^ (n + 1) *
              WordType.structuralZeroMultinomialLoss dwz63Alpha t *
              (((dwz63MarkedWords n
                (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (dwz63_card_plainMarginalWords_le_marked K ht hn) hbeh)
          hstirX
    _ = (125136 * dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) *
          WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
          WordType.typeCountLoss (Fin 15) (n + 1) *
          WordType.structuralZeroMultinomialLoss dwz63Alpha t *
          (((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ) *
          dwz63HashLossMultiplier ^ (n + 1) := by ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch` at the joint class**, in the `4 |R|²` / Behrend form
`dwz63_exists_seed_plainCopyCount_at_sharpDegree` consumes.

Proof sketch: the modulus is bracketed from both sides --- below by the committed character floor
`15625 ≤ M`, above by `M ≤ 2(15625 + 8·degree + 1)` (`dwz63SharpHashModulus_le`) --- and
`M / 3 ≤ ⌊M / 2⌋` in the reals, so the Behrend hypothesis `hB`, whose exponential factor is by
`dwz63SharpBehrendLoss`'s definition exactly `behrendLoss⁻¹`, gives
`M / 3 * behrendLoss⁻¹ ≤ #B`.  `dwz63_markedBranch_pow_mul_retentionLoss_le`, with
`dwz63SharpRetentionLoss` and `dwz63SharpModulusLoss` unfolded, supplies the branch inequality
against `4 * (2(15625 + 8·degree + 1)) * behrendLoss`.  The committed arithmetic wrapper
`dwz63_plainHashBranch_arith` combines the two: it replaces `4 |R|²` --- `|R| = M` by `hcard` ---
by the upper bracket and trades `behrendLoss` for the factor `3 * #B`, keeping the direction. -/
theorem dwz63_markedHashBranch {R : Type v} [Field R] [Fintype R] (K : Type u) [CommRing K]
    {n t : ℕ} (ht : 0 < t) (hn : n + 1 = 100000000 * t)
    (hcard : Fintype.card R = dwz63SharpHashModulus (dwz63PlainSharpDegree K n t))
    (B : Finset R)
    (hB : ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ) *
        Real.exp (-4 * Real.sqrt (Real.log
          ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ))) ≤
      (B.card : ℝ)) :
    dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      dwz63PlainMarkedLossHashJoint K (n + 1) *
        (3 * (((dwz63MarkedWords n
          (WordType.proportionalCounts dwz63Alpha t)).card : ℝ)) * (B.card : ℝ)) := by
  have hMfloor : 15625 ≤ dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) :=
    dwz63SharpHashModulus_char_floor _
  have hMposNat : 0 < dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) := by omega
  have hMpos : (0 : ℝ) < (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) := by
    exact_mod_cast hMposNat
  have hUM : (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) ≤
      2 * (15625 + 8 * ((dwz63PlainSharpDegree K n t : ℕ) : ℝ) + 1) := by
    have hnat := dwz63SharpHashModulus_le (dwz63PlainSharpDegree K n t)
    have hcast : ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℕ) : ℝ) ≤
        ((2 * (15625 + 8 * dwz63PlainSharpDegree K n t + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hhalf : (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) / 3 ≤
      ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hnat : dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) ≤
        dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 * 3 := by omega
    exact_mod_cast hnat
  have hBehPos : (0 : ℝ) < dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t) :=
    dwz63SharpBehrendLoss_pos _
  have hinv : Real.exp (-4 * Real.sqrt (Real.log
        ((dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) / 2 : ℕ) : ℝ))) =
      (dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t))⁻¹ := by
    unfold dwz63SharpBehrendLoss
    rw [← Real.exp_neg]
    ring_nf
  have hBc : (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t) : ℝ) / 3 *
      (dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t))⁻¹ ≤ (B.card : ℝ) := by
    refine le_trans ?_ hB
    rw [← hinv]
    exact mul_le_mul_of_nonneg_right hhalf (Real.exp_nonneg _)
  have hstep : dwz63HashingBranch ^ (n + 1) *
      (4 * (2 * (15625 + 8 * ((dwz63PlainSharpDegree K n t : ℕ) : ℝ) + 1)) *
        dwz63SharpBehrendLoss (dwz63PlainSharpDegree K n t)) ≤
      dwz63PlainMarkedLossHashJoint K (n + 1) *
        (((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ) := by
    have h := dwz63_markedBranch_pow_mul_retentionLoss_le K ht hn
    unfold dwz63SharpRetentionLoss dwz63SharpModulusLoss at h
    exact h
  rw [hcard]
  exact dwz63_plainHashBranch_arith (pow_nonneg dwz63HashingBranch_pos.le _) hUM hMpos hBehPos
    (dwz63PlainMarkedLossHashJoint_nonneg K (n + 1)) (Nat.cast_nonneg _) hBc hstep

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hbranch` at the joint class, with the progression-free set produced.**

The exact shape of image 126's `hbranch` binder, at
`markedWords := dwz63MarkedWords n (proportionalCounts dwz63Alpha t)` and the enlarged loss. -/
theorem exists_behrend_dwz63_plainHashBranch_marked (K : Type u) [CommRing K] {n t : ℕ}
    (ht : 0 < t) (hn : n + 1 = 100000000 * t) :
    ∃ B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K n t)),
      ThreeAPFree (B : Set (dwz63SharpHashField (dwz63PlainSharpDegree K n t))) ∧
        dwz63HashingBranch ^ (n + 1) *
            (4 * ((Fintype.card (dwz63SharpHashField (dwz63PlainSharpDegree K n t)) : ℝ) *
              (Fintype.card (dwz63SharpHashField (dwz63PlainSharpDegree K n t)) : ℝ))) ≤
          dwz63PlainMarkedLossHashJoint K (n + 1) *
            (3 * (((dwz63MarkedWords n
              (WordType.proportionalCounts dwz63Alpha t)).card : ℝ)) * (B.card : ℝ)) := by
  obtain ⟨B, hfree, hcard⟩ :=
    exists_threeAPFree_zmod_half_behrend (dwz63SharpHashModulus (dwz63PlainSharpDegree K n t))
  exact ⟨B, hfree, dwz63_markedHashBranch K ht hn (card_dwz63SharpHashField _) B hcard⟩

end AlgebraicComplexity.Examples
