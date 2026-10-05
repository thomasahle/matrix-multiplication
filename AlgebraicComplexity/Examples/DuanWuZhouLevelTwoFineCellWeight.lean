/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellFusion
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoConstituentValues
import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue
import AlgebraicComplexity.Tensor.PermutationCoherence

set_option autoImplicit false

/-!
# The `tau`-weight of one fused fine cell

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/DuanWuZhouLevelTwoFineCellFusion.lean` delivers an **exact restriction** of one
zero-coordinate cell of the `[duan2023faster]` section 6.3 fine leaf onto
`⟨1, |fibre| * q ^ k, 1⟩`.  Everything downstream of it --- the segment product, and the
comparison
with `exp dwz63LogVal` --- speaks `HasTauWeight`, not `Restricts`.  This module is that one step,
and only that step: the fibre cardinality stays symbolic, so no counting enters here.

## Why the value is `(|fibre| * q ^ k) ^ tau` and not the cell's published value

They are different statements and the difference is the whole point of the fine route.  For the
*coarse* constituent the published value is already committed without any counting ---
`dwz63_hasTauWeight_022` reaches `dwz63Val022` through the plain `⟨1,1,q^2+2⟩` restriction of
`T_{0,2,2}`, because `dwz63Val022 <= dwz63Val220 = 38 ^ tau` (`dwz63_val022_le_val220`, a Gibbs
comparison with about `0.002` nats of room).  Inside the **fine** leaf that route is unavailable:
the leaf is a fibre of fine words, a single one of which carries only `q ^ (2 tau)` = `36 ^ tau`
per letter, strictly below `dwz63Val022`.  The missing factor is exactly the fibre cardinality,
which is why the fusion --- and not a single-constituent extraction --- is what the localized leaf
needs.  Turning `|fibre|` into the multinomial, and the multinomial into the entropy rate, is a
separate obligation and is deliberately not attempted here.

## Two frames

The fusion concludes in the rotated frame, as the committed orientation discipline requires.
`dwz63_hasTauWeight_permuted_fineCellPower` stays there.  `dwz63_hasTauWeight_fineCellPower`
rotates back, which costs nothing: `HasTauWeight.permute`
(`MatrixMultiplication/SixSymmetrizedValue.lean`) is invariance under an arbitrary leg
permutation, and `Tensor.Isomorphic.cancel_permute_symm_left`
(`Tensor/PermutationCoherence.lean`) cancels the two rotations.  The cancellation is stated as an
isomorphism rather than an equation because the two ambient leg families,
`fun i => V (e.symm (e i))` and `V`, are propositionally but not definitionally equal.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **The `tau`-weight of one fused fine cell, in the rotated frame.**

The fusion's `⟨1, N, 1⟩` with `N = |fibre| * q ^ k`, read as a weight.  The only extra
hypothesis
is that the fibre is inhabited, which `hasTauWeight_matrixMultiplication` needs for the middle
dimension. -/
theorem dwz63_hasTauWeight_permuted_fineCellPower (zero : Leg) (n k : ℕ) (τ : ℝ)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c a, Decidable (keep c a)]
    (hq : 0 < q)
    (hne : ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
      keep).support.Nonempty)
    (hzero : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n)
    (hones : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      dwz63CellOnes zero n s = k) :
    HasTauWeight K
      (Tensor.permute (zeroOrientation zero)
        ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep).realize) τ
      (((((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support.card * q ^ k : ℕ) : ℝ) ^ τ) := by
  classical
  have hcard : 0 < ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
      keep).support.card := Finset.card_pos.mpr hne
  have hpow : 0 < q ^ k := Nat.pow_pos hq
  have hmm := hasTauWeight_matrixMultiplication (K := K)
    (a := 1)
    (b := ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
      keep).support.card * q ^ k)
    (c := 1) Nat.one_pos (Nat.mul_pos hcard hpow) Nat.one_pos τ
  rw [show (1 * (((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
      keep).support.card * q ^ k) * 1) =
      ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support.card * q ^ k from by ring] at hmm
  exact hmm.of_restricts
    (dwz63_fineCellPower_restricts_matrixMultiplication K q zero n k keep hzero hones)

/-- **The `tau`-weight of one fused fine cell, unrotated.**

The frame the segment product and the `sym₆` step work in.  `HasTauWeight.permute` at the inverse
orientation costs nothing, because a `tau`-weight is invariant under every leg permutation. -/
theorem dwz63_hasTauWeight_fineCellPower (zero : Leg) (n k : ℕ) (τ : ℝ)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c a, Decidable (keep c a)]
    (hq : 0 < q)
    (hne : ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
      keep).support.Nonempty)
    (hzero : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n)
    (hones : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      dwz63CellOnes zero n s = k) :
    HasTauWeight K
      ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep).realize τ
      (((((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support.card * q ^ k : ℕ) : ℝ) ^ τ) := by
  have hrot := (dwz63_hasTauWeight_permuted_fineCellPower K q zero n k τ keep hq hne hzero
    hones).permute (zeroOrientation zero).symm
  exact hrot.of_restricts
    (Tensor.Isomorphic.cancel_permute_symm_left (zeroOrientation zero) _).symm.restricts

end AlgebraicComplexity.Examples
