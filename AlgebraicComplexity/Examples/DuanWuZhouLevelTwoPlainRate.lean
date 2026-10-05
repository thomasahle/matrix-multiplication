/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFiberCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedLossHash

set_option autoImplicit false

/-!
# The rate at the plain partition: the lossy branch, and its loss

Layer 4 (`AlgebraicComplexity/Examples/`).  On the plain route the `K` of
`dwz63HashLossMultiplier` is again the only unit of slack, and it is claimed by the
joint-versus-marginal entropy gap: the ambient a legwise `select` reaches is
`dwz63PlainMarginalWords`, whose count exceeds the joint typical count by at most `K` per
position (the committed Gibbs deficit certificate).  The method-of-types Stirling loss therefore
cannot also be paid out of `K`, and must be carried in `lossHash`.

So the branch bound to use is the **lossy** form
`WordType.two_rpow_profileEntropyBits_pow_le_structuralZeroLoss_mul_card_typeClass`, stated here
at the full marginal rate `ᾱ_X = exp dwz63EntropyX` rather than at `dwz63HashingBranch`:

`(exp dwz63EntropyX) ^ (n+1) ≤ structuralZeroMultinomialLoss dwz63AlphaX t * N_X`.

Dividing by `K ^ (n+1)` on the left leaves exactly the slack the Gibbs deficit needs, and the
Stirling factor is subexponential by the committed
`WordType.structuralZeroMultinomialLoss_subexponential`.

The contrast with `Examples/DuanWuZhouLevelTwoHashingBranchRate.lean` is deliberate: that module's
`dwz63_hashingBranch_pow_le_dwz63XTypicalCount` is loss-free, but it buys that by spending `K` on
the Stirling loss, which the plain route cannot afford.  Both are true; only this one composes.

`subexponential_dwz63PlainLossHash` re-instantiates the generic
`subexponential_dwz63SharpBehrendLoss` at the plain radix: the degree is bounded by
`15 ^ (n+1) + 1` rather than `11390625 ^ (n+1) + 1`, so the constants become `c = 15754`,
`G = 15`, `m = 1`, `s = 126`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The lossy branch bound at the plain partition.**

The full `X` marginal rate is attained by `N_X` up to the named Stirling loss, with no use of the
hash-loss multiplier --- leaving `K` free for the joint-versus-marginal gap. -/
theorem dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    Real.exp dwz63EntropyX ^ (n + 1) ≤
      WordType.structuralZeroMultinomialLoss dwz63AlphaX t *
        ((dwz63PlainLegCount .X n t : ℕ) : ℝ) := by
  have hmass : 0 < WordType.profileMass dwz63AlphaX := by
    rw [profileMass_dwz63AlphaX]; norm_num
  have h := WordType.two_rpow_profileEntropyBits_pow_le_structuralZeroLoss_mul_card_typeClass
    dwz63AlphaX hmass t
  rw [WordType.two_rpow_mul_profileEntropyBits, profileMass_dwz63AlphaX,
    profileEntropyNats_dwz63AlphaX, Real.exp_nat_mul] at h
  rw [dwz63PlainLegCount, show dwz63AlphaMarginal .X = dwz63AlphaX from rfl, hn, pow_mul]
  exact h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The plain-radix loss is subexponential.**  Same proof as at the six-orientation radix; only
the constants move, because `subexponential_dwz63SharpBehrendLoss` takes them as parameters. -/
theorem subexponential_dwz63PlainLossHash (degree : ℕ → ℕ)
    (hdeg : ∀ n : ℕ, degree n ≤ 15 ^ (n + 1) + 1) :
    Growth.Subexponential (fun n ↦ 125136 * dwz63SharpBehrendLoss (degree n)) := by
  refine Growth.Subexponential.const_mul ?_ (by norm_num)
  refine subexponential_dwz63SharpBehrendLoss degree
    (c := 15754) (G := 15) (s := 126) (m := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro n
  have hM : dwz63SharpHashModulus (degree n) / 2 ≤ 15626 + 8 * degree n := by
    have h := dwz63SharpHashModulus_le (degree n)
    omega
  have hnat : dwz63SharpHashModulus (degree n) / 2 ≤ 15754 * 15 ^ n := by
    calc dwz63SharpHashModulus (degree n) / 2
        ≤ 15626 + 8 * degree n := hM
      _ ≤ 15626 + 8 * (15 ^ (n + 1) + 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 8 (hdeg n)) _
      _ = 15634 + 120 * 15 ^ n := by rw [pow_succ]; ring
      _ ≤ 15634 * 15 ^ n + 120 * 15 ^ n :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_right 15634 (by positivity)) _
      _ = 15754 * 15 ^ n := by ring
  have hcast : ((dwz63SharpHashModulus (degree n) / 2 : ℕ) : ℝ) ≤ 15754 * (15 : ℝ) ^ n := by
    exact_mod_cast hnat
  simpa [one_mul] using hcast

end AlgebraicComplexity.Examples
