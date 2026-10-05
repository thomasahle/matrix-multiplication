/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedRate

/-!
# Subexponentiality of the marked-count loss

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoMarkedRate.lean` supplies
the integration's `hrate` with `lossHash n = 125136 * dwz63SharpBehrendLoss (degree n)`.  This
module discharges the remaining side condition, `Growth.Subexponential lossHash`.

Only the Behrend factor is live: `dwz63SharpBehrendLoss d = exp (4 √(log (M d / 2)))` with
`M d ≤ 2 (15625 + 8 d + 1)`, so its logarithm is linear in `log d` and the whole factor is
`exp (O (√n))` whenever the degree sequence is at most exponential.  Nothing is re-derived: the
committed `Growth.sqrt_log_le_mul_sqrt_succ` turns `√(log x)` into `s √(n+1)` from a geometric
bound on `x`, `Growth.Subexponential.exp_mul_sqrt_succ` gives subexponentiality of the resulting
square-root exponential, and `Growth.Subexponential.mono` and `.const_mul` carry it to the loss
itself and to its constant multiple.

`subexponential_dwz63MarkedLossHash` is the usable form: any degree sequence bounded by
`11390625 ^ (n+1) + 1` --- and `dwz63SharpDegree` of any two counts of block words is, since a
count of block words never exceeds `11390625 ^ (n+1)` --- gives a subexponential `lossHash`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

universe u

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The Behrend factor along an at-most-geometric degree sequence is subexponential.**  The
hypotheses are exactly those of the committed `Growth.sqrt_log_le_mul_sqrt_succ`. -/
theorem subexponential_dwz63SharpBehrendLoss (degree : ℕ → ℕ) {c G s : ℝ} {m : ℕ}
    (hc : 0 < c) (hG : 0 < G) (hs : 0 ≤ s) (hcs : c ≤ s ^ 2) (hGs : (m : ℝ) * G ≤ s ^ 2)
    (hbound : ∀ n : ℕ,
      ((dwz63SharpHashModulus (degree n) / 2 : ℕ) : ℝ) ≤ c * G ^ (m * n)) :
    Growth.Subexponential (fun n ↦ dwz63SharpBehrendLoss (degree n)) := by
  refine Growth.Subexponential.mono
    (Growth.Subexponential.exp_mul_sqrt_succ (a := 4 * s) (by positivity))
    (fun _ ↦ (dwz63SharpBehrendLoss_pos _).le) (fun n ↦ ?_)
  have hpos : 0 < dwz63SharpHashModulus (degree n) / 2 := by
    have h1 : 15625 ≤ dwz63SharpHashModulus (degree n) :=
      dwz63SharpHashModulus_char_floor (degree n)
    omega
  have hx : (0 : ℝ) < ((dwz63SharpHashModulus (degree n) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hpos
  have hsqrt := Growth.sqrt_log_le_mul_sqrt_succ (m := m) (k := n)
    hx hc hG hs (hbound n) hcs hGs
  unfold dwz63SharpBehrendLoss
  refine Real.exp_le_exp.mpr ?_
  calc 4 * Real.sqrt (Real.log ((dwz63SharpHashModulus (degree n) / 2 : ℕ) : ℝ))
      ≤ 4 * (s * Real.sqrt (((n + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = (4 * s) * Real.sqrt (((n + 1 : ℕ) : ℝ)) := by ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The marked-count loss is subexponential.**

Any degree sequence bounded by `11390625 ^ (n+1) + 1` --- in particular `dwz63SharpDegree` of any
two block-word counts --- gives a subexponential `lossHash`.  The constants are
`c = 91140634`, `G = 11390625`, `m = 1`, `s = 9550`; only `c ≤ s²` and `G ≤ s²` are needed of
them. -/
theorem subexponential_dwz63MarkedLossHash (degree : ℕ → ℕ)
    (hdeg : ∀ n : ℕ, degree n ≤ 11390625 ^ (n + 1) + 1) :
    Growth.Subexponential (fun n ↦ 125136 * dwz63SharpBehrendLoss (degree n)) := by
  refine Growth.Subexponential.const_mul ?_ (by norm_num)
  refine subexponential_dwz63SharpBehrendLoss degree
    (c := 91140634) (G := 11390625) (s := 9550) (m := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro n
  have hM : dwz63SharpHashModulus (degree n) / 2 ≤ 15626 + 8 * degree n := by
    have h := dwz63SharpHashModulus_le (degree n)
    omega
  have hone : (1 : ℕ) ≤ 11390625 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hnat : dwz63SharpHashModulus (degree n) / 2 ≤ 91140634 * 11390625 ^ n := by
    calc dwz63SharpHashModulus (degree n) / 2
        ≤ 15626 + 8 * degree n := hM
      _ ≤ 15626 + 8 * (11390625 ^ (n + 1) + 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 8 (hdeg n)) _
      _ = 15634 + 91125000 * 11390625 ^ n := by rw [pow_succ]; ring
      _ ≤ 15634 * 11390625 ^ n + 91125000 * 11390625 ^ n :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_right 15634 (by omega)) _
      _ = 91140634 * 11390625 ^ n := by ring
  have hcast : ((dwz63SharpHashModulus (degree n) / 2 : ℕ) : ℝ) ≤
      91140634 * (11390625 : ℝ) ^ n := by exact_mod_cast hnat
  simpa [one_mul] using hcast

end AlgebraicComplexity.Examples
