/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Asymptotics

/-!
# Subexponential losses

This module packages the elementary rate argument used after finite tensor extractions.  A
nonnegative real sequence is subexponential when it is bounded by `C * delta ^ n` for every
`delta > 1`.  Polynomial factors and `exp (a * sqrt (n + 1))` are the two recurring examples in
type counting and progression-free hashing.

The predicate `Growth.Subexponential` itself is defined in the Mathlib-only layer-0 module
`AlgebraicComplexity/Asymptotics.lean`; this file supplies its closure calculus and standard
witnesses.

`sqrt_log_le_mul_sqrt_succ` is the elementary companion of `Subexponential.exp_mul_sqrt_succ`: it
bounds `√(log x)` by `s * √(k + 1)` for a quantity `x` growing at most like `c * G ^ (m * k)`, and
is what puts a Behrend-style loss `exp (4 * √(log x))` into that subexponential form.  Its clients
are the progression-free hashing rate arguments of `Analysis/BehrendRate.lean` and the CW hashing
examples; it mentions no progression-free set itself.
-/

namespace AlgebraicComplexity.Growth

namespace Subexponential

theorem nonneg {a : ℕ → ℝ} (ha : Subexponential a) (n : ℕ) : 0 ≤ a n :=
  ha.1 n

/-- A nonnegative sequence pointwise dominated by a subexponential sequence is
subexponential. -/
theorem mono {a b : ℕ → ℝ} (hb : Subexponential b)
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n) : Subexponential a := by
  refine ⟨ha, ?_⟩
  intro δ hδ
  obtain ⟨C, hC, hbC⟩ := hb.2 δ hδ
  exact ⟨C, hC, fun n ↦ (hab n).trans (hbC n)⟩

/-- Pointwise products of subexponential nonnegative sequences are subexponential. -/
theorem mul {a b : ℕ → ℝ} (ha : Subexponential a) (hb : Subexponential b) :
    Subexponential (fun n ↦ a n * b n) := by
  refine ⟨fun n ↦ mul_nonneg (ha.nonneg n) (hb.nonneg n), ?_⟩
  intro δ hδ
  let γ := √δ
  have hδpos : 0 < δ := zero_lt_one.trans hδ
  have hγ : 1 < γ := by
    dsimp [γ]
    rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff zero_le_one]
    exact hδ
  obtain ⟨C, hC, haC⟩ := ha.2 γ hγ
  obtain ⟨D, hD, hbD⟩ := hb.2 γ hγ
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro n
  calc
    a n * b n ≤ (C * γ ^ n) * (D * γ ^ n) :=
      mul_le_mul (haC n) (hbD n) (hb.nonneg n)
        (mul_nonneg hC.le (pow_nonneg (Real.sqrt_nonneg _) _))
    _ = (C * D) * δ ^ n := by
      calc
        (C * γ ^ n) * (D * γ ^ n) = (C * D) * (γ ^ n * γ ^ n) := by ring
        _ = (C * D) * (γ * γ) ^ n := by rw [mul_pow]
        _ = (C * D) * δ ^ n := by rw [Real.mul_self_sqrt hδpos.le]

/-- Every fixed nonnegative sequence is subexponential. -/
theorem const {c : ℝ} (hc : 0 ≤ c) :
    Subexponential (fun _ : ℕ ↦ c) := by
  refine ⟨fun _ ↦ hc, ?_⟩
  intro delta hdelta
  refine ⟨c + 1, by linarith, ?_⟩
  intro n
  have hpow : 1 ≤ delta ^ n := one_le_pow₀ hdelta.le
  calc
    c ≤ (c + 1) * 1 := by
      simpa only [mul_one] using
        (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num) : c ≤ c + 1)
    _ ≤ (c + 1) * delta ^ n :=
      mul_le_mul_of_nonneg_left hpow (add_nonneg hc zero_le_one)

/-- Pointwise sums of subexponential nonnegative sequences are subexponential. -/
theorem add {a b : ℕ → ℝ} (ha : Subexponential a) (hb : Subexponential b) :
    Subexponential (fun n ↦ a n + b n) := by
  refine ⟨fun n ↦ add_nonneg (ha.nonneg n) (hb.nonneg n), ?_⟩
  intro delta hdelta
  obtain ⟨C, hC, haC⟩ := ha.2 delta hdelta
  obtain ⟨D, hD, hbD⟩ := hb.2 delta hdelta
  refine ⟨C + D, add_pos hC hD, ?_⟩
  intro n
  calc
    a n + b n ≤ C * delta ^ n + D * delta ^ n := add_le_add (haC n) (hbD n)
    _ = (C + D) * delta ^ n := by ring

/-- A finite pointwise sum of subexponential losses is subexponential. -/
theorem finset_sum {I : Type*} [DecidableEq I]
    (s : Finset I) (a : I → ℕ → ℝ)
    (ha : ∀ i ∈ s, Subexponential (a i)) :
    Subexponential (fun n ↦ ∑ i ∈ s, a i n) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (const (c := (0 : ℝ)) (by norm_num))
  | @insert i s hi ih =>
      have hleft : Subexponential (a i) := ha i (Finset.mem_insert_self i s)
      have hright : Subexponential (fun n ↦ ∑ j ∈ s, a j n) :=
        ih fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert, hi] using hleft.add hright

/-- Fintype-indexed form of `finset_sum`. -/
theorem fintype_sum {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ → ℝ) (ha : ∀ i, Subexponential (a i)) :
    Subexponential (fun n ↦ ∑ i, a i n) := by
  simpa using finset_sum (Finset.univ : Finset I) a (fun i _ ↦ ha i)

/-- A finite pointwise product of subexponential losses is subexponential.  This is the closure
used to combine the fixed collection of type-counting, hashing, and repair losses in a recursive
laser certificate. -/
theorem finset_prod {I : Type*} [DecidableEq I]
    (s : Finset I) (a : I → ℕ → ℝ)
    (ha : ∀ i ∈ s, Subexponential (a i)) :
    Subexponential (fun n ↦ ∏ i ∈ s, a i n) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (const (c := (1 : ℝ)) (by norm_num))
  | @insert i s hi ih =>
      have hleft : Subexponential (a i) := ha i (Finset.mem_insert_self i s)
      have hright : Subexponential (fun n ↦ ∏ j ∈ s, a j n) :=
        ih fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
      simpa [Finset.prod_insert, hi] using hleft.mul hright

/-- Fintype-indexed form of `finset_prod`. -/
theorem fintype_prod {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ → ℝ) (ha : ∀ i, Subexponential (a i)) :
    Subexponential (fun n ↦ ∏ i, a i n) := by
  simpa using finset_prod (Finset.univ : Finset I) a (fun i _ ↦ ha i)

/-- Multiplication by a fixed nonnegative constant preserves subexponential growth. -/
theorem const_mul {a : ℕ → ℝ} (ha : Subexponential a) {c : ℝ} (hc : 0 ≤ c) :
    Subexponential (fun n ↦ c * a n) := by
  refine ⟨fun n ↦ mul_nonneg hc (ha.nonneg n), ?_⟩
  intro δ hδ
  obtain ⟨C, hC, haC⟩ := ha.2 δ hδ
  refine ⟨(c + 1) * C, mul_pos (by linarith) hC, ?_⟩
  intro n
  calc
    c * a n ≤ c * (C * δ ^ n) := mul_le_mul_of_nonneg_left (haC n) hc
    _ ≤ (c + 1) * C * δ ^ n := by
      have hpow : 0 ≤ δ ^ n := pow_nonneg (zero_lt_one.trans hδ).le _
      nlinarith [mul_nonneg hC.le hpow]

/-- Natural powers, viewed as real sequences, are subexponential. -/
theorem natCast_pow (d : ℕ) : Subexponential (fun n ↦ (n : ℝ) ^ d) := by
  refine ⟨fun n ↦ pow_nonneg (Nat.cast_nonneg n) d, ?_⟩
  intro δ hδ
  exact ExponentialBound.exists_const_mul_pow_ge_polynomial d hδ

/-- A fixed power of `n + 1` is subexponential.  This shifted form is the natural loss in
finite-alphabet method-of-types estimates. -/
theorem natCast_succ_pow (d : ℕ) :
    Subexponential (fun n ↦ (((n + 1 : ℕ) : ℝ)) ^ d) := by
  refine ⟨fun n ↦ pow_nonneg (Nat.cast_nonneg (n + 1)) d, ?_⟩
  intro δ hδ
  obtain ⟨C, hC, hbound⟩ := (natCast_pow d).2 δ hδ
  have hδpos : 0 < δ := zero_lt_one.trans hδ
  refine ⟨C * δ, mul_pos hC hδpos, ?_⟩
  intro n
  calc
    (((n + 1 : ℕ) : ℝ)) ^ d ≤ C * δ ^ (n + 1) := hbound (n + 1)
    _ = (C * δ) * δ ^ n := by rw [pow_succ]; ring

/-- The tangent-line estimate for the concave square-root function, in the form used to
compare `exp (a * sqrt x)` with a geometric sequence. -/
theorem sqrt_le_mul_add_inv {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    √x ≤ s * x + 1 / (4 * s) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hsne : s ≠ 0 := hs.ne'
    have hid : (s * x + 1 / (4 * s)) ^ 2 - x =
        (s * x - 1 / (4 * s)) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (s * x - 1 / (4 * s))]

/-- A square-root exponential loss is subexponential. -/
theorem exp_mul_sqrt_succ {a : ℝ} (ha : 0 ≤ a) :
    Subexponential (fun n ↦ Real.exp (a * √((n + 1 : ℕ) : ℝ))) := by
  refine ⟨fun _ ↦ Real.exp_nonneg _, ?_⟩
  intro δ hδ
  have hδpos : 0 < δ := zero_lt_one.trans hδ
  have hlogδ : 0 < Real.log δ := Real.log_pos hδ
  by_cases ha0 : a = 0
  · subst a
    refine ⟨1, zero_lt_one, ?_⟩
    intro n
    simp only [zero_mul, Real.exp_zero, one_mul]
    exact one_le_pow₀ hδ.le
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let s : ℝ := Real.log δ / a
    have hs : 0 < s := div_pos hlogδ hapos
    let C : ℝ := Real.exp (Real.log δ + a / (4 * s))
    refine ⟨C, Real.exp_pos _, ?_⟩
    intro n
    have hx : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
    have hsqrt := sqrt_le_mul_add_inv hx hs
    have hexponent :
        a * √(((n + 1 : ℕ) : ℝ)) ≤
          (n : ℝ) * Real.log δ + (Real.log δ + a / (4 * s)) := by
      apply (mul_le_mul_of_nonneg_left hsqrt ha).trans_eq
      push_cast
      dsimp [s]
      field_simp
      ring
    calc
      Real.exp (a * √(((n + 1 : ℕ) : ℝ))) ≤
          Real.exp ((n : ℝ) * Real.log δ +
            (Real.log δ + a / (4 * s))) := Real.exp_le_exp.mpr hexponent
      _ = C * δ ^ n := by
        dsimp [C]
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hδpos]
        ring

/-- An `exp (a n / log n)` repair loss is subexponential.

The shift by two keeps the denominator strictly positive at every natural index.  This is the
rate appearing in recursive hole repair: a seven-branch tree of depth `O(n / log n)` costs only
`exp (O(n / log n))` copies and therefore does not affect an asymptotic tensor exponent. -/
theorem exp_mul_natCast_div_log_add_two {a : ℝ} (ha : 0 ≤ a) :
    Subexponential
      (fun n ↦ Real.exp (a * (n : ℝ) /
        Real.log (((n + 2 : ℕ) : ℝ)))) := by
  refine ⟨fun _ ↦ Real.exp_nonneg _, ?_⟩
  intro δ hδ
  have hδpos : 0 < δ := zero_lt_one.trans hδ
  have hlogδ : 0 < Real.log δ := Real.log_pos hδ
  have htend :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.log (((n + 2 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      a / Real.log (((n + 2 : ℕ) : ℝ)) ≤ Real.log δ := by
    have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
        a / Real.log δ ≤ Real.log (((n + 2 : ℕ) : ℝ)) :=
      htend.eventually (Filter.eventually_ge_atTop (a / Real.log δ))
    filter_upwards [hlarge] with n hn
    have hdenPos : 0 < Real.log (((n + 2 : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n + 2 by omega)
    apply (div_le_iff₀ hdenPos).2
    have haBound : a ≤ Real.log (((n + 2 : ℕ) : ℝ)) * Real.log δ :=
      (div_le_iff₀ hlogδ).1 hn
    simpa only [mul_comm] using haBound
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let C : ℝ := Real.exp (a * (N : ℝ) / Real.log 2)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hC : 0 < C := Real.exp_pos _
  have honeC : 1 ≤ C := by
    apply Real.one_le_exp
    exact div_nonneg (mul_nonneg ha (Nat.cast_nonneg N)) hlogTwo.le
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hcoefficient := hN n hn
    have hexponent :
        a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ)) ≤
          (n : ℝ) * Real.log δ := by
      calc
        a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ)) =
            (a / Real.log (((n + 2 : ℕ) : ℝ))) * (n : ℝ) := by ring
        _ ≤ Real.log δ * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg n)
        _ = (n : ℝ) * Real.log δ := mul_comm _ _
    calc
      Real.exp (a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ))) ≤
          Real.exp ((n : ℝ) * Real.log δ) := Real.exp_le_exp.mpr hexponent
      _ = δ ^ n := by rw [Real.exp_nat_mul, Real.exp_log hδpos]
      _ ≤ C * δ ^ n := by
        exact le_mul_of_one_le_left (pow_nonneg hδpos.le n) honeC
  · have hnN : n ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hcast : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ n + 2 by omega)
    have hden : Real.log 2 ≤ Real.log (((n + 2 : ℕ) : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn
        (show 0 < (2 : ℝ) by norm_num)
        (show 0 < ((n + 2 : ℕ) : ℝ) by positivity) hcast
    have hnum : a * (n : ℝ) ≤ a * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) ha
    have hexponent :
        a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ)) ≤
          a * (N : ℝ) / Real.log 2 :=
      div_le_div₀ (mul_nonneg ha (Nat.cast_nonneg N)) hnum hlogTwo hden
    calc
      Real.exp (a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ))) ≤ C := by
        exact Real.exp_le_exp.mpr hexponent
      _ ≤ C * δ ^ n := by
        exact le_mul_of_one_le_right hC.le (one_le_pow₀ hδ.le)

/-- The standard product of a constant, a polynomial, and a square-root exponential is
subexponential. -/
theorem const_mul_natCast_pow_mul_exp_sqrt_succ
    {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (d : ℕ) :
    Subexponential
      (fun n ↦ c * (n : ℝ) ^ d * Real.exp (a * √((n + 1 : ℕ) : ℝ))) := by
  simpa only [mul_assoc] using
    ((natCast_pow d).mul (exp_mul_sqrt_succ ha)).const_mul hc

/-- **A subexponential sequence is eventually below every exponential of base `> 1`, with no
constant left over.**  The definition of `Subexponential` allows a base-dependent constant `C`; for
a rate argument that needs a clean inequality `a k ≤ δ ^ k` the constant can be absorbed by waiting
long enough.

Proof sketch: apply the definition at the smaller base `√δ`, which is still `> 1`, obtaining
`a n ≤ C * √δ ^ n`.  Since `√δ > 1`, some power `√δ ^ N` exceeds `C`, and for `k ≥ N`
`C * √δ ^ k ≤ √δ ^ k * √δ ^ k = δ ^ k`. -/
theorem eventually_le_pow {a : ℕ → ℝ} (ha : Subexponential a) {δ : ℝ} (hδ : 1 < δ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → a k ≤ δ ^ k := by
  have hδ0 : (0 : ℝ) ≤ δ := (zero_lt_one.trans hδ).le
  set γ : ℝ := √δ with hγdef
  have hγ1 : 1 < γ := by
    rw [hγdef, show (1 : ℝ) = √1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt zero_le_one hδ
  have hγγ : γ * γ = δ := Real.mul_self_sqrt hδ0
  obtain ⟨C, hC, haC⟩ := ha.2 γ hγ1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C < γ ^ N := pow_unbounded_of_one_lt C hγ1
  refine ⟨N, fun k hk ↦ ?_⟩
  have hstep : C * γ ^ k ≤ γ ^ k * γ ^ k := by
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (zero_lt_one.trans hγ1).le k)
    exact hN.le.trans (pow_le_pow_right₀ hγ1.le hk)
  calc a k ≤ C * γ ^ k := haC k
    _ ≤ γ ^ k * γ ^ k := hstep
    _ = δ ^ k := by rw [← mul_pow, hγγ]

end Subexponential

/-- A quantity growing at most like `c * G ^ (m * k)` has `√(log ·)` bounded by `s * √(k + 1)`
as soon as `c` and `m * G` are bounded by `s ^ 2`.

This is the companion of `Subexponential.exp_mul_sqrt_succ`: it is what turns a Behrend-style loss
`exp (4 * √(log x))` into the subexponential sequence `exp (4 * s * √(k + 1))` when `x` is a
modulus growing geometrically in `k`.  Only the crude estimate `log y ≤ y - 1` is used, so the
hypotheses are stated on `c` and `G` themselves rather than on their logarithms. -/
theorem sqrt_log_le_mul_sqrt_succ {x c G s : ℝ} {m k : ℕ}
    (hx : 0 < x) (hc : 0 < c) (hG : 0 < G) (hs : 0 ≤ s)
    (hxb : x ≤ c * G ^ (m * k))
    (hcs : c ≤ s ^ 2) (hGs : (m : ℝ) * G ≤ s ^ 2) :
    √(Real.log x) ≤ s * √(((k + 1 : ℕ) : ℝ)) := by
  have hlog : Real.log x ≤ s ^ 2 * ((k : ℝ) + 1) := by
    have hle : Real.log x ≤ Real.log (c * G ^ (m * k)) := Real.log_le_log hx hxb
    have hsplit : Real.log (c * G ^ (m * k)) =
        Real.log c + ((m * k : ℕ) : ℝ) * Real.log G := by
      rw [Real.log_mul hc.ne' (by positivity), Real.log_pow]
    have hlc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc
    have hlG : Real.log G ≤ G - 1 := Real.log_le_sub_one_of_pos hG
    have hmk : (0 : ℝ) ≤ (m : ℝ) * (k : ℝ) := by positivity
    have hstep : ((m * k : ℕ) : ℝ) * Real.log G ≤ (m : ℝ) * (k : ℝ) * (G - 1) := by
      push_cast
      exact mul_le_mul_of_nonneg_left hlG hmk
    have hmG : (m : ℝ) * (G - 1) ≤ s ^ 2 := by
      refine le_trans ?_ hGs
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    have hshrink : (m : ℝ) * (k : ℝ) * (G - 1) ≤ s ^ 2 * (k : ℝ) := by
      have := mul_le_mul_of_nonneg_right hmG (Nat.cast_nonneg (α := ℝ) k)
      nlinarith
    nlinarith
  calc
    √(Real.log x) ≤ √(s ^ 2 * ((k : ℝ) + 1)) := Real.sqrt_le_sqrt hlog
    _ = s * √(((k + 1 : ℕ) : ℝ)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs]
      push_cast
      ring_nf

/-- A subexponential multiplicative loss can be removed from inequalities between all positive
powers.  This is the rate-level replacement for taking explicit `n`th roots and limits. -/
theorem le_of_pow_succ_le_subexponential_mul_pow_succ
    {b ρ : ℝ} {loss : ℕ → ℝ}
    (hρ : 0 ≤ ρ) (hloss : Subexponential loss)
    (h : ∀ n : ℕ, b ^ (n + 1) ≤ loss (n + 1) * ρ ^ (n + 1)) :
    b ≤ ρ := by
  by_cases hρzero : ρ = 0
  · subst ρ
    have hzero := h 0
    norm_num at hzero
    exact hzero
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρzero)
    by_contra hnot
    have hρb : ρ < b := lt_of_not_ge hnot
    let δ : ℝ := (b / ρ + 1) / 2
    have hratio : 1 < b / ρ := (lt_div_iff₀ hρpos).mpr (by simpa using hρb)
    have hδ : 1 < δ := by dsimp [δ]; linarith
    have hρδb : ρ * δ < b := by
      have hδratio : δ < b / ρ := by dsimp [δ]; linarith
      exact (mul_lt_mul_of_pos_left hδratio hρpos).trans_eq (by field_simp)
    obtain ⟨C, _hC, hlossC⟩ := hloss.2 δ hδ
    have hbound : ∀ n : ℕ,
        b ^ (n + 1) ≤ C * (ρ * δ) ^ (n + 1) := by
      intro n
      calc
        b ^ (n + 1) ≤ loss (n + 1) * ρ ^ (n + 1) := h n
        _ ≤ (C * δ ^ (n + 1)) * ρ ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (hlossC (n + 1)) (pow_nonneg hρ _)
        _ = C * (ρ * δ) ^ (n + 1) := by rw [mul_pow]; ring
    have hle : b ≤ ρ * δ :=
      le_of_pow_succ_le_const_mul_pow_succ
        (mul_nonneg hρ (zero_lt_one.trans hδ).le) hbound
    exact (not_le_of_gt hρδb) hle

end AlgebraicComplexity.Growth
