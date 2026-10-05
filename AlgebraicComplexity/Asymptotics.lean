/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.AsymptoticsDefs
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

/-!
# Growth rates for discrete sequences

This module provides the layer-0 analytic interface used by asymptotic tensor rank and the
matrix-multiplication exponent. It also defines `Subexponential` for nonnegative real-valued
sequences; the closure and concrete-example library remains in
`Analysis/Subexponential.lean`. Its main limit theory has two halves.

* **Constant-tolerant bounds.**  `ExponentialBound a ρ` and `PolynomialBound a τ` say that a
  natural-valued sequence is bounded by `C * ρ ^ n` resp. `C * n ^ τ`, with an explicit positive
  constant.  Taking the infimum of admissible bases or exponents (`exponentialRate`,
  `polynomialExponent`) then removes finite-prefix and normalization choices.  Two lemmas are the
  shared lower-bound engines of this half: `le_of_pow_succ_le_polynomial_mul_pow_succ` discards a
  polynomial loss from a geometric comparison, and `le_polynomialExponent_of_rpow_le` transports a
  real-exponent pointwise lower bound to the infimum.
* **The multiplicative Fekete engine.**  `Submultiplicative u` and `Supermultiplicative u` are the
  multiplicative forms `u (m + n) ≤ u m * u n` and `u m * u n ≤ u (m + n)` of sub- and
  superadditivity, and `Submultiplicative.tendsto_nthRootSeq` / `Supermultiplicative.tendsto_nthRootSeq`
  show that the roots `nthRootSeq u n = u n ^ (1/n)` converge to `submultiplicativeLimit u` resp.
  `supermultiplicativeLimit u`.  Both are transported from Fekete's subadditive lemma (Fekete 1923),
  available in Mathlib as `Subadditive.tendsto_lim`, along `log`.

`exponentialRate_eq_submultiplicativeLimit` joins the two halves: for a submultiplicative
natural-valued sequence bounded below by `1`, the constant-tolerant infimum agrees with the Fekete
limit.  `Tensor/AsymptoticInvariant.lean` is the tensor client of both.

A third, self-contained section, **trading a large real exponent for the square**, holds the single
arithmetic step `rpow_two_div_le_of_le_mul_rpow`: from `R ≤ F · M^f` with `f ≥ 2` it derives
`R^{2/f} ≤ F · M²`.  It is the balancing step of the independence-number barrier and, like the rest
of this module, mentions no tensor.

## References

* M. Fekete, *Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit
  ganzzahligen Koeffizienten*, Math. Z. 17 (1923), 228--249.
-/

namespace AlgebraicComplexity.Growth

/-- A nonnegative real sequence grows more slowly than every exponential base greater than one,
up to a base-dependent positive constant.

The predicate lives in this Mathlib-only layer-0 module because tensor invariants and higher
analysis adapters both use it. Closure properties and standard witnesses are developed in
`AlgebraicComplexity/Analysis/Subexponential.lean`. -/
def Subexponential (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧
    ∀ δ : ℝ, 1 < δ → ∃ C : ℝ, 0 < C ∧ ∀ n, a n ≤ C * δ ^ n

/-- `a` grows at most exponentially with base `ρ`, up to a fixed positive constant. -/
def ExponentialBound (a : ℕ → ℕ) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, (a n : ℝ) ≤ C * ρ ^ n

/-- If every positive power of `b` is bounded by a fixed constant times the corresponding
power of `ρ`, then `b ≤ ρ`.  This elementary closedness lemma avoids introducing roots or limsup
when polynomial losses are removed from exponential estimates.

It is stated before the `ExponentialBound` API because it is the single engine behind every
lower bound on an admissible exponential base: `ExponentialBound.base_le_of_pow_le` is the
immediate specialization in which the constant comes from the exponential bound itself. -/
theorem le_of_pow_succ_le_const_mul_pow_succ
    {b ρ A : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ n : ℕ, b ^ (n + 1) ≤ A * ρ ^ (n + 1)) :
    b ≤ ρ := by
  by_contra hnot
  have hρb : ρ < b := lt_of_not_ge hnot
  by_cases hρzero : ρ = 0
  · subst ρ
    have hbpos : 0 < b := hρb
    have hzero := h 0
    norm_num at hzero
    linarith
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρzero)
    let ratio : ℝ := b / ρ
    have hratio : 1 < ratio := (lt_div_iff₀ hρpos).mpr (by simpa using hρb)
    have heventually : ∀ᶠ n : ℕ in Filter.atTop, A < ratio ^ (n + 1) :=
      ((tendsto_pow_atTop_atTop_of_one_lt hratio).comp
        (Filter.tendsto_add_atTop_nat 1)).eventually_gt_atTop A
    rcases Filter.eventually_atTop.1 heventually with ⟨N, hN⟩
    have hlarge := hN N le_rfl
    have hpowρpos : 0 < ρ ^ (N + 1) := pow_pos hρpos _
    have hstrict : A * ρ ^ (N + 1) < b ^ (N + 1) := by
      calc
        A * ρ ^ (N + 1) < ratio ^ (N + 1) * ρ ^ (N + 1) :=
          mul_lt_mul_of_pos_right hlarge hpowρpos
        _ = b ^ (N + 1) := by
          dsimp [ratio]
          rw [div_pow]
          field_simp
    exact (not_lt_of_ge (h N)) hstrict

namespace ExponentialBound

theorem bddBelow (a : ℕ → ℕ) : BddBelow { ρ : ℝ | ExponentialBound a ρ } := by
  exact ⟨0, fun _ h ↦ h.1⟩

/-- A pointwise natural-power bound is an exponential bound with constant one. -/
theorem of_le_pow (a : ℕ → ℕ) (r : ℕ) (h : ∀ n, a n ≤ r ^ n) :
    ExponentialBound a (r : ℝ) := by
  refine ⟨by positivity, 1, by positivity, ?_⟩
  intro n
  simp only [one_mul, ← Nat.cast_pow]
  exact_mod_cast h n

/-- A pointwise smaller sequence inherits every exponential bound. -/
theorem of_le {a b : ℕ → ℕ} {r : ℝ} (h : ∀ n, a n ≤ b n)
    (hb : ExponentialBound b r) : ExponentialBound a r := by
  rcases hb with ⟨hr, C, hC, hb⟩
  refine ⟨hr, C, hC, fun n ↦ ?_⟩
  exact (Nat.cast_le.mpr (h n)).trans (hb n)

/-- Increasing a nonnegative base preserves an exponential bound. -/
theorem mono_base {a : ℕ → ℕ} {ρ σ : ℝ} (h : ExponentialBound a ρ)
    (hρσ : ρ ≤ σ) : ExponentialBound a σ := by
  rcases h with ⟨hρ, C, hC, ha⟩
  refine ⟨hρ.trans hρσ, C, hC, fun n ↦ (ha n).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hρσ n) hC.le

/-- If `b^n` is a pointwise lower bound, every admissible exponential base is at least `b`.

Proof sketch: chaining the lower bound `b^(n+1) ≤ a (n+1)` with the exponential upper bound
`a (n+1) ≤ C·ρ^(n+1)` puts the hypothesis of `le_of_pow_succ_le_const_mul_pow_succ` in place,
with the constant `C` supplied by the exponential bound. -/
theorem base_le_of_pow_le
    {a : ℕ → ℕ} {ρ b : ℝ}
    (h : ExponentialBound a ρ)
    (hlower : ∀ n, b ^ n ≤ a n) :
    b ≤ ρ := by
  obtain ⟨hρ, C, _hC, ha⟩ := h
  exact le_of_pow_succ_le_const_mul_pow_succ hρ
    fun n ↦ (hlower (n + 1)).trans (ha (n + 1))

/-- Pointwise products multiply exponential bases and constants. -/
theorem mul {a b : ℕ → ℕ} {ρ σ : ℝ}
    (ha : ExponentialBound a ρ) (hb : ExponentialBound b σ) :
    ExponentialBound (fun n ↦ a n * b n) (ρ * σ) := by
  rcases ha with ⟨hρ, C, hC, ha⟩
  rcases hb with ⟨hσ, D, hD, hb⟩
  refine ⟨mul_nonneg hρ hσ, C * D, mul_pos hC hD, fun n ↦ ?_⟩
  rw [Nat.cast_mul, mul_pow]
  calc
    (a n : ℝ) * b n ≤ (C * ρ ^ n) * (D * σ ^ n) :=
      mul_le_mul (ha n) (hb n) (Nat.cast_nonneg _) (mul_nonneg hC.le (pow_nonneg hρ _))
    _ = (C * D) * (ρ ^ n * σ ^ n) := by ring

/-- An eventually valid exponential estimate can absorb its finite prefix into the constant. -/
theorem of_eventually {a : ℕ → ℕ} {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 < C)
    (h : ∀ᶠ n in Filter.atTop, (a n : ℝ) ≤ C * ρ ^ n) :
    ExponentialBound a ρ := by
  rcases Filter.eventually_atTop.1 h with ⟨N, hN⟩
  let finitePart : ℝ := ∑ i ∈ Finset.range N, (a i : ℝ) / ρ ^ i
  have hfinitePart : 0 ≤ finitePart := by
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ.le _)
  refine ⟨hρ.le, C + finitePart, add_pos_of_pos_of_nonneg hC hfinitePart, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hfinitePart) (pow_nonneg hρ.le _))
  · have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have hterm : (a n : ℝ) / ρ ^ n ≤ finitePart := by
      change (a n : ℝ) / ρ ^ n ≤
        ∑ i ∈ Finset.range N, (a i : ℝ) / ρ ^ i
      exact Finset.single_le_sum (s := Finset.range N)
        (f := fun i ↦ (a i : ℝ) / ρ ^ i)
        (fun i hi ↦ div_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ.le _)) hnmem
    apply (div_le_iff₀ (pow_pos hρ n)).mp
    exact hterm.trans (le_add_of_nonneg_left hC.le)

/-- Every real exponential base greater than one eventually dominates a fixed natural power,
up to a positive constant.  The proof is elementary and keeps this foundational module free of
the much broader normed-asymptotics import. -/
theorem exists_const_mul_pow_ge_polynomial
    (k : ℕ) {δ : ℝ} (hδ : 1 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, (n : ℝ) ^ k ≤ A * δ ^ n := by
  have heventually : ∀ᶠ M : ℕ in Filter.atTop, (2 : ℝ) ^ k < δ ^ M :=
    (tendsto_pow_atTop_atTop_of_one_lt hδ).eventually_gt_atTop ((2 : ℝ) ^ k)
  rcases Filter.eventually_atTop.1 heventually with ⟨M₀, hM₀⟩
  let M := max M₀ 1
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_right M₀ 1)
  have hM : (2 : ℝ) ^ k < δ ^ M := hM₀ M (le_max_left M₀ 1)
  let A : ℝ := (M : ℝ) ^ k * δ ^ M
  have hA : 0 < A := mul_pos (pow_pos (by exact_mod_cast hMpos) _)
    (pow_pos (lt_trans zero_lt_one hδ) _)
  refine ⟨A, hA, ?_⟩
  intro n
  let q := n / M
  have hn_upper : n ≤ M * (q + 1) :=
    (Nat.lt_mul_div_succ n hMpos).le
  have hMq_upper : M * (q + 1) ≤ n + M := by
    dsimp [q]
    rw [Nat.mul_add]
    simpa using Nat.add_le_add_right (Nat.mul_div_le n M) M
  have hq_two : q + 1 ≤ 2 ^ (q + 1) :=
    (Nat.lt_two_pow_self (n := q + 1)).le
  calc
    (n : ℝ) ^ k ≤ (M * (q + 1) : ℕ) ^ k := by
      exact_mod_cast Nat.pow_le_pow_left hn_upper k
    _ = (M : ℝ) ^ k * (q + 1 : ℕ) ^ k := by
      push_cast
      rw [mul_pow]
    _ ≤ (M : ℝ) ^ k * (2 ^ (q + 1) : ℕ) ^ k := by
      gcongr
    _ = (M : ℝ) ^ k * ((2 : ℝ) ^ k) ^ (q + 1) := by
      push_cast
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (M : ℝ) ^ k * (δ ^ M) ^ (q + 1) := by
      gcongr
    _ = (M : ℝ) ^ k * δ ^ (M * (q + 1)) := by
      rw [pow_mul]
    _ ≤ (M : ℝ) ^ k * δ ^ (n + M) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hδ.le hMq_upper) (pow_nonneg (by positivity) _)
    _ = A * δ ^ n := by
      dsimp [A]
      rw [pow_add]
      ring

/-- A polynomial factor multiplying `r^n` can be absorbed into every strictly larger base. -/
theorem of_le_pow_mul_affine
    {a : ℕ → ℕ} {r d k : ℕ} {ρ : ℝ} (hrρ : (r : ℝ) < ρ)
    (h : ∀ n, a n ≤ r ^ n * (n * d + 1) ^ k) :
    ExponentialBound a ρ := by
  have hρpos : 0 < ρ := (Nat.cast_nonneg r).trans_lt hrρ
  by_cases hrzero : r = 0
  · apply of_eventually hρpos zero_lt_one
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have ha0 : a n = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hrzero, Nat.ne_of_gt (Nat.zero_lt_of_lt hn)] using h n
    simp [ha0]
    positivity
  · have hrpos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hrzero
    let σ : ℝ := ((r : ℝ) + ρ) / 2
    have hrσ : (r : ℝ) < σ := by dsimp [σ]; linarith
    have hσρ : σ < ρ := by dsimp [σ]; linarith
    let δ : ℝ := σ / r
    have hδ : 1 < δ := (lt_div_iff₀ hrpos).mpr (by simpa using hrσ)
    obtain ⟨A, hA, hpoly⟩ := exists_const_mul_pow_ge_polynomial k hδ
    let C : ℝ := A * ((d + 1 : ℕ) : ℝ) ^ k
    have hC : 0 < C := mul_pos hA (pow_pos (by positivity) _)
    apply of_eventually hρpos hC
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have haffineNat : n * d + 1 ≤ n * (d + 1) := by
      calc
        n * d + 1 ≤ n * d + n := Nat.add_le_add_left hn (n * d)
        _ = n * (d + 1) := by ring
    have haffine :
        (((n * d + 1 : ℕ) : ℝ) ^ k) ≤
          ((n : ℝ) ^ k * ((d + 1 : ℕ) : ℝ) ^ k) := by
      calc
        (((n * d + 1 : ℕ) : ℝ) ^ k) ≤
            (((n * (d + 1) : ℕ) : ℝ) ^ k) := by
          exact_mod_cast Nat.pow_le_pow_left haffineNat k
        _ = (n : ℝ) ^ k * ((d + 1 : ℕ) : ℝ) ^ k := by
          push_cast
          rw [mul_pow]
    have ha :
        (a n : ℝ) ≤ (r : ℝ) ^ n * (((n * d + 1 : ℕ) : ℝ) ^ k) := by
      exact_mod_cast h n
    have hbase : (r : ℝ) * δ = σ := by
      dsimp [δ]
      exact mul_div_cancel₀ σ hrpos.ne'
    calc
      (a n : ℝ) ≤ (r : ℝ) ^ n * (((n * d + 1 : ℕ) : ℝ) ^ k) := ha
      _ ≤ (r : ℝ) ^ n * ((n : ℝ) ^ k * ((d + 1 : ℕ) : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left haffine (pow_nonneg (Nat.cast_nonneg r) _)
      _ ≤ (r : ℝ) ^ n * ((A * δ ^ n) * ((d + 1 : ℕ) : ℝ) ^ k) := by
        gcongr
        exact hpoly n
      _ = C * σ ^ n := by
        dsimp [C]
        rw [← hbase, mul_pow]
        ring
      _ ≤ C * ρ ^ n :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hσρ.le n) hC.le

end ExponentialBound

/-- Removing a fixed polynomial loss from a geometric comparison of two nonnegative reals: if
`b^(n+1) ≤ C·(n+2)^k·ρ^(n+1)` for every `n`, then `b ≤ ρ`.

This is the polynomially-degraded companion of `le_of_pow_succ_le_const_mul_pow_succ`, and the
shared engine behind every "a polynomial factor does not change a growth rate" argument: the
positive-power indexing `n + 1`, `(n + 2)^k` matches tensor-power type-selection counts, where
`n + 1` tensor factors carry at most `(n + 2)^k` multiplicity types.  Its two consumers are
`le_exponentialRate_of_pow_succ_le_mul_polynomial` just below and Schönhage's partial
`τ`-theorem in `MatrixMultiplication/PartialAsymptoticSum.lean`.

Proof sketch: if `ρ < b`, pick `δ` strictly between `1` and `b / ρ`.  The polynomial factor is
dominated by `A·δ^n` (`ExponentialBound.exists_const_mul_pow_ge_polynomial`), so the hypothesis
degrades to a comparison with constant loss against the strictly smaller base `ρ·δ < b`,
contradicting `le_of_pow_succ_le_const_mul_pow_succ`. -/
theorem le_of_pow_succ_le_polynomial_mul_pow_succ
    {b ρ C : ℝ} {k : ℕ} (hρ : 0 ≤ ρ) (hC : 0 < C)
    (h : ∀ n : ℕ, b ^ (n + 1) ≤ C * ((n + 2 : ℕ) : ℝ) ^ k * ρ ^ (n + 1)) :
    b ≤ ρ := by
  by_contra hnot
  have hρb : ρ < b := lt_of_not_ge hnot
  by_cases hρzero : ρ = 0
  · subst hρzero
    have h0 := h 0
    norm_num at h0
    linarith
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρzero)
    have hratio : 1 < b / ρ := (lt_div_iff₀ hρpos).mpr (by simpa using hρb)
    have hδ : 1 < (b / ρ + 1) / 2 := by linarith
    have hδratio : (b / ρ + 1) / 2 < b / ρ := by linarith
    obtain ⟨A, hA, hpoly⟩ :=
      ExponentialBound.exists_const_mul_pow_ge_polynomial k hδ
    have hbase : ρ * ((b / ρ + 1) / 2) < b := by
      have h1 : ρ * ((b / ρ + 1) / 2) < ρ * (b / ρ) :=
        mul_lt_mul_of_pos_left hδratio hρpos
      have h2 : ρ * (b / ρ) = b := by field_simp
      linarith
    have hbound : ∀ n : ℕ,
        b ^ (n + 1) ≤ (C * A * ((b / ρ + 1) / 2)) * (ρ * ((b / ρ + 1) / 2)) ^ (n + 1) := by
      intro n
      calc b ^ (n + 1) ≤ C * ((n + 2 : ℕ) : ℝ) ^ k * ρ ^ (n + 1) := h n
        _ ≤ C * (A * ((b / ρ + 1) / 2) ^ (n + 2)) * ρ ^ (n + 1) := by
            gcongr
            exact hpoly (n + 2)
        _ = (C * A * ((b / ρ + 1) / 2)) * (ρ * ((b / ρ + 1) / 2)) ^ (n + 1) := by
            rw [mul_pow]
            ring
    have hle := le_of_pow_succ_le_const_mul_pow_succ (by positivity) hbound
    exact absurd hle (not_le_of_gt hbase)

/-- The least exponential base bounding `a`, allowing a fixed positive multiplicative constant. -/
noncomputable def exponentialRate (a : ℕ → ℕ) : ℝ :=
  sInf { ρ : ℝ | ExponentialBound a ρ }

theorem exponentialRate_nonneg (a : ℕ → ℕ) : 0 ≤ exponentialRate a := by
  exact Real.sInf_nonneg fun _ h ↦ h.1

theorem exponentialRate_le {a : ℕ → ℕ} {ρ : ℝ} (h : ExponentialBound a ρ) :
    exponentialRate a ≤ ρ := by
  exact csInf_le (ExponentialBound.bddBelow a) h

/-- Every base strictly above the exponential rate is admissible, provided the sequence has at
least one exponential bound. -/
theorem exponentialBound_of_exponentialRate_lt
    {a : ℕ → ℕ} {ρ : ℝ}
    (hupper : ∃ σ, ExponentialBound a σ)
    (hρ : exponentialRate a < ρ) :
    ExponentialBound a ρ := by
  obtain ⟨σ, hσ, hσρ⟩ := exists_lt_of_csInf_lt hupper hρ
  exact ExponentialBound.mono_base hσ hσρ.le

/-- A global geometric lower bound gives the same lower bound on exponential rate. -/
theorem le_exponentialRate_of_pow_le
    {a : ℕ → ℕ} {b : ℝ}
    (hupper : ∃ ρ, ExponentialBound a ρ)
    (hlower : ∀ n, b ^ n ≤ a n) :
    b ≤ exponentialRate a := by
  apply le_csInf
  · exact hupper
  · intro ρ hρ
    exact ExponentialBound.base_le_of_pow_le hρ hlower

/-- A fixed polynomial loss in a lower bound does not change the resulting lower bound on an
exponential rate.  The positive-power indexing matches tensor-power type-selection arguments:
`n + 1` tensor factors have at most `(n + 2)^k` multiplicity types.

Proof sketch: unfold the infimum and feed each admissible base to
`le_of_pow_succ_le_polynomial_mul_pow_succ`, whose constant absorbs the one carried by the
exponential bound. -/
theorem le_exponentialRate_of_pow_succ_le_mul_polynomial
    {a : ℕ → ℕ} {b C : ℝ} {k : ℕ}
    (hupper : ∃ ρ, ExponentialBound a ρ)
    (hC : 0 < C)
    (hlower : ∀ n : ℕ,
      b ^ (n + 1) ≤ C * ((n + 2 : ℕ) : ℝ) ^ k * a (n + 1)) :
    b ≤ exponentialRate a := by
  apply le_csInf
  · exact hupper
  · rintro ρ ⟨hρ, D, hD, ha⟩
    refine le_of_pow_succ_le_polynomial_mul_pow_succ (C := C * D) (k := k) hρ
      (mul_pos hC hD) fun n ↦ ?_
    calc b ^ (n + 1) ≤ C * ((n + 2 : ℕ) : ℝ) ^ k * a (n + 1) := hlower n
      _ ≤ C * ((n + 2 : ℕ) : ℝ) ^ k * (D * ρ ^ (n + 1)) := by gcongr; exact ha (n + 1)
      _ = C * D * ((n + 2 : ℕ) : ℝ) ^ k * ρ ^ (n + 1) := by ring

/-- A fixed polynomial factor does not change the exponential growth rate.  This form is tailored
to coefficient extraction from degree-`d` tensor certificates. -/
theorem exponentialRate_le_of_le_pow_mul_affine
    (a : ℕ → ℕ) (r d k : ℕ)
    (h : ∀ n, a n ≤ r ^ n * (n * d + 1) ^ k) :
    exponentialRate a ≤ r := by
  apply le_of_forall_gt
  intro ρ hρ
  let σ : ℝ := ((r : ℝ) + ρ) / 2
  have hrσ : (r : ℝ) < σ := by dsimp [σ]; linarith
  have hσρ : σ < ρ := by dsimp [σ]; linarith
  exact (exponentialRate_le (ExponentialBound.of_le_pow_mul_affine hrσ h)).trans_lt hσρ

/-- Multiplication by a fixed affine-polynomial factor does not increase exponential rate.

Unlike `exponentialRate_le_of_le_pow_mul_affine`, the larger sequence need not itself be a pure
power.  This is the form needed to compare optimized rank certificates before and after
coefficient extraction. -/
theorem exponentialRate_le_of_le_mul_affine
    {a b : ℕ → ℕ} (d k : ℕ)
    (h : ∀ n, a n ≤ b n * (n * d + 1) ^ k)
    (hb : ∃ ρ, ExponentialBound b ρ) :
    exponentialRate a ≤ exponentialRate b := by
  apply le_csInf
  · exact hb
  · intro ρ hρ
    by_cases hρzero : ρ = 0
    · subst ρ
      have hp : ExponentialBound (fun n ↦ (n * d + 1) ^ k) (2 : ℝ) := by
        refine ExponentialBound.of_le_pow_mul_affine
          (a := fun n ↦ (n * d + 1) ^ k) (r := 1) (d := d) (k := k)
          (by norm_num) ?_
        intro n
        simp
      have hab : ExponentialBound a ((0 : ℝ) * 2) :=
        ExponentialBound.of_le h (ExponentialBound.mul hρ hp)
      simpa using exponentialRate_le hab
    · have hρpos : 0 < ρ := lt_of_le_of_ne hρ.1 (Ne.symm hρzero)
      apply le_of_forall_gt
      intro σ hρσ
      let τ : ℝ := (ρ + σ) / 2
      have hρτ : ρ < τ := by dsimp [τ]; linarith
      have hτσ : τ < σ := by dsimp [τ]; linarith
      let ratio : ℝ := τ / ρ
      have hratio : (1 : ℝ) < ratio := by
        dsimp [ratio]
        exact (lt_div_iff₀ hρpos).2 (by simpa using hρτ)
      have hp : ExponentialBound (fun n ↦ (n * d + 1) ^ k) ratio := by
        refine ExponentialBound.of_le_pow_mul_affine
          (a := fun n ↦ (n * d + 1) ^ k) (r := 1) (d := d) (k := k)
          (by simpa only [Nat.cast_one] using hratio) ?_
        intro n
        simp
      have hab : ExponentialBound a (ρ * ratio) :=
        ExponentialBound.of_le h (ExponentialBound.mul hρ hp)
      have hbase : ρ * ratio = τ := by
        dsimp [ratio]
        exact mul_div_cancel₀ τ hρzero
      rw [hbase] at hab
      exact (exponentialRate_le hab).trans_lt hτσ

/-- Exponential growth rate is monotone under pointwise comparison, provided the larger sequence
has at least one exponential bound. -/
theorem exponentialRate_mono {a b : ℕ → ℕ} (h : ∀ n, a n ≤ b n)
    (hb : ∃ ρ, ExponentialBound b ρ) : exponentialRate a ≤ exponentialRate b := by
  apply le_csInf
  · rcases hb with ⟨ρ, hρ⟩
    exact ⟨ρ, hρ⟩
  · intro ρ hρ
    exact exponentialRate_le (hρ.of_le h)

namespace PolynomialBound

theorem bddBelow (a : ℕ → ℕ) : BddBelow { τ : ℝ | PolynomialBound a τ } := by
  exact ⟨0, fun _ h ↦ h.1⟩

/-- A pointwise natural polynomial bound has the corresponding real exponent. -/
theorem of_le_pow (a : ℕ → ℕ) (k : ℕ) (h : ∀ n, a n ≤ n ^ k) :
    PolynomialBound a (k : ℝ) := by
  refine ⟨by positivity, 1, by positivity, ?_⟩
  intro n _
  simp only [one_mul, Real.rpow_natCast, ← Nat.cast_pow]
  exact_mod_cast h n

/-- A sequence that is pointwise smaller on positive inputs inherits every polynomial bound.
The comparison is required only where `PolynomialBound` looks: the value at `n = 0` is never
inspected. -/
theorem of_le {a b : ℕ → ℕ} {τ : ℝ} (h : ∀ n : ℕ, 1 ≤ n → a n ≤ b n)
    (hb : PolynomialBound b τ) : PolynomialBound a τ := by
  rcases hb with ⟨hτ, C, hC, hb⟩
  refine ⟨hτ, C, hC, fun n hn ↦ ?_⟩
  exact (Nat.cast_le.mpr (h n hn)).trans (hb n hn)

/-- Increasing a nonnegative polynomial exponent preserves a bound on positive naturals. -/
theorem mono_exponent {a : ℕ → ℕ} {τ υ : ℝ} (h : PolynomialBound a τ)
    (hτυ : τ ≤ υ) : PolynomialBound a υ := by
  rcases h with ⟨hτ, C, hC, ha⟩
  refine ⟨hτ.trans hτυ, C, hC, fun n hn ↦ (ha n hn).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hτυ

/-- A pointwise lower bound `(n : ℝ)^γ ≤ a n` on positive inputs, with a *real* exponent `γ`,
forces every admissible polynomial exponent `τ` to satisfy `γ ≤ τ`.  This is the general
lower-bound counterpart of `mono_exponent`, and the engine behind both
`natCast_le_exponent` and the infimum-level statements below.

Proof sketch: if some admissible exponent `τ` were smaller than `γ`, then along the powers
`n = 2^N` the ratio `n^γ / n^τ = n^(γ - τ)` grows without bound, eventually exceeding the
constant `C` of the polynomial bound and contradicting `n^γ ≤ a n ≤ C·n^τ`. -/
theorem le_exponent_of_rpow_le
    {a : ℕ → ℕ} {γ τ : ℝ}
    (h : PolynomialBound a τ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ γ ≤ a n) :
    γ ≤ τ := by
  rcases h with ⟨hτ0, C, hC, ha⟩
  by_contra hnot
  have hgap : 0 < γ - τ := sub_pos.mpr (lt_of_not_ge hnot)
  let b : ℝ := (2 : ℝ) ^ (γ - τ)
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) hgap
  have heventually : ∀ᶠ N : ℕ in Filter.atTop, C < b ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt hb).eventually_gt_atTop C
  rcases Filter.eventually_atTop.1 heventually with ⟨N, hN⟩
  let N' := max N 1
  let n := 2 ^ N'
  have hlargeBase : C < b ^ N' := hN N' (le_max_left N 1)
  have hnlarge : C < (n : ℝ) ^ (γ - τ) :=
    hlargeBase.trans_le (by
      dsimp [b, n]
      push_cast
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
      exact le_rfl)
  have hn : 1 ≤ n := Nat.one_le_two_pow
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hlowerN : (n : ℝ) ^ γ ≤ a n := hlower n hn
  have hupperN : (a n : ℝ) ≤ C * (n : ℝ) ^ τ := ha n hn
  have hpow : (n : ℝ) ^ γ ≤ C * (n : ℝ) ^ τ := hlowerN.trans hupperN
  have hfactor : (n : ℝ) ^ γ = (n : ℝ) ^ (γ - τ) * (n : ℝ) ^ τ := by
    rw [← Real.rpow_add hnpos]
    ring_nf
  rw [hfactor] at hpow
  have hpowτpos : 0 < (n : ℝ) ^ τ := Real.rpow_pos_of_pos hnpos _
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hnlarge hpowτpos)) hpow

/-- A pointwise lower bound by `n^k` forces every admissible polynomial exponent to be at least
`k`.  This is the lower-bound counterpart of `of_le_pow`, and the natural-exponent
specialization of `le_exponent_of_rpow_le`. -/
theorem natCast_le_exponent
    {a : ℕ → ℕ} {k : ℕ} {τ : ℝ}
    (h : PolynomialBound a τ)
    (hlower : ∀ n, n ^ k ≤ a n) :
    (k : ℝ) ≤ τ :=
  h.le_exponent_of_rpow_le fun n _ ↦ by
    rw [Real.rpow_natCast, ← Nat.cast_pow]
    exact_mod_cast hlower n

end PolynomialBound

theorem polynomialExponent_nonneg (a : ℕ → ℕ) : 0 ≤ polynomialExponent a := by
  exact Real.sInf_nonneg fun _ h ↦ h.1

theorem polynomialExponent_le {a : ℕ → ℕ} {τ : ℝ} (h : PolynomialBound a τ) :
    polynomialExponent a ≤ τ := by
  exact csInf_le (PolynomialBound.bddBelow a) h

/-- A pointwise lower bound `(n : ℝ)^γ ≤ a n` on positive inputs, with a *real* exponent `γ`,
forces `γ ≤ polynomialExponent a`, provided at least one polynomial upper bound exists.

Proof sketch: the pointwise estimate bounds *every* admissible exponent below by `γ`, via
`PolynomialBound.le_exponent_of_rpow_le`, so `γ` is a lower bound for the defining set and hence
for its infimum.  This is the infimum-level counterpart of `PolynomialBound.le_exponent_of_rpow_le`,
and specializes to `natCast_le_polynomialExponent` exactly as `le_exponent_of_rpow_le` specializes
to `natCast_le_exponent` one level down.  The rectangular matrix-multiplication exponent needs the
real-exponent form because its flattening lower bound has the irrational exponent `1 + κ`. -/
theorem le_polynomialExponent_of_rpow_le
    {a : ℕ → ℕ} {γ : ℝ}
    (hupper : ∃ τ, PolynomialBound a τ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ γ ≤ a n) :
    γ ≤ polynomialExponent a :=
  le_csInf hupper fun _ hτ ↦ hτ.le_exponent_of_rpow_le hlower

/-- A global lower bound `n^k ≤ a(n)` gives the corresponding lower bound on the least
polynomial exponent, provided at least one polynomial upper bound exists.  This is the
natural-exponent specialization of `le_polynomialExponent_of_rpow_le`. -/
theorem natCast_le_polynomialExponent
    {a : ℕ → ℕ} {k : ℕ}
    (hupper : ∃ τ, PolynomialBound a τ)
    (hlower : ∀ n, n ^ k ≤ a n) :
    (k : ℝ) ≤ polynomialExponent a :=
  le_polynomialExponent_of_rpow_le hupper fun n _ ↦ by
    rw [Real.rpow_natCast, ← Nat.cast_pow]
    exact_mod_cast hlower n

/-- Polynomial growth exponent is monotone under pointwise comparison on positive inputs,
provided the larger sequence has at least one polynomial bound.  As in
`PolynomialBound.of_le`, the comparison at `n = 0` is not needed because `PolynomialBound`
never inspects that value. -/
theorem polynomialExponent_mono {a b : ℕ → ℕ} (h : ∀ n : ℕ, 1 ≤ n → a n ≤ b n)
    (hb : ∃ τ, PolynomialBound b τ) : polynomialExponent a ≤ polynomialExponent b := by
  apply le_csInf
  · rcases hb with ⟨τ, hτ⟩
    exact ⟨τ, hτ⟩
  · intro τ hτ
    exact polynomialExponent_le (hτ.of_le h)

open Filter Topology

/-!
## The multiplicative Fekete engine

This section is layer-0 material: it mentions only real sequences.  It is the multiplicative form
of Fekete's subadditive lemma, transported along `log` from Mathlib's `Subadditive.tendsto_lim`,
together with the comparison lemmas for the resulting limits.  `Tensor/AsymptoticInvariant.lean`
is its client: a numerical tensor invariant that is sub- or supermultiplicative under external
products has a sub- or supermultiplicative power sequence, and its exponential growth rate is the
limit produced here.
-/

variable {u v : ℕ → ℝ}

/-- The sequence of `n`th roots `n ↦ u n ^ (1/n)` of a real sequence.

The value at `n = 0` is a junk value: `(0 : ℝ)⁻¹ = 0`, so `nthRootSeq u 0 = u 0 ^ (0 : ℝ)`.  Every
result below inspects the sequence only at positive indices. -/
noncomputable def nthRootSeq (u : ℕ → ℝ) (n : ℕ) : ℝ := u n ^ ((n : ℝ)⁻¹)

/-- A real sequence is *submultiplicative* when `u (m + n) ≤ u m * u n` for all `m` and `n`.  This
is the multiplicative form of subadditivity; ordinary tensor rank of tensor powers is the motivating
example. -/
def Submultiplicative (u : ℕ → ℝ) : Prop := ∀ m n, u (m + n) ≤ u m * u n

/-- A real sequence is *supermultiplicative* when `u m * u n ≤ u (m + n)` for all `m` and `n`.
Subrank-style invariants of tensor powers are the motivating example. -/
def Supermultiplicative (u : ℕ → ℝ) : Prop := ∀ m n, u m * u n ≤ u (m + n)

/-- The normalized limit of a submultiplicative sequence, defined as the infimum of the roots
`u n ^ (1/n)` over positive `n`.  `Submultiplicative.tendsto_nthRootSeq` shows that the roots really
do converge to this infimum under the hypotheses of Fekete's lemma. -/
noncomputable def submultiplicativeLimit (u : ℕ → ℝ) : ℝ := sInf (nthRootSeq u '' Set.Ici 1)

/-- The normalized limit of a supermultiplicative sequence, defined as the supremum of the roots
`u n ^ (1/n)` over positive `n`.  `Supermultiplicative.tendsto_nthRootSeq` shows that the roots
really do converge to this supremum under a geometric upper bound. -/
noncomputable def supermultiplicativeLimit (u : ℕ → ℝ) : ℝ := sSup (nthRootSeq u '' Set.Ici 1)

/-! ### Elementary properties of the root sequence -/

/-- Roots of a nonnegative sequence are nonnegative. -/
theorem nthRootSeq_nonneg (hu : ∀ n, 0 ≤ u n) (n : ℕ) : 0 ≤ nthRootSeq u n :=
  Real.rpow_nonneg (hu n) _

/-- Roots of a sequence bounded below by `1` are bounded below by `1`. -/
theorem one_le_nthRootSeq (hu : ∀ n, 1 ≤ u n) (n : ℕ) : 1 ≤ nthRootSeq u n := by
  simpa [nthRootSeq] using Real.rpow_le_rpow zero_le_one (hu n) (by positivity)

/-- Pointwise domination of nonnegative sequences is inherited by their root sequences. -/
theorem nthRootSeq_mono (hu : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n) (n : ℕ) :
    nthRootSeq u n ≤ nthRootSeq v n :=
  Real.rpow_le_rpow (hu n) (huv n) (by positivity)

/-- Every positive-index root of a geometric sequence is its base. -/
theorem nthRootSeq_pow {b : ℝ} (hb : 0 ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    nthRootSeq (fun k ↦ b ^ k) n = b :=
  Real.pow_rpow_inv_natCast hb (by omega)

/-- The positive-index roots of a real sequence form a nonempty set. -/
theorem nthRootSeq_image_nonempty (u : ℕ → ℝ) : (nthRootSeq u '' Set.Ici 1).Nonempty :=
  ⟨nthRootSeq u 1, 1, Set.mem_Ici.mpr le_rfl, rfl⟩

/-- The positive-index roots of a nonnegative sequence are bounded below by zero. -/
theorem bddBelow_nthRootSeq_image (hu : ∀ n, 0 ≤ u n) :
    BddBelow (nthRootSeq u '' Set.Ici 1) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, -, rfl⟩
  exact nthRootSeq_nonneg hu n

/-- A geometric upper bound `u n ≤ C ^ n` bounds every positive-index root by `C`, hence bounds the
set of roots above.

Proof sketch: monotonicity of `n`th roots reduces the claim to `nthRootSeq (C ^ ·) n = C`. -/
theorem bddAbove_nthRootSeq_image {C : ℝ} (hu : ∀ n, 0 ≤ u n) (hub : ∀ n, u n ≤ C ^ n) :
    BddAbove (nthRootSeq u '' Set.Ici 1) := by
  have hC : 0 ≤ C := (hu 1).trans (by simpa using hub 1)
  refine ⟨C, ?_⟩
  rintro x ⟨n, hn, rfl⟩
  calc nthRootSeq u n ≤ nthRootSeq (fun k ↦ C ^ k) n := nthRootSeq_mono hu hub n
    _ = C := nthRootSeq_pow hC hn

/-! ### Comparison lemmas for the two limits -/

/-- The submultiplicative limit is bounded by every individual positive-index root. -/
theorem submultiplicativeLimit_le_nthRootSeq (hu : ∀ n, 0 ≤ u n) {n : ℕ} (hn : 1 ≤ n) :
    submultiplicativeLimit u ≤ nthRootSeq u n :=
  csInf_le (bddBelow_nthRootSeq_image hu) ⟨n, hn, rfl⟩

/-- A uniform lower bound on the positive-index roots bounds the submultiplicative limit below. -/
theorem le_submultiplicativeLimit {b : ℝ} (h : ∀ n : ℕ, 1 ≤ n → b ≤ nthRootSeq u n) :
    b ≤ submultiplicativeLimit u := by
  refine le_csInf (nthRootSeq_image_nonempty u) ?_
  rintro x ⟨n, hn, rfl⟩
  exact h n hn

/-- A sequence bounded below by `1` has submultiplicative limit at least `1`. -/
theorem one_le_submultiplicativeLimit (hu : ∀ n, 1 ≤ u n) : 1 ≤ submultiplicativeLimit u :=
  le_submultiplicativeLimit fun n _ ↦ one_le_nthRootSeq hu n

/-- The submultiplicative limit is monotone under pointwise domination of nonnegative sequences.
No multiplicativity hypothesis is needed: both sides are infima of root sets. -/
theorem submultiplicativeLimit_mono (hu : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n) :
    submultiplicativeLimit u ≤ submultiplicativeLimit v := by
  refine le_csInf (nthRootSeq_image_nonempty v) ?_
  rintro x ⟨n, hn, rfl⟩
  exact (submultiplicativeLimit_le_nthRootSeq hu hn).trans (nthRootSeq_mono hu huv n)

/-- A uniform upper bound on the positive-index roots bounds the supermultiplicative limit above. -/
theorem supermultiplicativeLimit_le {b : ℝ} (h : ∀ n : ℕ, 1 ≤ n → nthRootSeq u n ≤ b) :
    supermultiplicativeLimit u ≤ b := by
  refine csSup_le (nthRootSeq_image_nonempty u) ?_
  rintro x ⟨n, hn, rfl⟩
  exact h n hn

/-- Every individual positive-index root is bounded by the supermultiplicative limit, provided the
roots are bounded above at all. -/
theorem nthRootSeq_le_supermultiplicativeLimit
    (hbdd : BddAbove (nthRootSeq u '' Set.Ici 1)) {n : ℕ} (hn : 1 ≤ n) :
    nthRootSeq u n ≤ supermultiplicativeLimit u :=
  le_csSup hbdd ⟨n, hn, rfl⟩

/-- The supermultiplicative limit is monotone under pointwise domination, provided the larger
sequence has a geometric upper bound. -/
theorem supermultiplicativeLimit_mono {C : ℝ} (hu : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n)
    (hv : ∀ n, 0 ≤ v n) (hub : ∀ n, v n ≤ C ^ n) :
    supermultiplicativeLimit u ≤ supermultiplicativeLimit v := by
  refine supermultiplicativeLimit_le fun n hn ↦ ?_
  exact (nthRootSeq_mono hu huv n).trans
    (nthRootSeq_le_supermultiplicativeLimit (bddAbove_nthRootSeq_image hv hub) hn)

/-- On an exactly geometric sequence the positive-index roots are constant. -/
theorem nthRootSeq_image_pow {b : ℝ} (hb : 0 ≤ b) :
    nthRootSeq (fun k ↦ b ^ k) '' Set.Ici 1 = {b} := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact nthRootSeq_pow hb hn
  · rintro rfl
    exact ⟨1, Set.mem_Ici.mpr le_rfl, nthRootSeq_pow hb le_rfl⟩

/-- The submultiplicative limit of an exactly geometric sequence is its base. -/
@[simp] theorem submultiplicativeLimit_pow {b : ℝ} (hb : 0 ≤ b) :
    submultiplicativeLimit (fun k ↦ b ^ k) = b := by
  rw [submultiplicativeLimit, nthRootSeq_image_pow hb, csInf_singleton]

/-- The supermultiplicative limit of an exactly geometric sequence is its base. -/
@[simp] theorem supermultiplicativeLimit_pow {b : ℝ} (hb : 0 ≤ b) :
    supermultiplicativeLimit (fun k ↦ b ^ k) = b := by
  rw [supermultiplicativeLimit, nthRootSeq_image_pow hb, csSup_singleton]

/-! ### Fekete's lemma in multiplicative form -/

/-- The `n`th root of a fixed positive constant tends to one.

Proof sketch: write `c ^ (1/n) = exp (log c / n)` and use that `log c / n → 0`. -/
theorem tendsto_const_rpow_inv_natCast {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ c ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log c * ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul (Real.log c)
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (Real.log c * ((n : ℝ))⁻¹)) atTop (𝓝 1) := by
    have hcomp : Tendsto (fun n : ℕ ↦ Real.exp (Real.log c * ((n : ℝ))⁻¹)) atTop
        (𝓝 (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp hlog
    rwa [Real.exp_zero] at hcomp
  refine hexp.congr fun n ↦ ?_
  rw [Real.rpow_def_of_pos hc]

/-- Writing a positive sequence's roots through the exponential of its normalized logarithm. -/
theorem nthRootSeq_eq_exp (hpos : ∀ n, 0 < u n) (n : ℕ) :
    nthRootSeq u n = Real.exp (Real.log (u n) / n) := by
  rw [nthRootSeq, Real.rpow_def_of_pos (hpos n), div_eq_mul_inv]

/-- **Fekete's lemma, submultiplicative form.**  A positive submultiplicative sequence bounded
below by a positive geometric sequence has convergent `n`th roots, and the limit is the infimum of
those roots.

Proof sketch: `n ↦ log (u n)` is subadditive because `log` is monotone and turns the product
`u m * u n` into a sum, and the geometric lower bound `c ^ n ≤ u n` makes `log (u n) / n ≥ log c`
for `n ≥ 1`, so the quotients are bounded below.  Fekete's lemma (Mathlib's
`Subadditive.tendsto_lim`) gives `log (u n) / n → L`, whence `u n ^ (1/n) = exp (log (u n) / n)`
converges to `exp L`.  Finally `exp L` is a lower bound of the roots because `L ≤ log (u n) / n`
for `n ≥ 1`, and it is the greatest one because the roots converge to it; so `exp L` is the
infimum. -/
theorem Submultiplicative.tendsto_nthRootSeq (hu : Submultiplicative u) (hpos : ∀ n, 0 < u n)
    {c : ℝ} (hc : 0 < c) (hlb : ∀ n, c ^ n ≤ u n) :
    Tendsto (nthRootSeq u) atTop (𝓝 (submultiplicativeLimit u)) := by
  have hlog : Subadditive fun n ↦ Real.log (u n) := by
    intro m n
    calc Real.log (u (m + n)) ≤ Real.log (u m * u n) := Real.log_le_log (hpos _) (hu m n)
      _ = Real.log (u m) + Real.log (u n) := Real.log_mul (hpos m).ne' (hpos n).ne'
  have hbdd : BddBelow (Set.range fun n : ℕ ↦ Real.log (u n) / n) := by
    refine ⟨min 0 (Real.log c), ?_⟩
    rintro x ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]
      exact min_le_left (0 : ℝ) (Real.log c)
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hlogpow : (n : ℝ) * Real.log c ≤ Real.log (u n) := by
        have := Real.log_le_log (pow_pos hc n) (hlb n)
        rwa [Real.log_pow] at this
      refine (min_le_right _ _).trans ?_
      rw [le_div_iff₀ hnpos, mul_comm]
      exact hlogpow
  have htend : Tendsto (fun n : ℕ ↦ Real.log (u n) / n) atTop (𝓝 hlog.lim) :=
    hlog.tendsto_lim hbdd
  have htendroot : Tendsto (nthRootSeq u) atTop (𝓝 (Real.exp hlog.lim)) := by
    have hcomp : Tendsto (fun n : ℕ ↦ Real.exp (Real.log (u n) / n)) atTop
        (𝓝 (Real.exp hlog.lim)) := (Real.continuous_exp.tendsto _).comp htend
    exact hcomp.congr fun n ↦ (nthRootSeq_eq_exp hpos n).symm
  have hglb : IsGLB (nthRootSeq u '' Set.Ici 1) (Real.exp hlog.lim) := by
    constructor
    · rintro x ⟨n, hn, rfl⟩
      rw [nthRootSeq_eq_exp hpos n]
      exact Real.exp_le_exp.mpr (hlog.lim_le_div hbdd (Nat.one_le_iff_ne_zero.mp hn))
    · intro b hb
      refine ge_of_tendsto htendroot ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hb ⟨n, hn, rfl⟩
  rw [submultiplicativeLimit, hglb.csInf_eq (nthRootSeq_image_nonempty u)]
  exact htendroot

/-- **Fekete's lemma, supermultiplicative form.**  A positive supermultiplicative sequence bounded
above by a geometric sequence has convergent `n`th roots, and the limit is the supremum of those
roots.

Proof sketch: the dual transport.  `n ↦ -log (u n)` is subadditive because `log (u m) + log (u n) ≤
log (u (m + n))`, and the geometric upper bound `u n ≤ C ^ n` makes `-log (u n) / n ≥ -log C` for
`n ≥ 1`.  Fekete's lemma gives `-log (u n) / n → L`, so `log (u n) / n → -L` and the roots converge
to `exp (-L)`, which is simultaneously an upper bound for the roots and the least one. -/
theorem Supermultiplicative.tendsto_nthRootSeq (hu : Supermultiplicative u) (hpos : ∀ n, 0 < u n)
    {C : ℝ} (hub : ∀ n, u n ≤ C ^ n) :
    Tendsto (nthRootSeq u) atTop (𝓝 (supermultiplicativeLimit u)) := by
  have hC : 0 < C := lt_of_lt_of_le (hpos 1) (by simpa using hub 1)
  have hlog : Subadditive fun n ↦ -Real.log (u n) := by
    intro m n
    have hmul := Real.log_le_log (mul_pos (hpos m) (hpos n)) (hu m n)
    rw [Real.log_mul (hpos m).ne' (hpos n).ne'] at hmul
    linarith
  have hbdd : BddBelow (Set.range fun n : ℕ ↦ -Real.log (u n) / n) := by
    refine ⟨min 0 (-Real.log C), ?_⟩
    rintro x ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]
      exact min_le_left (0 : ℝ) (-Real.log C)
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hlogpow : Real.log (u n) ≤ (n : ℝ) * Real.log C := by
        have := Real.log_le_log (hpos n) (hub n)
        rwa [Real.log_pow] at this
      refine (min_le_right _ _).trans ?_
      rw [le_div_iff₀ hnpos]
      nlinarith
  have htend : Tendsto (fun n : ℕ ↦ -Real.log (u n) / n) atTop (𝓝 hlog.lim) :=
    hlog.tendsto_lim hbdd
  have htend' : Tendsto (fun n : ℕ ↦ Real.log (u n) / n) atTop (𝓝 (-hlog.lim)) := by
    have := htend.neg
    simpa [neg_div] using this
  have htendroot : Tendsto (nthRootSeq u) atTop (𝓝 (Real.exp (-hlog.lim))) := by
    have hcomp : Tendsto (fun n : ℕ ↦ Real.exp (Real.log (u n) / n)) atTop
        (𝓝 (Real.exp (-hlog.lim))) := (Real.continuous_exp.tendsto _).comp htend'
    exact hcomp.congr fun n ↦ (nthRootSeq_eq_exp hpos n).symm
  have hlub : IsLUB (nthRootSeq u '' Set.Ici 1) (Real.exp (-hlog.lim)) := by
    constructor
    · rintro x ⟨n, hn, rfl⟩
      rw [nthRootSeq_eq_exp hpos n]
      refine Real.exp_le_exp.mpr ?_
      have hstep := hlog.lim_le_div hbdd (n := n) (Nat.one_le_iff_ne_zero.mp hn)
      rw [neg_div] at hstep
      linarith
    · intro b hb
      refine le_of_tendsto htendroot ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hb ⟨n, hn, rfl⟩
  rw [supermultiplicativeLimit, hlub.csSup_eq (nthRootSeq_image_nonempty u)]
  exact htendroot

/-! ### Bridge to the constant-tolerant exponential rate -/

/-- A submultiplicative natural sequence bounded below by one admits an exponential bound: its
values never exceed `a 0 * a 1 ^ n`. -/
theorem exists_exponentialBound_of_submultiplicative {a : ℕ → ℕ} (hone : ∀ n, 1 ≤ a n)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n) : ∃ ρ, ExponentialBound a ρ := by
  have hpow : ∀ n, a n ≤ a 0 * a 1 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc a (n + 1) ≤ a n * a 1 := hsub n 1
          _ ≤ a 0 * a 1 ^ n * a 1 := Nat.mul_le_mul_right _ ih
          _ = a 0 * a 1 ^ (n + 1) := by ring
  refine ⟨(a 1 : ℝ), by positivity, (a 0 : ℝ), by exact_mod_cast hone 0, fun n ↦ ?_⟩
  exact_mod_cast hpow n

/-- The constant-tolerant exponential rate of `AlgebraicComplexity/Asymptotics.lean` agrees with
the engine's normalized limit for a submultiplicative natural sequence bounded below by one.

Proof sketch: two inequalities.  For `ρ` strictly above the limit `L`, convergence of the roots
gives `a n ≤ ρ ^ n` eventually, and `ExponentialBound.of_eventually` absorbs the finite prefix into
a constant, so `exponentialRate a ≤ ρ`; density then yields `exponentialRate a ≤ L`.  Conversely, an
exponential bound `a n ≤ C * ρ ^ n` gives `a n ^ (1/n) ≤ C ^ (1/n) * ρ` for `n ≥ 1`, and the right
side converges to `ρ`, so `L ≤ ρ` for every admissible base. -/
theorem exponentialRate_eq_submultiplicativeLimit {a : ℕ → ℕ} (hone : ∀ n, 1 ≤ a n)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n) :
    exponentialRate a = submultiplicativeLimit fun n ↦ (a n : ℝ) := by
  set w : ℕ → ℝ := fun n ↦ (a n : ℝ) with hw
  have hwpos : ∀ n, 0 < w n := fun n ↦ by
    have := hone n
    simp only [hw]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hwone : ∀ n, 1 ≤ w n := fun n ↦ by
    simp only [hw]
    exact_mod_cast hone n
  have hwsub : Submultiplicative w := fun m n ↦ by
    simp only [hw]
    exact_mod_cast hsub m n
  have htend : Tendsto (nthRootSeq w) atTop (𝓝 (submultiplicativeLimit w)) :=
    hwsub.tendsto_nthRootSeq hwpos zero_lt_one fun n ↦ by simpa using hwone n
  have hL1 : (1 : ℝ) ≤ submultiplicativeLimit w := one_le_submultiplicativeLimit hwone
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun ρ hρ ↦ ?_
    have hρpos : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one (hL1.trans hρ.le)
    refine exponentialRate_le (ExponentialBound.of_eventually hρpos zero_lt_one ?_)
    filter_upwards [htend.eventually (gt_mem_nhds hρ), eventually_ge_atTop 1] with n hn hn1
    rw [one_mul]
    calc (a n : ℝ) = nthRootSeq w n ^ n :=
          (Real.rpow_inv_natCast_pow (hwpos n).le (by omega)).symm
      _ ≤ ρ ^ n := pow_le_pow_left₀ (nthRootSeq_nonneg (fun k ↦ (hwpos k).le) n) hn.le n
  · refine le_csInf (exists_exponentialBound_of_submultiplicative hone hsub) ?_
    rintro ρ ⟨hρ0, C, hC, hbound⟩
    have hCtend : Tendsto (fun n : ℕ ↦ C ^ ((n : ℝ)⁻¹) * ρ) atTop (𝓝 ρ) := by
      simpa using (tendsto_const_rpow_inv_natCast hC).mul_const ρ
    refine le_of_tendsto_of_tendsto htend hCtend ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    calc nthRootSeq w n ≤ (C * ρ ^ n) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (hwpos n).le (hbound n) (by positivity)
      _ = C ^ ((n : ℝ)⁻¹) * ρ := by
          rw [Real.mul_rpow hC.le (by positivity), Real.pow_rpow_inv_natCast hρ0 (by omega)]

/-! ### Trading a large real exponent for the square

The following is pure real arithmetic, but it is the arithmetic step that turns an extraction of
`F` copies of an `a x a x a` matrix-multiplication tensor out of an `f`-th power into the
*balanced* bound the independence-number barrier consumes.  Intended client: milestone **M6**
(`Examples/CoppersmithWinogradEasyCoordinate.lean`), where the extraction exponent `f` is a real
number rather than `2`; the tensor-side statement it feeds is
`CoordinateGalacticCertificate.sq_le_asymptoticIndependenceNumber_pow` in
`MatrixMultiplication/IndependenceBarrier.lean`, which does not itself use this lemma.  Nothing
about tensors is involved here.
-/

/-- **Taking the `2/f`-th root of a bound `R ≤ F · M^f`.**  For `F, M ≥ 1` and a real exponent
`f ≥ 2`,

```text
R ≤ F · M^f   implies   R^{2/f} ≤ F · M².
```

The nonnegativity hypothesis on `R` is not removable: for `R < 0` the real power `R^{2/f}` is
`|R|^{2/f} · cos (2π/f)`, which is positive and unbounded once `f > 4`, while the hypothesis
`R ≤ F · M^f` puts no lower bound on `R`.

Proof sketch: `x ↦ x^{2/f}` is monotone on the nonnegatives, so `R^{2/f} ≤ (F · M^f)^{2/f}`, and
the right-hand side factors as `F^{2/f} · M^{f · (2/f)} = F^{2/f} · M²`.  Since `F ≥ 1` and
`2/f ≤ 1`, the remaining factor `F^{2/f}` is at most `F`. -/
theorem rpow_two_div_le_of_le_mul_rpow {R F M f : ℝ} (hR : 0 ≤ R) (hF : 1 ≤ F) (hM : 1 ≤ M)
    (hf : 2 ≤ f) (h : R ≤ F * M ^ f) : R ^ (2 / f) ≤ F * M ^ 2 := by
  have hf0 : (0 : ℝ) < f := lt_of_lt_of_le (by norm_num) hf
  have hF0 : (0 : ℝ) < F := lt_of_lt_of_le one_pos hF
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hexp : (0 : ℝ) ≤ 2 / f := by positivity
  have hcancel : f * (2 / f) = 2 := by field_simp
  have hsq : M ^ (2 : ℝ) = M ^ (2 : ℕ) := Real.rpow_two M
  have hfactor : (F * M ^ f) ^ (2 / f) = F ^ (2 / f) * M ^ (2 : ℕ) := by
    rw [Real.mul_rpow hF0.le (Real.rpow_nonneg hM0.le f), ← Real.rpow_mul hM0.le, hcancel, hsq]
  have hstep : R ^ (2 / f) ≤ F ^ (2 / f) * M ^ (2 : ℕ) := by
    rw [← hfactor]
    exact Real.rpow_le_rpow hR h hexp
  have hbase : F ^ (2 / f) ≤ F := by
    have hle : (2 : ℝ) / f ≤ 1 := (div_le_one hf0).mpr hf
    simpa using Real.rpow_le_rpow_of_exponent_le hF hle
  exact hstep.trans (mul_le_mul_of_nonneg_right hbase (by positivity))

end AlgebraicComplexity.Growth
