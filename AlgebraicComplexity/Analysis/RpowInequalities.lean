/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Order facts for the Schönhage bootstrap

Every statement below is what a *bootstrapping* rate argument needs.  Schönhage's device proves
a rate inequality first with the growth constant raised to a fractional exponent
`θ = ω/τ ∈ (0, 1]`, where `τ > ω` is an admissible exponent, and only then lets `τ` decrease to
`ω`.  Three elementary manipulations recur along the way:

* `le_rpow_inv_of_rpow_mul_le` inverts the fractional power, turning `x^θ · Y ≤ Z` into
  `x ≤ (Z/Y)^(1/θ)`;
* `rpow_le_add_one` keeps a subexponential loss subexponential after the exponent is applied, by
  replacing `x^θ` with the `θ`-free majorant `x + 1`;
* `le_of_rpow_div_mul_le` performs the limit `τ ↓ ω` itself, removing the fractional exponent from
  the finished inequality.

The same file also carries the elementary exchange between natural powers and one rational
exponent, `rpow_div_le_of_pow_le_pow` and `le_rpow_div_of_pow_le_pow`: an exact inequality between
natural powers `x ^ j` and `y ^ N` is the standard certificate for a bound on `x ^ (j / N)`, and
every barrier client that has to compare a rational exponent with a closed-form quantity needs one
of the two directions.

Their clients are the two rectangular Huang--Pan rate modules,
`Examples/CoppersmithWinogradEasyRectangularRate.lean` and
`Examples/CoppersmithWinogradRectangularRate.lean`, and the generalized Coppersmith--Winograd
barrier, all of which ran identical private copies before.

## Position in the library

Layer 2 (`AlgebraicComplexity/Analysis/`), a leaf: it imports only `Real.rpow` from Mathlib and
mentions no entropy, no tensor, and no matrix-multiplication construction.
-/

namespace AlgebraicComplexity.Analysis

/-- **Dividing a natural exponent out of a power inequality.**  An exact inequality `x ^ j ≤ y ^ N`
between natural powers is exactly a bound `x ^ (j / N) ≤ y` on the rational power.

This is the certificate form in which a numerical barrier argument produces bounds on rational
powers: the exponent `j / N` never has to be approximated. -/
theorem rpow_div_le_of_pow_le_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {j N : ℕ} (hN : N ≠ 0)
    (h : x ^ j ≤ y ^ N) : x ^ ((j : ℝ) / (N : ℝ)) ≤ y := by
  refine le_of_pow_le_pow_left₀ hN hy ?_
  rw [← Real.rpow_natCast (x ^ ((j : ℝ) / (N : ℝ))) N, ← Real.rpow_mul hx,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hN), Real.rpow_natCast]
  exact h

/-- **The opposite direction.**  From `y ^ N ≤ x ^ j` one gets `y ≤ x ^ (j / N)`.

Nonnegativity of `y` is not a hypothesis: it follows from the conclusion when it holds at all, and
the rational power on the right is nonnegative regardless. -/
theorem le_rpow_div_of_pow_le_pow {x y : ℝ} (hx : 0 ≤ x) {j N : ℕ} (hN : N ≠ 0)
    (h : y ^ N ≤ x ^ j) : y ≤ x ^ ((j : ℝ) / (N : ℝ)) := by
  refine le_of_pow_le_pow_left₀ hN (Real.rpow_nonneg hx _) ?_
  rw [← Real.rpow_natCast (x ^ ((j : ℝ) / (N : ℝ))) N, ← Real.rpow_mul hx,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hN), Real.rpow_natCast]
  exact h

/-- **Inverting a fractional power in an inequality.**  From `x ^ θ * Y ≤ Z` with `θ > 0` and
`Y > 0` one recovers `x ≤ (Z / Y) ^ (1 / θ)`. -/
theorem le_rpow_inv_of_rpow_mul_le {x Y Z θ : ℝ} (hx : 0 ≤ x) (hY : 0 < Y) (hθ : 0 < θ)
    (h : x ^ θ * Y ≤ Z) : x ≤ (Z / Y) ^ (1 / θ) := by
  have h1 : x ^ θ ≤ Z / Y := (le_div_iff₀ hY).mpr h
  have h2 : (x ^ θ) ^ (1 / θ) ≤ (Z / Y) ^ (1 / θ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hx θ) h1 (by positivity)
  rwa [← Real.rpow_mul hx, mul_one_div, div_self hθ.ne', Real.rpow_one] at h2

/-- **A fractional power is dominated by the value plus one.**  For `0 ≤ θ ≤ 1` and `0 ≤ x`,
`x ^ θ ≤ x + 1`.  Since the right-hand side no longer mentions `θ`, a subexponential bound
survives the bootstrap exponent unchanged. -/
theorem rpow_le_add_one {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ^ θ ≤ x + 1 := by
  rcases le_total x 1 with h | h
  · have : x ^ θ ≤ 1 := Real.rpow_le_one hx h hθ0
    linarith
  · have : x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hθ1
    rw [Real.rpow_one] at this
    linarith

/-- **The `τ ↓ ω` limit of Schönhage's bootstrap.**  A rate argument whose compression scale is
built from an admissible exponent `τ > ω` proves its target inequality only with the growth
constant `G` raised to `θ = ω/τ < 1`.  Because the whole family of such inequalities is available,
the exponent can be removed: if `G ^ (ω/τ) · Y ≤ ρ` for *every* `τ > ω`, then `G · Y ≤ ρ`.

Positivity of `ρ` is not a hypothesis; it follows from the family at `τ = 2ω`. -/
theorem le_of_rpow_div_mul_le {G Y ρ ω : ℝ} (hG : 0 < G) (hY : 0 < Y) (hω : 0 < ω)
    (h : ∀ τ : ℝ, ω < τ → G ^ (ω / τ) * Y ≤ ρ) : G * Y ≤ ρ := by
  have hρ : 0 < ρ := by
    have hτ := h (2 * ω) (by linarith)
    have hlhs : (0 : ℝ) < G ^ (ω / (2 * ω)) * Y := mul_pos (Real.rpow_pos_of_pos hG _) hY
    linarith
  set V : ℝ := ρ / Y with hVdef
  have hVpos : 0 < V := div_pos hρ hY
  -- The `δ`-family of bootstrap exponents `τ = ω(1+δ)`.
  have hδ : ∀ δ : ℝ, 0 < δ → Real.log G ≤ (1 + δ) * Real.log V := by
    intro δ hδpos
    have hpos : (0 : ℝ) < 1 + δ := by linarith
    have hrate := h (ω * (1 + δ)) (by nlinarith)
    have hratio : ω / (ω * (1 + δ)) = 1 / (1 + δ) := by field_simp
    rw [hratio] at hrate
    have hle : G ^ (1 / (1 + δ)) ≤ V := (le_div_iff₀ hY).mpr hrate
    have hlogle : Real.log (G ^ (1 / (1 + δ))) ≤ Real.log V :=
      Real.log_le_log (Real.rpow_pos_of_pos hG _) hle
    rw [Real.log_rpow hG] at hlogle
    calc
      Real.log G = (1 + δ) * ((1 / (1 + δ)) * Real.log G) := by field_simp
      _ ≤ (1 + δ) * Real.log V := mul_le_mul_of_nonneg_left hlogle hpos.le
  have hlogGV : Real.log G ≤ Real.log V := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    set δ : ℝ := ε / (|Real.log V| + 1) with hδdef
    have habs : (0 : ℝ) < |Real.log V| + 1 := by positivity
    have hδpos : 0 < δ := by
      rw [hδdef]
      positivity
    have hmain := hδ δ hδpos
    have hbound : δ * Real.log V ≤ ε := by
      have h1 : δ * Real.log V ≤ δ * |Real.log V| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hδpos.le
      have h2 : δ * |Real.log V| ≤ ε := by
        rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ habs]
        nlinarith [abs_nonneg (Real.log V), hε.le]
      linarith
    nlinarith [hmain, hbound]
  have hGV : G ≤ V := by
    have h1 : Real.exp (Real.log G) ≤ Real.exp (Real.log V) := Real.exp_le_exp.mpr hlogGV
    rwa [Real.exp_log hG, Real.exp_log hVpos] at h1
  rwa [hVdef, le_div_iff₀ hY] at hGV

end AlgebraicComplexity.Analysis
