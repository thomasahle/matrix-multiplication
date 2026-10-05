/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Balanced multinomial coefficients

Equal-multiplicity word classes are the basic finite objects behind tensor-power type selection.
This module isolates their elementary growth estimates from tensor algebra and from any named
laser-method client.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

/-- The multinomial coefficient of `m` letters, each occurring exactly `k` times. -/
def balancedMultinomial (m k : ℕ) : ℕ :=
  Nat.multinomial (Finset.univ : Finset (Fin m)) (fun _ ↦ k)

/-- Factorial specification of a balanced multinomial coefficient, stated without natural-number
division. -/
theorem balancedMultinomial_spec (m k : ℕ) :
    (Nat.factorial k) ^ m * balancedMultinomial m k = Nat.factorial (m * k) := by
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin m)) (fun _ ↦ k)
  simpa [balancedMultinomial, Finset.prod_const, Finset.sum_const,
    nsmul_eq_mul] using h

/-- A constant multiplicity vector on any `m`-element alphabet has the canonical balanced
multinomial cardinality. -/
theorem multinomial_const_eq_balanced {ι : Type*} [Fintype ι]
    (m k : ℕ) (hcard : Fintype.card ι = m) :
    Nat.multinomial (Finset.univ : Finset ι) (fun _ ↦ k) =
      balancedMultinomial m k := by
  classical
  have hι := Nat.multinomial_spec (Finset.univ : Finset ι) (fun _ ↦ k)
  have hι' : (Nat.factorial k) ^ m *
      Nat.multinomial (Finset.univ : Finset ι) (fun _ ↦ k) =
        Nat.factorial (m * k) := by
    simpa [Finset.prod_const, Finset.sum_const, nsmul_eq_mul, hcard] using hι
  apply Nat.mul_left_cancel (by positivity : 0 < (Nat.factorial k) ^ m)
  rw [hι', balancedMultinomial_spec]

/-- Exact step ratio for the balanced three-letter coefficient, expressed division-free. -/
theorem balancedMultinomial_three_recurrence (k : ℕ) :
    (k + 1) ^ 3 * balancedMultinomial 3 (k + 1) =
      (3 * k + 1) * (3 * k + 2) * (3 * k + 3) * balancedMultinomial 3 k := by
  have hk := balancedMultinomial_spec 3 k
  have hk1 := balancedMultinomial_spec 3 (k + 1)
  rw [Nat.factorial_succ] at hk1
  have hfac : Nat.factorial (3 * (k + 1)) =
      (3 * k + 3) * (3 * k + 2) * (3 * k + 1) * Nat.factorial (3 * k) := by
    rw [show 3 * (k + 1) = (3 * k + 2) + 1 by ring,
      Nat.factorial_succ,
      show 3 * k + 2 = (3 * k + 1) + 1 by omega,
      Nat.factorial_succ,
      show 3 * k + 1 = 3 * k + 1 by rfl,
      Nat.factorial_succ]
    ring
  rw [hfac, ← hk] at hk1
  apply Nat.mul_left_cancel (by positivity : 0 < (Nat.factorial k) ^ 3)
  calc
    (Nat.factorial k) ^ 3 *
        ((k + 1) ^ 3 * balancedMultinomial 3 (k + 1)) =
        ((k + 1) * Nat.factorial k) ^ 3 * balancedMultinomial 3 (k + 1) := by
      ring
    _ = (3 * k + 3) * (3 * k + 2) * (3 * k + 1) *
        ((Nat.factorial k) ^ 3 * balancedMultinomial 3 k) := hk1
    _ = (Nat.factorial k) ^ 3 *
        ((3 * k + 1) * (3 * k + 2) * (3 * k + 3) *
          balancedMultinomial 3 k) := by
      ring

/-- One recurrence step retains the base-`27` growth after paying a square polynomial factor. -/
theorem balancedMultinomial_three_growth_step (k : ℕ) :
    27 * k ^ 2 * balancedMultinomial 3 k ≤
      (k + 1) ^ 2 * balancedMultinomial 3 (k + 1) := by
  apply Nat.le_of_mul_le_mul_left (c := k + 1) ?_ (by omega)
  rw [show (k + 1) * ((k + 1) ^ 2 * balancedMultinomial 3 (k + 1)) =
      (k + 1) ^ 3 * balancedMultinomial 3 (k + 1) by ring,
    balancedMultinomial_three_recurrence]
  calc
    (k + 1) * (27 * k ^ 2 * balancedMultinomial 3 k) =
        ((k + 1) * (27 * k ^ 2)) * balancedMultinomial 3 k := by
      ring
    _ ≤ ((3 * k + 1) * (3 * k + 2) * (3 * k + 3)) *
        balancedMultinomial 3 k := Nat.mul_le_mul_right _ (by nlinarith)

/-- Explicit polynomial-loss lower bound for positive balanced three-letter types. -/
theorem two_mul_twentySeven_pow_le_nine_mul_sq_mul_balancedMultinomial_three
    (k : ℕ) (hk : 0 < k) :
    2 * 27 ^ k ≤ 9 * k ^ 2 * balancedMultinomial 3 k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [balancedMultinomial, Nat.multinomial, Nat.factorial]
  | succ k _hk ih =>
      calc
        2 * 27 ^ (k + 1) = 27 * (2 * 27 ^ k) := by ring
        _ ≤ 27 * (9 * k ^ 2 * balancedMultinomial 3 k) :=
          Nat.mul_le_mul_left 27 ih
        _ = 9 * (27 * k ^ 2 * balancedMultinomial 3 k) := by ring
        _ ≤ 9 * ((k + 1) ^ 2 * balancedMultinomial 3 (k + 1)) :=
          Nat.mul_le_mul_left 9 (balancedMultinomial_three_growth_step k)
        _ = 9 * (k + 1) ^ 2 * balancedMultinomial 3 (k + 1) := by ring

/-- All-index form of the balanced three-letter lower bound. -/
theorem two_mul_twentySeven_pow_le_nine_mul_succ_sq_mul_balancedMultinomial_three
    (k : ℕ) :
    2 * 27 ^ k ≤ 9 * (k + 1) ^ 2 * balancedMultinomial 3 k := by
  rcases k with _ | k
  · norm_num [balancedMultinomial, Nat.multinomial, Nat.factorial]
  · calc
      2 * 27 ^ (k + 1) ≤
          9 * (k + 1) ^ 2 * balancedMultinomial 3 (k + 1) :=
        two_mul_twentySeven_pow_le_nine_mul_sq_mul_balancedMultinomial_three
          (k + 1) (by omega)
      _ ≤ 9 * (k + 1 + 1) ^ 2 * balancedMultinomial 3 (k + 1) := by
        gcongr
        omega

end AlgebraicComplexity.WordType
