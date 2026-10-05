/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.MaximumEntropyDual

/-!
# Constant shifts of finite entropy-dual scores

The fixed-marginal maximum-entropy step in [duan2023faster], Algorithm
`alg:verify_sec_power`, Step `step:conv_prog_entr`
(`papers/sources/2210.10173/second_power.tex:536-563`), is bounded by the existing
finite Gibbs dual. Clearing denominators of its positive coordinate factors adds
a constant to the logarithmic score. The partition logarithm and the expectation
both increase by that constant when the reference has total mass one.

These identities only change the representation of the same witness; they do not
change the structural support or require an optimizer. In particular, a state of
zero reference mass remains in the partition. The bit/nat identity below exposes
the existing coordinate-potential expression without introducing another dual.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.MaximumEntropyDual

variable {A X Y Z : Type*}

/-- A constant score shift multiplies the entire partition by its exponential. -/
theorem partition_add_const [Fintype A] (score : A → ℝ) (c : ℝ) :
    partition (fun a ↦ score a + c) = partition score * Real.exp c := by
  simp only [partition, Real.exp_add, Finset.sum_mul]

/-- A constant score shift cancels from the dual when the reference has mass one. -/
theorem logPartition_sub_expectation_add_const [Fintype A] [Nonempty A]
    (p score : A → ℝ) (c : ℝ) (hpsum : ∑ a, p a = 1) :
    Real.log (partition (fun a ↦ score a + c)) - ∑ a, p a * (score a + c) =
      Real.log (partition score) - ∑ a, p a * score a := by
  rw [partition_add_const, Real.log_mul (partition_pos score).ne' (Real.exp_pos c).ne',
    Real.log_exp]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hpsum]
  ring

/-- Natural-log coordinate potentials, divided by `log 2`, give the same dual in bits. -/
theorem coordinateDualBits_div_log_two
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ) :
    coordinateDualBits coordX coordY coordZ p
        (fun x ↦ uX x / Real.log 2) (fun y ↦ uY y / Real.log 2)
        (fun z ↦ uZ z / Real.log 2) =
      (Real.log (partition (coordinateScore coordX coordY coordZ uX uY uZ)) -
        ∑ a, p a * coordinateScore coordX coordY coordZ uX uY uZ a) / Real.log 2 := by
  have htwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hscore :
      (fun a ↦ Real.log 2 * coordinateScore coordX coordY coordZ
        (fun x ↦ uX x / Real.log 2) (fun y ↦ uY y / Real.log 2)
        (fun z ↦ uZ z / Real.log 2) a) =
      coordinateScore coordX coordY coordZ uX uY uZ := by
    funext a
    simp only [coordinateScore]
    field_simp
  rw [coordinateDualBits, partitionTwo, hscore, coordinateScore_expectation]
  simp_rw [div_mul_eq_mul_div, div_eq_mul_inv, ← Finset.sum_mul]
  ring

end AlgebraicComplexity.MaximumEntropyDual
