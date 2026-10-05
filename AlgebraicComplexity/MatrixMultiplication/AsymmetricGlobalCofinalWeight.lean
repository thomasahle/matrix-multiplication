/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalValue

/-!
# Cofinal weighted powers force a strict exponent bound

This is the loss-absorption step of [duan2023faster], section 6,
`eq:value_before_nth_root` to `eq:numeric_conclusion_g`
(`papers/sources/2210.10173/global_value.tex:269-309`).

The source is already assembled: this theorem neither symmetrizes it nor changes its rank
budget. One subexponential loss controls positive weighted powers at cofinally many positive
lengths. A positive interior rate absorbs the loss, after which the existing finite
`omega_lt_three_mul_of_hasTauWeight` theorem applies. No value supremum or attainment is assumed.

The concrete section 6.3 instance is in
`Examples/DuanWuZhouLevelTwoSharedCofinalWeight.lean`; its six orientations are paid for in both
the source rank budget and the per-repetition weight rate.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.AsymmetricGlobal

open _root_.AlgebraicComplexity.Tensor

universe u v

variable {F : Type u} [Field F]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- Cofinal positive weighted powers beating a rank budget after subexponential loss imply
`ω < 3τ`. This transcribes [duan2023faster]'s passage to the normalized rate: the fixed strict
interior rate `b` absorbs the loss before applying the finite weighted-power theorem. -/
theorem omega_lt_three_mul_of_cofinal_hasTauWeight
    {T : Tensor3 F V} {τ r a b : ℝ}
    (hrank : Tensor.asymptoticRank T ≤ r)
    (hb : 0 < b) (hrb : r < b) (hba : b < a)
    (hstages : ∃ loss : ℕ → ℝ, Growth.Subexponential loss ∧
      ∀ cutoff : ℕ, ∃ N : ℕ, cutoff ≤ N ∧ 0 < N ∧
        ∃ value : ℝ, 0 < value ∧ HasTauWeight F (Tensor.power T N) τ value ∧
          a ^ N ≤ loss N * value) :
    omega F < 3 * τ := by
  obtain ⟨loss, hloss, hcofinal⟩ := hstages
  have hratio : 1 < a / b := (one_lt_div hb).2 hba
  obtain ⟨cutoff, hcutoff⟩ := hloss.eventually_le_pow hratio
  obtain ⟨N, hNcutoff, hN, value, hvalue, hweight, hbound⟩ := hcofinal cutoff
  have hkey : a ^ N ≤ a ^ N / b ^ N * value := by
    calc
      a ^ N ≤ loss N * value := hbound
      _ ≤ (a / b) ^ N * value :=
        mul_le_mul_of_nonneg_right (hcutoff N hNcutoff) hvalue.le
      _ = a ^ N / b ^ N * value := by rw [div_pow]
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb N)] at hkey
  have hpow : b ^ N ≤ value :=
    le_of_mul_le_mul_left hkey (pow_pos (hb.trans hba) N)
  apply omega_lt_three_mul_of_hasTauWeight hN hvalue hrank hweight
  calc
    r < b := hrb
    _ = (b ^ N) ^ ((N : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hb.le hN.ne').symm
    _ ≤ value ^ ((N : ℝ)⁻¹) :=
      Real.rpow_le_rpow (pow_nonneg hb.le N) hpow (by positivity)

end AlgebraicComplexity.AsymmetricGlobal
