/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedRectangular
import OAI.LinearAlgebra.MatrixMultiplication.Duality.ExponentBound
import AlgebraicComplexity.MatrixMultiplication.FieldExtension
import AlgebraicComplexity.MatrixMultiplication.RectangularInterpolation
import OpenAIBridge.ArithmeticPrograms
import OpenAIBridge.NineQuarters

/-!
# The vendored rectangular bounds, for this repository's exponents

Besides `ω ≤ 9/4`, OpenAI's Lean development (`openai/math`, directory
`lean/OAI/LinearAlgebra/MatrixMultiplication`) proves two statements about rectangular matrix
multiplication over `ℂ`, in its arithmetic-program model:

* `Arithmetic.rectangularOmega ℂ 0.709 < 2.092`: multiplying an `n × n^0.709` matrix by an
  `n^0.709 × n` matrix;
* `0.465 < Arithmetic.complexAlpha`: the dual exponent, the largest `k` for which
  `n × n^k` by `n^k × n` multiplication has exponent `2`.

The modules they need are vendored under `ThirdParty/OAI/` next to the all-fields `9/4`
development (see `ThirdParty/README.md`).  This file restates both for the rank-based exponents
of this repository, `rectangularOmega` and `rectangularAlpha`, through the comparison of models
in `OpenAIBridge/ArithmeticPrograms.lean`.

## Main results

* `rectangularOmega_complex_lt`: `rectangularOmega ℂ (709/1000) < 523/250`.
* `rectangularOmega_complex_eq_two`: `rectangularOmega ℂ (4651/10000) = 2`.
* `rectangularAlpha_complex_gt`: `93/200 < rectangularAlpha ℂ`.
* `rectangularOmega_lt_of_charZero`, `rectangularOmega_eq_two_of_charZero`,
  `rectangularAlpha_gt_of_charZero`: the same three statements over every field of
  characteristic zero, by this repository's invariance of the rectangular exponents under field
  extensions.
* `rectangularOmega_le_chord_of_charZero`: `ω(1, κ, 1) ≤ 2 + (κ − 0.4651) / (4 · 0.5349)` for
  `0.4651 ≤ κ ≤ 1`, the dual-exponent bound and `ω ≤ 9/4` joined by convexity.

For comparison, the best dual-exponent bound proved in this repository itself is Coppersmith's
`α > 0.294` (`coppersmith1997_alpha_gt`).

## Trust

As in `OpenAIBridge/NineQuarters.lean`: the statements are this repository's, the proofs are the
vendored ones, and the enforcing audit is in `OpenAIBridge/Audit.lean`.  Upstream these two
results are about `ℂ` only; the passage to every field of characteristic zero at the end of this
file is this repository's.  Nothing is claimed in positive characteristic.
-/

namespace AlgebraicComplexity.OpenAIBridge

open OAI.MatrixMultiplication

/-- **`ω(1, 0.709, 1) < 2.092` over `ℂ`**, for the rank-based rectangular exponent of this
repository.  The mathematical content is the vendored
`CW75ReorderedRectangular.rectangularOmega_lt_target`. -/
theorem rectangularOmega_complex_lt : rectangularOmega ℂ (709 / 1000) < 523 / 250 :=
  (rectangularOmega_le_arithmeticRectangularOmega ℂ _).trans_lt
    CW75ReorderedRectangular.rectangularOmega_lt_target

/-- **`ω(1, 0.4651, 1) = 2` over `ℂ`**: multiplying an `n × n^0.4651` matrix by an
`n^0.4651 × n` matrix has exponent exactly `2`.  The upper bound is the vendored
`DualExponentBound.fixedAspect_omega_eq_two`; the lower bound is this repository's. -/
theorem rectangularOmega_complex_eq_two : rectangularOmega ℂ (4651 / 10000) = 2 := by
  refine le_antisymm ?_ (two_le_rectangularOmega ℂ _)
  have h := rectangularOmega_le_arithmeticRectangularOmega ℂ DualExponentBound.fixedAspect
  rw [DualExponentBound.fixedAspect_omega_eq_two] at h
  exact h

/-- **The dual exponent of matrix multiplication over `ℂ` exceeds `0.465`**, for this
repository's `rectangularAlpha`. -/
theorem rectangularAlpha_complex_gt : (93 : ℝ) / 200 < rectangularAlpha ℂ := by
  have hmem : (4651 / 10000 : ℝ) ∈ {κ : ℝ | 0 ≤ κ ∧ rectangularOmega ℂ κ = 2} :=
    ⟨by norm_num, rectangularOmega_complex_eq_two⟩
  have h := le_csSup (bddAbove_setOf_rectangularOmega_eq_two ℂ) hmem
  have hlt : (93 : ℝ) / 200 < 4651 / 10000 := by norm_num
  exact hlt.trans_le h

/-! ### Every field of characteristic zero

The vendored statements are about `ℂ`.  The rectangular exponents of this repository are
invariant under field extensions (`rectangularOmega_eq_of_fieldExtension`,
`rectangularAlpha_eq_of_fieldExtension`, in
`AlgebraicComplexity/MatrixMultiplication/FieldExtension.lean`), so both bounds hold over every
field of characteristic zero: such a field and `ℂ` both extend `ℚ`. -/

universe u

/-- **`ω(1, 0.709, 1) < 2.092` over every field of characteristic zero.** -/
theorem rectangularOmega_lt_of_charZero (K : Type u) [Field K] [CharZero K] :
    rectangularOmega K (709 / 1000) < 523 / 250 := by
  rw [rectangularOmega_eq_rectangularOmega_rat K (by norm_num),
    ← rectangularOmega_eq_rectangularOmega_rat ℂ (by norm_num)]
  exact rectangularOmega_complex_lt

/-- **`ω(1, κ, 1) = 2` for every `0 ≤ κ ≤ 0.4651`, over every field of characteristic zero.** -/
theorem rectangularOmega_eq_two_of_charZero (K : Type u) [Field K] [CharZero K] {κ : ℝ}
    (hκ : κ ≤ 4651 / 10000) : rectangularOmega K κ = 2 := by
  refine rectangularOmega_eq_two_of_le K hκ ?_
  rw [rectangularOmega_eq_rectangularOmega_rat K (by norm_num),
    ← rectangularOmega_eq_rectangularOmega_rat ℂ (by norm_num)]
  exact rectangularOmega_complex_eq_two

/-- **The dual exponent exceeds `0.465` over every field of characteristic zero.** -/
theorem rectangularAlpha_gt_of_charZero (K : Type u) [Field K] [CharZero K] :
    (93 : ℝ) / 200 < rectangularAlpha K := by
  rw [rectangularAlpha_eq_rectangularAlpha_rat K, ← rectangularAlpha_eq_rectangularAlpha_rat ℂ]
  exact rectangularAlpha_complex_gt

/-- **An upper envelope for the rectangular exponent in characteristic zero**: for
`0.4651 ≤ κ ≤ 1`,

```text
ω(1, κ, 1)  ≤  2 + (κ − 0.4651) / (4 · (1 − 0.4651)).
```

This is the chord of the convex function `κ ↦ ω(κ)` between `ω(0.4651) = 2` and
`ω(1) = ω ≤ 9/4`: the dual-exponent bound and the square bound combined by this repository's
convexity theorem (`rectangularOmega_le_interpolation_of_eq_two`). -/
theorem rectangularOmega_le_chord_of_charZero (K : Type u) [Field K] [CharZero K] {κ : ℝ}
    (h₀ : 4651 / 10000 ≤ κ) (h₁ : κ ≤ 1) :
    rectangularOmega K κ ≤ 2 + (κ - 4651 / 10000) / (4 * (1 - 4651 / 10000)) := by
  have h := rectangularOmega_le_interpolation_of_eq_two K (κ₀ := 4651 / 10000) (by norm_num)
    (by norm_num) (rectangularOmega_eq_two_of_charZero K le_rfl) h₀ h₁
  have h9 := omega_le_nine_quarters K
  have ht : 0 ≤ (κ - 4651 / 10000) / (1 - 4651 / 10000 : ℝ) :=
    div_nonneg (by linarith) (by norm_num)
  calc rectangularOmega K κ
      ≤ 2 + (omega K - 2) * (κ - 4651 / 10000) / (1 - 4651 / 10000) := h
    _ = 2 + (omega K - 2) * ((κ - 4651 / 10000) / (1 - 4651 / 10000)) := by ring
    _ ≤ 2 + (1 / 4) * ((κ - 4651 / 10000) / (1 - 4651 / 10000)) := by nlinarith
    _ = 2 + (κ - 4651 / 10000) / (4 * (1 - 4651 / 10000)) := by ring

end AlgebraicComplexity.OpenAIBridge
