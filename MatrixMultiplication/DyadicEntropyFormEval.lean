/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropyFormDefs
import MatrixMultiplication.DyadicEntropyList
import MatrixMultiplication.SignedDyadicLogFormAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Real evaluation of dyadic signed-log forms

This module proves that the definition-only form constructors have their intended homogeneous
Shannon-entropy values and records the denominator-rescaling laws used by recursive evaluators.
It preserves the existing `DyadicEntropyForm` statements and proofs while importing list semantics
from `DyadicEntropyList`; it is a definition-preserving refactor, not a new paper result.

This module carries no claim of its own.  The homogeneous Shannon entropies it represents exactly
are the ones evaluated by the recursive Coppersmith--Winograd constituent analysis of
[alman2025more], `papers/sources/2404.16349/constituent.tex:113-147`, and by the dual certificate
of the Total-Weight manuscript, `better_bound/paper.tex`, `sec:dual` (lines 2274-2307).

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*.
-/

set_option autoImplicit false

namespace MatrixMultiplication.DyadicEntropyForm

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

/-- Evaluating the exact form of one dyadic numerator gives its Shannon-entropy summand.

Proof sketch: zero has both zero form and zero entropy; for a positive numerator, expand its
entropy as mass times the difference between denominator bits and the numerator's logarithm. -/
theorem entropyTermForm_eval (bits numerator : ℕ) :
    Form.eval bits (entropyTermForm bits numerator) = entropyTerm bits numerator := by
  by_cases hn : numerator = 0
  · subst numerator
    simp [entropyTermForm, entropyTerm_zero]
  · have hpos : 0 < numerator := Nat.pos_of_ne_zero hn
    rw [entropyTerm_eq hpos]
    simp only [entropyTermForm, hn, if_false, Form.eval, Form.termsValue,
      Form.termValue, SignedDyadicLogForm.log2Nat, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, Int.cast_neg, Int.cast_natCast]
    unfold mass
    push_cast
    ring

/-- Evaluating the sum of exact summand forms gives the serialized row's Shannon entropy. -/
theorem entropyForm_eval (bits : ℕ) (numerators : List ℕ) :
    Form.eval bits (entropyForm bits numerators) = entropyList bits numerators := by
  rw [entropyForm, Form.eval_sum]
  unfold entropyList
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro numerator _
  exact entropyTermForm_eval bits numerator

/-- Evaluating the exact homogeneous-entropy form gives the row's homogeneous entropy. -/
theorem weightedEntropyForm_eval (bits : ℕ) (numerators : List ℕ) :
    Form.eval bits (weightedEntropyForm bits numerators) =
      weightedEntropyList bits numerators := by
  rw [weightedEntropyForm, Form.eval_sub, entropyForm_eval, entropyTermForm_eval]
  rfl

/-- Adding `extra` denominator bits divides the value of an unchanged form by `2^extra`.

Proof sketch: factor the common extra power of two out of the constant and every logarithmic
term; induction on the term list factors it out of their sum. -/
theorem eval_at_add_bits (bits extra : ℕ) (form : Form) :
    Form.eval (bits + extra) form = Form.eval bits form / (2 : ℝ) ^ extra := by
  rcases form with ⟨constant, terms⟩
  unfold Form.eval Form.termsValue Form.termValue
  rw [pow_add]
  have hpow : (2 : ℝ) ^ extra ≠ 0 := by positivity
  have hterms :
      ((terms.map fun term ↦
          (term.coefficient : ℝ) / ((2 : ℝ) ^ bits * (2 : ℝ) ^ extra) *
            SignedDyadicLogForm.log2Nat term.argument).sum) =
        (terms.map fun term ↦
          (term.coefficient : ℝ) / (2 : ℝ) ^ bits *
            SignedDyadicLogForm.log2Nat term.argument).sum / (2 : ℝ) ^ extra := by
    induction terms with
    | nil => simp
    | cons term terms ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        field_simp
  rw [hterms]
  field_simp

/-- Scaling all coefficients by `2^extra` compensates for adding `extra` denominator bits. -/
theorem rescale_eval (bits extra : ℕ) (form : Form) :
    Form.eval (bits + extra) (rescale extra form) = Form.eval bits form := by
  rw [rescale, Form.eval_scaleNat, eval_at_add_bits]
  have hpow : (2 : ℝ) ^ extra ≠ 0 := by positivity
  push_cast
  field_simp

/-- Multiplying a form by an outer dyadic numerator and adding the outer denominator bits is
exactly multiplication by that represented outer mass. -/
theorem scaleNat_eval_add_bits (outerBits innerBits outerNumerator : ℕ) (form : Form) :
    Form.eval (innerBits + outerBits) (Form.scaleNat outerNumerator form) =
      mass outerBits outerNumerator * Form.eval innerBits form := by
  rw [Form.eval_scaleNat, eval_at_add_bits]
  unfold mass
  ring

/-- Weighting a row's exact homogeneous-entropy form by an outer dyadic mass evaluates to that
mass times the row's homogeneous entropy. -/
theorem scaleNat_weightedEntropyForm_eval
    (outerBits innerBits outerNumerator : ℕ) (numerators : List ℕ) :
    Form.eval (innerBits + outerBits)
        (Form.scaleNat outerNumerator (weightedEntropyForm innerBits numerators)) =
      mass outerBits outerNumerator * weightedEntropyList innerBits numerators := by
  rw [scaleNat_eval_add_bits, weightedEntropyForm_eval]

end

end MatrixMultiplication.DyadicEntropyForm
