/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormEvalDefs
import Mathlib.Tactic.Ring

/-!
# Additive algebra of signed dyadic logarithm forms

The executable constructors in `SignedDyadicLogFormDefs` respect real evaluation.  Normalization
is deliberately proved in a separate module because its insertion induction is substantially
heavier than these additive and scaling laws.
-/

open scoped BigOperators

namespace MatrixMultiplication.SignedDyadicLogForm

noncomputable section

namespace Form

/-- Two exact signed-log forms are equal when their rational constants and term lists agree.

Proof sketch: destruct both structures; the two field equalities identify their constructors. -/
@[ext] theorem ext {left right : Form}
    (hconstant : left.constantNumerator = right.constantNumerator)
    (hterms : left.terms = right.terms) : left = right := by
  cases left
  cases right
  simp_all

/-- Finite natural-coefficient logarithm sum used by compact certificate families. -/
def natLogSum {count : ℕ} (bits : ℕ)
    (argument coefficient : Fin count → ℕ) : ℝ :=
  ∑ index, (coefficient index : ℝ) / (2 : ℝ) ^ bits * log2Nat (argument index)

theorem eval_ofNegativeFamily {count : ℕ} (bits : ℕ) (constantNumerator : ℤ)
    (argument coefficient : Fin count → ℕ) :
    eval bits (ofNegativeFamily constantNumerator argument coefficient) =
      (constantNumerator : ℝ) / (2 : ℝ) ^ bits -
        natLogSum bits argument coefficient := by
  unfold eval ofNegativeFamily termsValue natLogSum
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, termValue, Int.cast_neg, Int.cast_natCast]
  simp_rw [neg_div, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

@[simp] theorem eval_zero (bits : ℕ) : eval bits zero = 0 := by
  simp [eval, zero, termsValue]

theorem eval_add (bits : ℕ) (left right : Form) :
    eval bits (add left right) = eval bits left + eval bits right := by
  simp only [eval, add, termsValue, List.map_append, List.sum_append, Int.cast_add]
  ring

theorem termValue_zero_coefficient (bits argument : ℕ) :
    termValue bits ⟨argument, 0⟩ = 0 := by
  simp [termValue]

theorem termValue_add_coefficient (bits argument : ℕ) (left right : ℤ) :
    termValue bits ⟨argument, left + right⟩ =
      termValue bits ⟨argument, left⟩ + termValue bits ⟨argument, right⟩ := by
  simp only [termValue, Int.cast_add]
  ring

theorem termsValue_neg (bits : ℕ) (terms : List Term) :
    termsValue bits (terms.map fun term => ⟨term.argument, -term.coefficient⟩) =
      -termsValue bits terms := by
  induction terms with
  | nil => simp [termsValue]
  | cons head tail ih =>
      change termValue bits ⟨head.argument, -head.coefficient⟩ +
          termsValue bits (tail.map fun term => ⟨term.argument, -term.coefficient⟩) =
        -(termValue bits head + termsValue bits tail)
      rw [ih]
      simp only [termValue, Int.cast_neg]
      ring

theorem eval_neg (bits : ℕ) (form : Form) :
    eval bits (neg form) = -eval bits form := by
  simp only [eval, neg, Int.cast_neg, termsValue_neg]
  ring

theorem eval_sub (bits : ℕ) (left right : Form) :
    eval bits (sub left right) = eval bits left - eval bits right := by
  rw [sub, eval_add, eval_neg]
  ring

/-- The constant numerator of a finite form sum is the integer sum of the component constants.

Proof sketch: induct on the list and unfold the exact `Form.add` operation at the head. -/
theorem sum_constantNumerator (forms : List Form) :
    (sum forms).constantNumerator =
      (forms.map fun form ↦ form.constantNumerator).sum := by
  induction forms with
  | nil => rfl
  | cons form forms ih =>
      simp only [sum, add, List.map_cons, List.sum_cons]
      rw [ih]

/-- The logarithmic terms of a finite form sum are the concatenation of the component term lists.

Proof sketch: induct on the list; `Form.add` appends term lists, exactly as `List.flatten` does. -/
theorem sum_terms (forms : List Form) :
    (sum forms).terms = (forms.map fun form ↦ form.terms).flatten := by
  induction forms with
  | nil => rfl
  | cons form forms ih =>
      simp only [sum, add, List.map_cons, List.flatten_cons]
      rw [ih]

theorem eval_sum (bits : ℕ) (forms : List Form) :
    eval bits (sum forms) = (forms.map (eval bits)).sum := by
  induction forms with
  | nil => simp [sum]
  | cons head tail ih => simp [sum, eval_add, ih]

theorem termsValue_scaleNat (bits scalar : ℕ) (terms : List Term) :
    termsValue bits
        (terms.map fun term => ⟨term.argument, scalar * term.coefficient⟩) =
      scalar * termsValue bits terms := by
  induction terms with
  | nil => simp [termsValue]
  | cons head tail ih =>
      change termValue bits ⟨head.argument, scalar * head.coefficient⟩ +
          termsValue bits
            (tail.map fun term => ⟨term.argument, scalar * term.coefficient⟩) =
        scalar * (termValue bits head + termsValue bits tail)
      rw [ih]
      simp only [termValue, Int.cast_mul, Int.cast_natCast]
      ring

theorem eval_scaleNat (bits scalar : ℕ) (form : Form) :
    eval bits (scaleNat scalar form) = scalar * eval bits form := by
  simp only [eval, scaleNat, Int.cast_mul, Int.cast_natCast,
    termsValue_scaleNat]
  ring

end Form

end

end MatrixMultiplication.SignedDyadicLogForm
