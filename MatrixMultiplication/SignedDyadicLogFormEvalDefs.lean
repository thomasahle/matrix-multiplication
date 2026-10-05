/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormDefs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Real evaluation of signed dyadic logarithm forms

This module defines only the real semantics of exact forms.  It contains no theorem, finite
indexed sum, normalization code, or certificate-specific entropy development.
-/

namespace MatrixMultiplication.SignedDyadicLogForm

noncomputable section

/-- Base-two logarithm of a natural-number argument, using Lean's real-log convention at zero. -/
def log2Nat (argument : ℕ) : ℝ :=
  Real.log (argument : ℝ) / Real.log 2

namespace Form

/-- Real value of one integer-weighted logarithm term at a dyadic denominator. -/
def termValue (bits : ℕ) (term : Term) : ℝ :=
  (term.coefficient : ℝ) / (2 : ℝ) ^ bits * log2Nat term.argument

/-- Sum of the real values of a term list. -/
def termsValue (bits : ℕ) (terms : List Term) : ℝ :=
  (terms.map (termValue bits)).sum

/-- Real value represented by an exact signed-log form. -/
def eval (bits : ℕ) (form : Form) : ℝ :=
  (form.constantNumerator : ℝ) / (2 : ℝ) ^ bits +
    termsValue bits form.terms

end Form

end

end MatrixMultiplication.SignedDyadicLogForm
