/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropy

/-!
# Real entropy semantics for dyadic numerator lists

This module is the lightweight semantic boundary between list-based certificate rows and the
finite-family entropy API.  It contains no signed logarithmic forms or exact-arithmetic checker
machinery, so counting and rate theorems can import it without paying for the numerical layer.
-/

namespace MatrixMultiplication.DyadicEntropyForm

open MatrixMultiplication.DyadicEntropy

noncomputable section

/-- Shannon entropy of a finite dyadic numerator list, without assuming normalization. -/
def entropyList (bits : ℕ) (numerators : List ℕ) : ℝ :=
  (numerators.map (entropyTerm bits)).sum

/-- Homogeneous entropy of a finite dyadic mass list. -/
def weightedEntropyList (bits : ℕ) (numerators : List ℕ) : ℝ :=
  entropyList bits numerators - entropyTerm bits numerators.sum

/-- Serializing a finite dyadic row in `Fin` order does not change its homogeneous entropy. -/
theorem weightedEntropyList_ofFn_eq_weightedEntropy
    {n : ℕ} (bits : ℕ) (numerator : Fin n → ℕ) :
    weightedEntropyList bits (List.ofFn numerator) =
      weightedEntropy bits numerator := by
  unfold weightedEntropyList entropyList weightedEntropy totalNumerator
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

end

end MatrixMultiplication.DyadicEntropyForm
