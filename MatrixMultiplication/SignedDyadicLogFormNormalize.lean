/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormAlgebra

/-!
# Normalization of signed dyadic logarithm forms

Insertion combines equal logarithm arguments and removes zero coefficients.  These structural
normalization operations preserve the represented real value.
-/

namespace MatrixMultiplication.SignedDyadicLogForm

noncomputable section

namespace Form

theorem termsValue_insert (bits : ℕ) (term : Term) (terms : List Term) :
    termsValue bits (insert term terms) = termValue bits term + termsValue bits terms := by
  rcases term with ⟨termArgument, termCoefficient⟩
  induction terms with
  | nil =>
      by_cases hzero : termCoefficient = 0
      · simp [insert, hzero, termsValue, termValue]
      · simp [insert, hzero, termsValue]
  | cons head tail ih =>
      rcases head with ⟨headArgument, headCoefficient⟩
      by_cases hzero : termCoefficient = 0
      · simp [insert, hzero, termsValue, termValue]
      · by_cases hlt : termArgument < headArgument
        · simp [insert, hzero, hlt, termsValue]
        · by_cases heq : termArgument = headArgument
          · subst headArgument
            by_cases hsum : termCoefficient + headCoefficient = 0
            · have hcancel :
                  termValue bits ⟨termArgument, termCoefficient⟩ +
                    termValue bits ⟨termArgument, headCoefficient⟩ = 0 := by
                  rw [← termValue_add_coefficient]
                  rw [hsum, termValue_zero_coefficient]
              simp only [insert, hzero, hlt, if_false, if_true, hsum,
                termsValue, List.map_cons, List.sum_cons]
              change
                (List.map (termValue bits) tail).sum =
                  termValue bits ⟨termArgument, termCoefficient⟩ +
                    (termValue bits ⟨termArgument, headCoefficient⟩ +
                      (List.map (termValue bits) tail).sum)
              rw [← add_assoc, hcancel, zero_add]
            · simp only [insert, hzero, hlt, hsum, if_false, if_true,
                termsValue, List.map_cons, List.sum_cons]
              rw [termValue_add_coefficient]
              ring
          · simp only [insert, hzero, hlt, heq, if_false, termsValue,
              List.map_cons, List.sum_cons]
            change
              (List.map (termValue bits)
                (insert ⟨termArgument, termCoefficient⟩ tail)).sum =
                termValue bits ⟨termArgument, termCoefficient⟩ +
                  (List.map (termValue bits) tail).sum at ih
            rw [ih]
            ring

theorem termsValue_normalizeTerms (bits : ℕ) (terms : List Term) :
    termsValue bits (normalizeTerms terms) = termsValue bits terms := by
  induction terms with
  | nil => rfl
  | cons head tail ih =>
      change termsValue bits (insert head (List.foldr insert [] tail)) = _
      rw [termsValue_insert]
      change termsValue bits (List.foldr insert [] tail) = termsValue bits tail at ih
      rw [ih]
      rfl

theorem eval_normalize (bits : ℕ) (form : Form) :
    eval bits (normalize form) = eval bits form := by
  simp [eval, normalize, termsValue_normalizeTerms]

end Form

end

end MatrixMultiplication.SignedDyadicLogForm
