/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.AsymptoticsDefs
import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.Tensor.RankDefs

/-!
# Lightweight definitions of the matrix-multiplication exponent

This module contains only the rank sequence, its polynomial-bound predicate, and the resulting
infimum `omega`.  Bounds and structural theorems live in
`MatrixMultiplication/Exponent.lean`, whose old import path continues to re-export these names.

Keeping the definitions in a leaf lets finite value and laser-rate certificates mention `omega`
without loading conciseness, recursive algorithms, or the full discrete asymptotics theorem
library.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

variable (K : Type u) [CommSemiring K]

/-- Ordinary ranks of square matrix-multiplication tensors over `K`. -/
noncomputable def squareMatrixRankSequence (n : ℕ) : ℕ :=
  rank (matrixMultiplication (K := K) n n n)

/-- `τ` is a polynomial upper bound for square matrix-multiplication rank over `K`. -/
abbrev MatrixExponentLE (τ : ℝ) : Prop :=
  PolynomialBound (squareMatrixRankSequence K) τ

/-- The matrix-multiplication exponent over `K`. -/
noncomputable def matrixMultiplicationExponent : ℝ :=
  polynomialExponent (squareMatrixRankSequence K)

/-- Short conventional name for the matrix-multiplication exponent. -/
noncomputable abbrev omega : ℝ := matrixMultiplicationExponent K

end AlgebraicComplexity
