/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.BasicDefs
import AlgebraicComplexity.Tensor.CoordinatesDefs
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Matrix-multiplication tensor: lightweight core

This module contains only the coordinate types, defining pure terms, the tensor itself, and its
elementary one-dimensional summation formulas.  Rank, symmetry, restriction, and product calculi
live in higher modules.  Keeping these definition-level facts at this small boundary lets
constituent-assembly clients avoid loading the full matrix-multiplication theorem environment.
-/

namespace AlgebraicComplexity

open Tensor

universe u

/-- Coordinate indices on the three legs of an `m` by `n` by `p` matrix product. -/
abbrev MMIndex (m n p : ℕ) : Leg → Type
  | .X => Fin m × Fin n
  | .Y => Fin n × Fin p
  | .Z => Fin p × Fin m

instance (m n p : ℕ) (c : Leg) : Fintype (MMIndex m n p c) := by
  cases c <;> infer_instance

instance (m n p : ℕ) (c : Leg) : DecidableEq (MMIndex m n p c) := by
  cases c <;> infer_instance

/-- The three coordinate vector spaces of a matrix-multiplication tensor. -/
abbrev MMSpace (K : Type u) (m n p : ℕ) : Leg → Type u :=
  CoordinateSpace K (MMIndex m n p)

/-- A triple of summation indices for `⟨m,n,p⟩`. -/
abbrev MMTriple (m n p : ℕ) := Fin m × Fin n × Fin p

variable {K : Type u} [CommSemiring K]

/-- The pure summand indexed by `(i,j,k)` in a matrix-multiplication tensor. -/
def mmTerm (m n p : ℕ) (i : Fin m) (j : Fin n) (k : Fin p) :
    ∀ c, MMSpace K m n p c
  | .X => Pi.single (i, j) 1
  | .Y => Pi.single (j, k) 1
  | .Z => Pi.single (k, i) 1

/-- The pure summand selected by a bundled triple of indices. -/
abbrev mmTermOfTriple (m n p : ℕ) (a : MMTriple m n p) :
    ∀ c, MMSpace K m n p c :=
  mmTerm (K := K) m n p a.1 a.2.1 a.2.2

/-- The matrix-multiplication tensor `⟨m,n,p⟩`. -/
noncomputable def matrixMultiplication (m n p : ℕ) : Tensor3 K (MMSpace K m n p) :=
  ∑ a : MMTriple m n p,
    pure (K := K) (mmTermOfTriple (K := K) m n p a)

/-- When the first two dimensions are one, the defining triple sum is just the remaining
coordinate sum. -/
theorem matrixMultiplication_one_one (p : ℕ) :
    matrixMultiplication (K := K) 1 1 p =
      ∑ k : Fin p, pure (K := K) (mmTerm (K := K) 1 1 p 0 0 k) := by
  unfold matrixMultiplication
  simp [Fintype.sum_prod_type]

/-- When the middle dimension is one, the defining triple sum is a double sum over the outer
dimensions. -/
theorem matrixMultiplication_middle_one (m p : ℕ) :
    matrixMultiplication (K := K) m 1 p =
      ∑ i : Fin m, ∑ k : Fin p,
        pure (K := K) (mmTerm (K := K) m 1 p i 0 k) := by
  unfold matrixMultiplication
  simp [Fintype.sum_prod_type]

/-- When the two outer dimensions are one, the defining triple sum is just the middle
coordinate sum. -/
theorem matrixMultiplication_outer_one (n : ℕ) :
    matrixMultiplication (K := K) 1 n 1 =
      ∑ j : Fin n, pure (K := K) (mmTerm (K := K) 1 n 1 0 j 0) := by
  unfold matrixMultiplication
  simp [Fintype.sum_prod_type]

end AlgebraicComplexity
