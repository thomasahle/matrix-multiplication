/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.MatrixMultiplication.Volume

/-!
# Finite direct sums of matrix-multiplication tensors

This lightweight module contains only the finite direct-sum target and its numerical volume
functions.  It is intentionally independent of the exponent and Schönhage's asymptotic theorem;
value certificates and finite extraction clients can therefore import it without loading the
analytic compression machinery.  The theorem-heavy asymptotic interface lives in
`MatrixMultiplication/AsymptoticSum.lean`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped DirectSum

universe u v w

variable (K : Type u) [CommSemiring K]
variable {ι : Type w} [Fintype ι]

/-- Leg spaces of a finite direct sum of varying matrix-multiplication tensors. -/
abbrev MMDirectSumSpace (m n p : ι → ℕ) : Leg → Type (max u w) :=
  IndexedDirectSumSpace K (fun i ↦ MMSpace K (m i) (n i) (p i))

/-- A finite direct sum of rectangular matrix-multiplication tensors. -/
noncomputable def matrixMultiplicationDirectSum (m n p : ι → ℕ) :
    Tensor3 K (MMDirectSumSpace K m n p) :=
  indexedDirectSum (fun i ↦ matrixMultiplication (K := K) (m i) (n i) (p i))

end AlgebraicComplexity
