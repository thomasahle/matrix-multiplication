/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Compression

/-!
# Tiny regression for multiple compression

Two independent copies in each of three cyclic orientations produce eight square scalar products.
The elementary rank-eight algorithm for `2 × 2` multiplication compresses them to one `2 × 2`
product.  This deliberately distinguishes full cross-term symmetrization from diagonal extraction,
which would retain only two products.

The single regression theorem is `compression_two_two_two_restricts`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable {K : Type u} [CommSemiring K]

/-- The smallest nontrivial instance of Schönhage's finite multiple-compression step: the
external product of three cyclic copies of the two-fold direct sum of `⟨1,1,1⟩` is a
restriction of `⟨2,2,2⟩`.

Read in the `Restricts` direction, the source is `⟨2,2,2⟩` and the result is the eight-term
product; the elementary rank-eight `2 × 2` algorithm is what supplies the legwise maps.

Proof sketch: the defining decomposition gives `RankLE 8 ⟨2,2,2⟩`, and `8 = |Fin 2|³`, so
`Tensor.RankLE.matrixMultiplication_multipleCompression` applies verbatim at `m = n = p = 1`. -/
theorem compression_two_two_two_restricts :
    Restricts
      (Tensor.external
        (Tensor.external
          (Tensor.indexedDirectSum
            (fun _ : Fin 2 ↦ matrixMultiplication (K := K) 1 1 1))
          (Tensor.indexedDirectSum
            (fun _ : Fin 2 ↦ matrixMultiplication (K := K) 1 1 1)))
        (Tensor.indexedDirectSum
          (fun _ : Fin 2 ↦ matrixMultiplication (K := K) 1 1 1)))
      (matrixMultiplication (K := K) 2 2 2) := by
  have h : RankLE ((Fintype.card (Fin 2)) ^ 3)
      (matrixMultiplication (K := K) 2 2 2) := by
    simpa using matrixMultiplication_rankLE (K := K) 2 2 2
  simpa using h.matrixMultiplication_multipleCompression (m := 1) (n := 1) (p := 1)

end AlgebraicComplexity.Examples
