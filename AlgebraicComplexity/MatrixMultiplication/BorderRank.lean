/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.Tensor.BorderRank

/-!
# Border-rank laws for matrix-multiplication tensors

This module keeps the basic matrix-multiplication tensor definition independent of polynomial
degeneration, then adds the constructive border-rank consequences of its cyclic symmetry and of
its external-product law.  These are the border-rank counterparts of the exact-rank laws in
`AlgebraicComplexity/MatrixMultiplication.lean`.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [CommSemiring K]

namespace Tensor.BorderRankLE

/-- Cyclically rotating the three roles of a matrix-multiplication tensor preserves every
constructive border-rank upper bound: a size-`r` certificate for `⟨m,n,p⟩` gives one for
`⟨p,m,n⟩`.

Proof sketch: rotate the certificate along the cyclic leg permutation, then retype the permuted
legs as the rotated matrix spaces.  That composite is the canonical isomorphism `mmCycleEquiv`,
which sends `⟨m,n,p⟩` to `⟨p,m,n⟩`. -/
theorem matrixMultiplication_cycle
    {m n p r : ℕ}
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    BorderRankLE r (matrixMultiplication (K := K) p m n) := by
  have h' := h.permute_cycle.map
    (fun c ↦ (mmCycleLegEquiv (K := K) m n p c).toLinearMap)
  have heq :
      Tensor.map (fun c ↦ (mmCycleLegEquiv (K := K) m n p c).toLinearMap)
          (Tensor.permute cycle (matrixMultiplication (K := K) m n p)) =
        mmCycleEquiv (K := K) m n p
          (matrixMultiplication (K := K) m n p) := by
    rfl
  rw [heq, mmCycleEquiv_matrixMultiplication] at h'
  exact h'

/-- Border-rank certificates for matrix-multiplication tensors multiply after the canonical
external-product reindexing. -/
theorem matrixMultiplication_mul
    {m n p m' n' p' r s : ℕ}
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p))
    (h' : BorderRankLE s (matrixMultiplication (K := K) m' n' p')) :
    BorderRankLE (r * s)
      (matrixMultiplication (K := K) (m * m') (n * n') (p * p')) := by
  have hproduct := (h.external h').map
    (fun c ↦ (mmProductLegEquiv (K := K) m n p m' n' p' c).toLinearMap)
  rw [← mmExternalEquiv_matrixMultiplication]
  simpa [mmExternalEquiv, PiTensorProduct.congr] using hproduct

/-- Iterating a square border-rank certificate gives the expected power bound. -/
theorem matrixMultiplication_pow {n r : ℕ}
    (h : BorderRankLE r (matrixMultiplication (K := K) n n n)) (k : ℕ) :
    BorderRankLE (r ^ k)
      (matrixMultiplication (K := K) (n ^ k) (n ^ k) (n ^ k)) := by
  induction k with
  | zero =>
      change BorderRankLE 1 (matrixMultiplication (K := K) 1 1 1)
      exact (matrixMultiplication_rankLE (K := K) 1 1 1).toBorderRankLE
  | succ k ih =>
      rw [pow_succ]
      exact ih.matrixMultiplication_mul h

end Tensor.BorderRankLE

end AlgebraicComplexity
