/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.MatrixMultiplication.CTensor

/-!
# C-tensor extraction to matrix-multiplication tensors

This adapter specializes the target-agnostic finite C-tensor degeneration to rectangular
matrix-multiplication tensors.  Keeping it outside `CTensor.lean` preserves the reusable
C-tensor core's independence from named algebraic-complexity tensors.

The main theorem is the finite leaf API used by Coppersmith--Winograd and follow-up laser-method
clients: they need only prove that every selected antidiagonal constituent restricts to the same
`⟨m,n,p⟩`; the generic C-tensor machinery supplies the simultaneous polynomial degeneration.
-/

namespace AlgebraicComplexity.CTensor

open Tensor

universe u v

/-- A uniform matrix-multiplication restriction for every selected antidiagonal constituent
yields that many independent copies of `⟨m,n,p⟩`, with the explicit C-tensor leading degree.

Proof sketch: instantiate `cyclicTensor_degeneratesAt_constantIndexedDirectSum` with the
matrix-multiplication tensor. -/
theorem cyclicTensor_degeneratesAt_matrixMultiplicationDirectSum
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (m n p : ℕ)
    (hmm : ∀ s : (antidiagonal T).support,
      Restricts ((antidiagonal T).constituent s.1)
        (matrixMultiplication (K := K) m n p)) :
    PolynomialDegeneratesAt (antidiagonalDegree h) (cyclicTensor T)
      (Tensor.indexedDirectSum
        (fun _ : (antidiagonal T).support ↦ matrixMultiplication (K := K) m n p)) :=
  cyclicTensor_degeneratesAt_constantIndexedDirectSum T
    (matrixMultiplication (K := K) m n p) hmm

end AlgebraicComplexity.CTensor
