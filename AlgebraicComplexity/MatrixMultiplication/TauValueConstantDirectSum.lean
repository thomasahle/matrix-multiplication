/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicValueTensor
import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum

set_option autoImplicit false

/-!
# A constant indexed direct sum of matrix multiplications is a `tau`-weight

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `HasTauWeight`
(`MatrixMultiplication/TauValueDirectSum.lean:204`) asks for a polynomial degeneration onto a
`Fin`-indexed family; an extraction theorem instead produces a degeneration onto a *constant*
family indexed by its own structured survivor type.  This module is the adapter, and it is exactly
the `HasTauWeight` analogue of the committed
`CyclicDegenerationCertificate.of_constantIndexedDirectSum`
(`MatrixMultiplication/CyclicValueTensor.lean:173`): reindex the constant sum along
`Fintype.equivFin`, promote that exact reindexing to a degree-zero degeneration, and compose.

The `Nonempty` hypothesis the certificate version needs is absent here, because `HasTauWeight`
deliberately admits the empty family.

Primary source: none directly; this is the numerical bookkeeping of the value calculus, whose
shape is Coppersmith--Winograd's "count the surviving triples, each of the same volume"
(Coppersmith and Winograd, *Matrix multiplication via arithmetic progressions*, J. Symbolic
Computation 9 (1990), pp. 270--272), as used by `[duan2023faster]`
`second_power_appendix.tex:26-45`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A polynomial degeneration onto a constant indexed direct sum of equal matrix
multiplications is a `tau`-weight**, at any value bounded by the corresponding volume power sum.

Proof sketch: take the copy count to be `Fintype.card I` and the three size families constant;
`Tensor.Restricts.indexedDirectSum_const_equiv` reindexes the survivor-indexed sum onto
`Fin (Fintype.card I)`, and an exact restriction is a degree-zero polynomial degeneration. -/
theorem HasTauWeight.ofConstantIndexedDirectSum
    {I : Type w} [Fintype I]
    (τ : ℝ) (X : Tensor3 K V) (m n p : ℕ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (hdeg : PolynomialDegenerates X
      (Tensor.indexedDirectSum (fun _ : I ↦ matrixMultiplication (K := K) m n p)))
    {value : ℝ}
    (hvalue : value ≤ matrixMultiplicationVolumePowerSum
      (fun _ : Fin (Fintype.card I) ↦ m) (fun _ : Fin (Fintype.card I) ↦ n)
      (fun _ : Fin (Fintype.card I) ↦ p) τ) :
    HasTauWeight K X τ value := by
  classical
  refine ⟨Fintype.card I, (fun _ ↦ m), (fun _ ↦ n), (fun _ ↦ p),
    (fun _ ↦ hm), (fun _ ↦ hn), (fun _ ↦ hp), ?_, hvalue⟩
  refine hdeg.trans (PolynomialDegenerates.of_restricts ?_)
  simpa only [matrixMultiplicationDirectSum] using
    Tensor.Restricts.indexedDirectSum_const_equiv (K := K) (Fintype.equivFin I)
      (matrixMultiplication (K := K) m n p)

end AlgebraicComplexity
