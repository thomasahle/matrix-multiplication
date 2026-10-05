/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.Tensor.Coordinates
import AlgebraicComplexity.Tensor.Product

/-!
# External products of matrix-multiplication tensors

This lightweight module exposes the binary product law without importing multinomial type
extraction.  Semantic assembly code can therefore multiply rectangular leaves without loading
the considerably broader type-counting environment.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [CommSemiring K]

/-- Pair corresponding row and column indices and encode each pair as one finite index. -/
def finPairProductEquiv (a b a' b' : ℕ) :
    (Fin a × Fin b) × (Fin a' × Fin b') ≃ Fin (a * a') × Fin (b * b') :=
  (Equiv.prodProdProdComm _ _ _ _).trans
    (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)

@[simp] theorem finPairProductEquiv_apply
    {a b a' b' : ℕ} (i : Fin a) (j : Fin b) (i' : Fin a') (j' : Fin b') :
    finPairProductEquiv a b a' b' ((i, j), (i', j')) =
      (finProdFinEquiv (i, i'), finProdFinEquiv (j, j')) := rfl

/-- Pair and encode the three coordinates of two finite index triples. -/
def finTripleProductEquiv (a b c a' b' c' : ℕ) :
    (Fin a × Fin b × Fin c) × (Fin a' × Fin b' × Fin c') ≃
      Fin (a * a') × Fin (b * b') × Fin (c * c') :=
  (Equiv.prodProdProdComm _ _ _ _).trans
    (Equiv.prodCongr finProdFinEquiv
      ((Equiv.prodProdProdComm _ _ _ _).trans
        (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)))

@[simp] theorem finTripleProductEquiv_apply
    {a b c a' b' c' : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin c)
    (i' : Fin a') (j' : Fin b') (k' : Fin c') :
    finTripleProductEquiv a b c a' b' c' ((i, j, k), (i', j', k')) =
      (finProdFinEquiv (i, i'), finProdFinEquiv (j, j'),
        finProdFinEquiv (k, k')) := rfl

/-- The coordinate-index equivalence on each leg of an external product of matrix tensors. -/
def mmIndexProductEquiv (m n p m' n' p' : ℕ) :
    ∀ c, MMIndex m n p c × MMIndex m' n' p' c ≃
      MMIndex (m * m') (n * n') (p * p') c
  | .X => finPairProductEquiv m n m' n'
  | .Y => finPairProductEquiv n p n' p'
  | .Z => finPairProductEquiv p m p' m'

/-- The coordinate-space equivalence on each leg of a product of matrix tensors. -/
noncomputable def mmProductLegEquiv (m n p m' n' p' : ℕ) (c : Leg) :
    TensorProduct K (MMSpace K m n p c) (MMSpace K m' n' p' c) ≃ₗ[K]
      MMSpace K (m * m') (n * n') (p * p') c :=
  (coordinateTensorEquiv (K := K)).trans
    (LinearEquiv.funCongrLeft K K (mmIndexProductEquiv m n p m' n' p' c).symm)

/-- The legwise equivalence relating an external product to the larger matrix tensor's space. -/
noncomputable def mmExternalEquiv (m n p m' n' p' : ℕ) :
    Tensor3 K (fun c ↦ TensorProduct K (MMSpace K m n p c) (MMSpace K m' n' p' c)) ≃ₗ[K]
      Tensor3 K (MMSpace K (m * m') (n * n') (p * p')) :=
  PiTensorProduct.congr (mmProductLegEquiv (K := K) m n p m' n' p')

@[simp] theorem mmProductLegEquiv_mmTerm
    (m n p m' n' p' : ℕ)
    (i : Fin m) (j : Fin n) (k : Fin p)
    (i' : Fin m') (j' : Fin n') (k' : Fin p') (c : Leg) :
    mmProductLegEquiv (K := K) m n p m' n' p' c
        (mmTerm (K := K) m n p i j k c ⊗ₜ[K]
          mmTerm (K := K) m' n' p' i' j' k' c) =
      mmTerm (K := K) (m * m') (n * n') (p * p')
        (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j'))
        (finProdFinEquiv (k, k')) c := by
  cases c <;>
    simp only [mmProductLegEquiv, LinearEquiv.trans_apply, mmTerm,
      coordinateTensorEquiv_single_tmul_single, funCongrLeft_symm_single,
      mmIndexProductEquiv, finPairProductEquiv_apply]

/-- On defining pure terms, the external-product equivalence pairs all three indices. -/
@[simp] theorem mmExternalEquiv_external_mmTerm
    (m n p m' n' p' : ℕ)
    (i : Fin m) (j : Fin n) (k : Fin p)
    (i' : Fin m') (j' : Fin n') (k' : Fin p') :
    mmExternalEquiv (K := K) m n p m' n' p'
        (external
          (pure (K := K) (mmTerm (K := K) m n p i j k))
          (pure (K := K) (mmTerm (K := K) m' n' p' i' j' k'))) =
      pure (K := K)
        (mmTerm (K := K) (m * m') (n * n') (p * p')
          (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j'))
          (finProdFinEquiv (k, k'))) := by
  simp only [external_pure, mmExternalEquiv, PiTensorProduct.congr_tprod]
  congr 1
  funext c
  exact mmProductLegEquiv_mmTerm m n p m' n' p' i j k i' j' k' c

/-- Bundled-index form of `mmExternalEquiv_external_mmTerm`. -/
@[simp] theorem mmExternalEquiv_external_mmTermOfTriple
    (m n p m' n' p' : ℕ)
    (a : MMTriple m n p) (b : MMTriple m' n' p') :
    mmExternalEquiv (K := K) m n p m' n' p'
        (external
          (pure (K := K) (mmTermOfTriple (K := K) m n p a))
          (pure (K := K) (mmTermOfTriple (K := K) m' n' p' b))) =
      pure (K := K)
        (mmTermOfTriple (K := K) (m * m') (n * n') (p * p')
          (finTripleProductEquiv m n p m' n' p' (a, b))) := by
  rcases a with ⟨i, j, k⟩
  rcases b with ⟨i', j', k'⟩
  exact mmExternalEquiv_external_mmTerm m n p m' n' p' i j k i' j' k'

/-- Matrix-multiplication tensors multiply under the factorwise external product. -/
theorem mmExternalEquiv_matrixMultiplication (m n p m' n' p' : ℕ) :
    mmExternalEquiv (K := K) m n p m' n' p'
        (external (matrixMultiplication (K := K) m n p)
          (matrixMultiplication (K := K) m' n' p')) =
      matrixMultiplication (K := K) (m * m') (n * n') (p * p') := by
  unfold matrixMultiplication
  rw [external_sum_sum]
  simp_rw [map_sum, mmExternalEquiv_external_mmTermOfTriple]
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp (finTripleProductEquiv m n p m' n' p')
    (fun a : MMTriple (m * m') (n * n') (p * p') ↦
      pure (K := K)
        (mmTermOfTriple (K := K) (m * m') (n * n') (p * p') a))

namespace Tensor.Isomorphic

/-- The external product of two rectangular matrix-multiplication tensors is the rectangular
tensor obtained by multiplying the three dimensions. -/
theorem matrixMultiplication_externalProduct (m n p m' n' p' : ℕ) :
    Isomorphic
      (Tensor.external
        (matrixMultiplication (K := K) m n p)
        (matrixMultiplication (K := K) m' n' p'))
      (matrixMultiplication (K := K) (m * m') (n * n') (p * p')) := by
  refine ⟨mmProductLegEquiv (K := K) m n p m' n' p', ?_⟩
  simpa [mmExternalEquiv, PiTensorProduct.congr] using
    mmExternalEquiv_matrixMultiplication (K := K) m n p m' n' p'

end Tensor.Isomorphic

end AlgebraicComplexity
