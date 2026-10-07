/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.NonminimalRankSpeedup
import AlgebraicComplexity.Tensor.OneSliceBorderSpeedup
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis

/-!
# One-slice speedup for a nonminimal border-rank decomposition

This file proves [AlmanLi2026, Theorem 6.1, p. 19] in its original *border-rank* form: if a tensor
`T` whose `X` and `Y` legs have dimension `n` has border rank at most `r`, then

```text
⟨r⟩ ⊕ ⟨1,n,1⟩  ⊵  T ⊕ ⟨1, r − n, 1⟩.
```

`MatrixMultiplication/NonminimalRankSpeedup.lean` proves the same statement from an exact rank
decomposition and records why the paper's route to the border-rank form — Propositions 5.3 and
5.4 over the function field `F(λ)` — was not available.  The route taken here avoids that layer
altogether: `Tensor/OneSliceBorderSpeedup.lean` applies the polynomial free-lunch theorem to two
explicit polynomial families of leg maps, and the only field of fractions in the argument is
hidden inside the kernel-frame lemma of `Tensor/PolynomialKernelFrame.lean`.

The statement proved is slightly more general than the paper's: the two leg dimensions may
differ, `⟨r⟩ ⊕ ⟨1,nY,1⟩ ⊵ T ⊕ ⟨1, r − nX, 1⟩`, and nothing is assumed about the `Z` leg.

## Main results

* `oneSliceFrameTensor_eq_directSum_diagonalTensor`: `⟨r⟩ ⊕ ⟨1,n,1⟩` on its coordinate spaces is
  a framed source in the sense of `Tensor.oneSliceFrameTensor`.
* `polynomialDegenerates_diagonalTensor_oneSlice_of_borderRankLE`: **Theorem 6.1**, border-rank
  form.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Theorem 6.1, p. 19.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u w

variable {K : Type u} [Field K]

/-- The `X`-leg basis of `⟨r⟩ ⊕ ⟨1,n,1⟩`: the standard basis of the diagonal part followed by the
standard basis of the slice. -/
noncomputable def diagonalOneSliceBasisX (K : Type u) [Field K] (r n : ℕ) :
    Basis (Fin r ⊕ Fin 1 × Fin n) K ((Fin r → K) × MMSpace K 1 n 1 .X) :=
  (Pi.basisFun K (Fin r)).prod (Pi.basisFun K (Fin 1 × Fin n))

/-- The `Y`-leg basis of `⟨r⟩ ⊕ ⟨1,n,1⟩`, with the slice coordinates `(j, 0)` reindexed as
`(0, j)`. -/
noncomputable def diagonalOneSliceBasisY (K : Type u) [Field K] (r n : ℕ) :
    Basis (Fin r ⊕ Fin 1 × Fin n) K ((Fin r → K) × MMSpace K 1 n 1 .Y) :=
  (Pi.basisFun K (Fin r)).prod
    ((Pi.basisFun K (Fin n × Fin 1)).reindex (Equiv.prodComm (Fin n) (Fin 1)))

/-- The `Z`-leg basis of `⟨r⟩ ⊕ ⟨1,n,1⟩`: the standard basis of the diagonal part followed by the
single slice vector. -/
noncomputable def diagonalOneSliceBasisZ (K : Type u) [Field K] (r n : ℕ) :
    Basis (Fin r ⊕ Fin 1) K ((Fin r → K) × MMSpace K 1 n 1 .Z) :=
  (Pi.basisFun K (Fin r)).prod
    ((Pi.basisFun K (Fin 1 × Fin 1)).reindex (Equiv.prodUnique (Fin 1) (Fin 1)))

/-- `⟨r⟩ ⊕ ⟨1,n,1⟩` on its coordinate spaces is the framed source of the border-rank one-slice
speedup, with one group of slices. -/
theorem oneSliceFrameTensor_eq_directSum_diagonalTensor (r n : ℕ) :
    oneSliceFrameTensor (S := fun c ↦ (Fin r → K) × MMSpace K 1 n 1 c)
        (diagonalOneSliceBasisX K r n) (diagonalOneSliceBasisY K r n)
        (diagonalOneSliceBasisZ K r n) =
      Tensor.directSum (diagonalTensor K (Fin r)) (matrixMultiplication (K := K) 1 n 1) := by
  classical
  rw [Tensor.directSum, diagonalTensor, matrixMultiplication_outer_one, map_sum, map_sum,
    oneSliceFrameTensor, Fin.sum_univ_one]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Tensor.map_pure]
    congr 1
    funext c
    cases c <;>
      simp [diagonalOneSliceBasisX, diagonalOneSliceBasisY, diagonalOneSliceBasisZ]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Tensor.map_pure]
    congr 1
    funext c
    cases c <;>
      simp [diagonalOneSliceBasisX, diagonalOneSliceBasisY, diagonalOneSliceBasisZ, mmTerm]

variable {W : Leg → Type w} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]

/-- **One-slice speedup for a nonminimal border-rank decomposition**
([AlmanLi2026], Theorem 6.1, p. 19, the displayed `s = n` clause, border-rank form).

If `T` has border rank at most `r` and its `X` and `Y` legs have dimensions `nX` and `nY`, then

```text
⟨r⟩ ⊕ ⟨1,nY,1⟩  ⊵  T ⊕ ⟨1, r − nX, 1⟩.
```

With `nX = nY = n` this is the paper's statement.  Natural-number subtraction truncates the
conclusion correctly when `r < nX`. -/
theorem polynomialDegenerates_diagonalTensor_oneSlice_of_borderRankLE
    [FiniteDimensional K (W .X)] [FiniteDimensional K (W .Y)]
    (nX nY r : ℕ) (T : Tensor3 K W)
    (hX : finrank K (W .X) = nX) (hY : finrank K (W .Y) = nY) (hT : BorderRankLE r T) :
    PolynomialDegenerates
      (Tensor.directSum (diagonalTensor K (Fin r)) (matrixMultiplication (K := K) 1 nY 1))
      (Tensor.directSum T (matrixMultiplication (K := K) 1 (r - nX) 1)) := by
  classical
  obtain ⟨d, x, hx⟩ := hT.exists_fin_family
  have hg : ∀ a : Fin 1, r - nX ≤
      (Finset.univ.filter fun i : Fin r ↦
        (fun _ : Fin r ↦ (some 0 : Option (Fin 1))) i = some a).card - nX := by
    intro a
    simp [Subsingleton.elim a 0]
  have htgt : matrixMultiplication (K := K) 1 (r - nX) 1 =
      ∑ _a : Fin 1, ∑ k : Fin (r - nX), Tensor.pure (K := K)
        (ofLegs (V := MMSpace K 1 (r - nX) 1)
          (Pi.single ((0 : Fin 1), k) 1) (Pi.single (k, (0 : Fin 1)) 1)
          (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1)) := by
    rw [matrixMultiplication_outer_one, Fin.sum_univ_one]
    refine Finset.sum_congr rfl fun k _ ↦ congrArg _ ?_
    funext c
    cases c <;> rfl
  have key := polynomialDegenerates_oneSliceFrameTensor_directSum
    (S := fun c ↦ (Fin r → K) × MMSpace K 1 nY 1 c) (W' := MMSpace K 1 (r - nX) 1)
    (diagonalOneSliceBasisX K r nY) (diagonalOneSliceBasisY K r nY)
    (diagonalOneSliceBasisZ K r nY)
    (finBasisOfFinrankEq K (W .X) hX) (finBasisOfFinrankEq K (W .Y) hY) x hx
    (fun _ ↦ some 0) hg
    (fun _ k ↦ Pi.single ((0 : Fin 1), k) 1) (fun _ k ↦ Pi.single (k, (0 : Fin 1)) 1)
    (fun _ ↦ Pi.single ((0 : Fin 1), (0 : Fin 1)) 1)
  rw [oneSliceFrameTensor_eq_directSum_diagonalTensor] at key
  rw [htgt]
  exact key

end AlgebraicComplexity
