/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.Tensor.Concise

/-!
# Conciseness of matrix-multiplication tensors

This leaf module proves the flattening lower bound needed by the exponent and asymptotic-sum
theory.  It is separate from the basic matrix-multiplication tensor so definitions, product laws,
and upper-bound clients do not inherit finite-dimensional conciseness dependencies.

It is also the canonical home of the two coordinate contractions of `⟨m,n,p⟩` that the
substitution-method clients need:

* `contractX_matrixMultiplication_basis`: contracting `Y` at `(j,k)` and `Z` at `(k,i)` returns
  the `X`-basis vector at `(i,j)` — the *detection* certificate of a substitution step;
* `contractY_matrixMultiplication_row`: contracting against any `X`-covector that acts as the
  coordinate covector on one row, and the matching `Z`-coordinate covector, returns a `Y`-basis
  vector — the *survival* certificate after a substitution chain in the other rows.

Both were previously duplicated verbatim, file-privately, in `Examples/SmallMatrixLowerBounds`
and `Examples/BlaeserLowerBound`; those copies are gone.  `contractZ_matrixMultiplication_basis`
stays private because nothing outside this file consumes it.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [Field K]

/-- Contracting `Y` at `(j,k)` and `Z` at `(k,i)` isolates the standard `X`-basis vector
indexed by `(i,j)`.  This is the detection certificate consumed by the substitution-method
clients as well as by the conciseness proofs below. -/
theorem contractX_matrixMultiplication_basis
    {m n p : ℕ} (i : Fin m) (j : Fin n) (k : Fin p) :
    contractX
        (LinearMap.proj (R := K) (j, k))
        (LinearMap.proj (R := K) (k, i))
        (matrixMultiplication (K := K) m n p) =
      Pi.single (i, j) 1 := by
  classical
  unfold matrixMultiplication
  rw [map_sum]
  ext a
  rw [Finset.sum_eq_single (i, j, k)]
  · simp [mmTermOfTriple, mmTerm, Pi.single_apply]
  · rintro ⟨i', j', k'⟩ _ hne
    by_cases hi : i' = i <;> by_cases hj : j' = j <;>
      by_cases hk : k' = k <;>
        simp_all [mmTermOfTriple, mmTerm]
  · simp

/-- **Row form of the `Y` flattening.**  Contracting `⟨m,n,p⟩` against an `X`-covector `fx`
that acts as the coordinate covector at `(i₁,b)` on the basis vectors of the single row `i₁`,
and against the `Z`-covector at `(c,i₁)`, isolates the `Y`-basis vector at `(b,c)`.

The hypothesis constrains `fx` on the protected row only, which is exactly what survives an
arbitrary substitution chain in the other rows; the substitution-method clients consume this
form, and `contractY_matrixMultiplication_basis` is its coordinate-covector special case.

Proof sketch: the `Z`-covector forces the summation triple to have row `i₁` and `Z`-column `c`,
so only the values of `fx` on row `i₁` matter and the surviving term is the defining term at
`(i₁,b,c)`. -/
theorem contractY_matrixMultiplication_row
    {m n p : ℕ} {i₁ : Fin m} {b : Fin n} (c : Fin p)
    {fx : MMSpace K m n p .X →ₗ[K] K}
    (hfx : ∀ j : Fin n, fx (Pi.single (i₁, j) 1) = if j = b then 1 else 0) :
    contractY fx (LinearMap.proj (R := K) (c, i₁))
        (matrixMultiplication (K := K) m n p) =
      Pi.single (b, c) 1 := by
  classical
  unfold matrixMultiplication
  rw [map_sum]
  ext a
  rw [Finset.sum_eq_single (i₁, b, c)]
  · simp [mmTermOfTriple, mmTerm, Pi.single_apply, hfx]
  · rintro ⟨i, j, k⟩ - hne2
    by_cases hi : i = i₁
    · subst hi
      by_cases hj : j = b
      · subst hj
        have hk : k ≠ c := fun hk ↦ hne2 (by rw [hk])
        simp [mmTermOfTriple, mmTerm, Ne.symm hk]
      · simp [mmTermOfTriple, mmTerm, hfx, hj]
    · simp [mmTermOfTriple, mmTerm, Ne.symm hi]
  · simp

/-- Contracting `X` at `(i,j)` and `Z` at `(k,i)` isolates the standard `Y`-basis vector
indexed by `(j,k)`.  The coordinate-covector case of `contractY_matrixMultiplication_row`. -/
theorem contractY_matrixMultiplication_basis
    {m n p : ℕ} (i : Fin m) (j : Fin n) (k : Fin p) :
    contractY
        (LinearMap.proj (R := K) (i, j))
        (LinearMap.proj (R := K) (k, i))
        (matrixMultiplication (K := K) m n p) =
      Pi.single (j, k) 1 :=
  contractY_matrixMultiplication_row k (fun j' ↦ by
    simp [Pi.single_apply, eq_comm])

/-- Contracting `X` at `(i,j)` and `Y` at `(j,k)` isolates the standard `Z`-basis vector
indexed by `(k,i)`. -/
private theorem contractZ_matrixMultiplication_basis
    {m n p : ℕ} (i : Fin m) (j : Fin n) (k : Fin p) :
    contractZ
        (LinearMap.proj (R := K) (i, j))
        (LinearMap.proj (R := K) (j, k))
        (matrixMultiplication (K := K) m n p) =
      Pi.single (k, i) 1 := by
  classical
  unfold matrixMultiplication
  rw [map_sum]
  ext a
  rw [Finset.sum_eq_single (i, j, k)]
  · simp [mmTermOfTriple, mmTerm, Pi.single_apply]
  · rintro ⟨i', j', k'⟩ _ hne
    by_cases hi : i' = i <;> by_cases hj : j' = j <;>
      by_cases hk : k' = k <;>
        simp_all [mmTermOfTriple, mmTerm]
  · simp

/-- A matrix-multiplication tensor with a nonempty contracted dimension is concise in `X`. -/
theorem matrixMultiplication_isConciseX
    {m n p : ℕ} (hp : 0 < p) :
    IsConciseX (matrixMultiplication (K := K) m n p) := by
  let k : Fin p := ⟨0, hp⟩
  apply le_antisymm le_top
  rw [← (Pi.basisFun K (Fin m × Fin n)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [Pi.basisFun_apply]
  exact ⟨(LinearMap.proj (R := K) (j, k),
      LinearMap.proj (R := K) (k, i)),
    contractX_matrixMultiplication_basis i j k⟩

/-- A matrix-multiplication tensor with a nonempty first dimension is concise in `Y`. -/
theorem matrixMultiplication_isConciseY
    {m n p : ℕ} (hm : 0 < m) :
    IsConciseY (matrixMultiplication (K := K) m n p) := by
  let i : Fin m := ⟨0, hm⟩
  apply le_antisymm le_top
  rw [← (Pi.basisFun K (Fin n × Fin p)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨⟨j, k⟩, rfl⟩
  rw [Pi.basisFun_apply]
  exact ⟨(LinearMap.proj (R := K) (i, j),
      LinearMap.proj (R := K) (k, i)),
    contractY_matrixMultiplication_basis i j k⟩

/-- A matrix-multiplication tensor with a nonempty second dimension is concise in `Z`. -/
theorem matrixMultiplication_isConciseZ
    {m n p : ℕ} (hn : 0 < n) :
    IsConciseZ (matrixMultiplication (K := K) m n p) := by
  let j : Fin n := ⟨0, hn⟩
  apply le_antisymm le_top
  rw [← (Pi.basisFun K (Fin p × Fin m)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨⟨k, i⟩, rfl⟩
  rw [Pi.basisFun_apply]
  exact ⟨(LinearMap.proj (R := K) (i, j),
      LinearMap.proj (R := K) (j, k)),
    contractZ_matrixMultiplication_basis i j k⟩

/-- A positive rectangular matrix-multiplication tensor is concise on all three legs. -/
theorem matrixMultiplication_isConcise
    {m n p : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) :
    IsConcise (matrixMultiplication (K := K) m n p) :=
  ⟨matrixMultiplication_isConciseX hp,
    matrixMultiplication_isConciseY hm, matrixMultiplication_isConciseZ hn⟩

/-- Flattening on the `X` leg gives the elementary lower bound
`rank ⟨m,n,p⟩ ≥ m*n` whenever `p` is positive. -/
theorem matrixMultiplication_rank_lower_X
    {m n p r : ℕ} (hp : 0 < p)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    m * n ≤ r := by
  have hdim := h.finrank_X_le (matrixMultiplication_isConciseX (K := K) hp)
  simpa [MMSpace, MMIndex, Module.finrank_fintype_fun_eq_card] using hdim

/-- Flattening on the `Y` leg gives the elementary lower bound
`rank ⟨m,n,p⟩ ≥ n*p` whenever `m` is positive. -/
theorem matrixMultiplication_rank_lower_Y
    {m n p r : ℕ} (hm : 0 < m)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    n * p ≤ r := by
  have hdim := h.finrank_Y_le (matrixMultiplication_isConciseY (K := K) hm)
  simpa [MMSpace, MMIndex, Module.finrank_fintype_fun_eq_card] using hdim

/-- Flattening on the `Z` leg gives the elementary lower bound
`rank ⟨m,n,p⟩ ≥ p*m` whenever `n` is positive. -/
theorem matrixMultiplication_rank_lower_Z
    {m n p r : ℕ} (hn : 0 < n)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    p * m ≤ r := by
  have hdim := h.finrank_Z_le (matrixMultiplication_isConciseZ (K := K) hn)
  simpa [MMSpace, MMIndex, Module.finrank_fintype_fun_eq_card] using hdim

/-- Every rank certificate for positive rectangular matrix multiplication has length at least the
largest leg dimension. -/
theorem matrixMultiplication_rank_lower_max
    {m n p r : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    max (m * n) (max (n * p) (p * m)) ≤ r := by
  have hdim := h.max_finrank_le
    (matrixMultiplication_isConcise (K := K) hm hn hp)
  simpa [MMSpace, MMIndex, Module.finrank_fintype_fun_eq_card] using hdim

end AlgebraicComplexity
