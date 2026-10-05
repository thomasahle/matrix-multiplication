/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceAppend
import AlgebraicComplexity.Tensor.SliceRank

/-!
# One-slice speedup for a nonminimal rank decomposition

This file proves the *restriction* half of [AlmanLi2026, Theorem 6.1, p. 19]: if an
`n × n × n` tensor `T` is a sum of `r` pure tensors, then

```text
⟨r⟩ ⊕ ⟨1,s,1⟩  ⊵  T ⊕ ⟨1, r + s − 2n, 1⟩
```

for every `s` bounding the rank of the contracted matrix `M = ∑ᵢ aᵢbᵢ`, and in particular
(taking `s = n`, which is unconditional)

```text
⟨r⟩ ⊕ ⟨1,n,1⟩  ⊵  T ⊕ ⟨1, r − n, 1⟩.
```

The source `⟨r⟩` is the library's diagonal tensor `Tensor.diagonalTensor K (Fin r)`
(`Tensor/SliceRank.lean`), i.e. `∑_{i<r} e_i ⊗ e_i ⊗ e_i` in coordinates.

## Why the hypothesis is `RankLE`, not `BorderRankLE`

The paper's Theorem 6.1 starts from a *border*-rank decomposition `∑ᵢ aᵢbᵢcᵢ = T + O(λ)` and runs
the whole of Propositions 5.3 and 5.4 over the function field `F(λ)`, descending at the end by
[AlmanLi2026, Corollary 5.1].  Propositions 5.3 and 5.4 are rank statements, so that argument
needs `matrixRank` for `F(λ)`-valued leg maps: a scalar extension of the tensor calculus to
`RatFunc K` together with a descent of the resulting degeneration.  No such layer exists here,
and none is built speculatively; the border-rank form therefore remains the recorded obligation
`AlmanLi.NonminimalBorderRankSpeedup` (`Examples/AlmanLiOneSliceSpeedup.lean`).  Everything below
the field is unchanged, so the `RankLE` version proved here is the exact statement the paper's
argument specializes to when the certificate is exact.

## Why the all-ones contraction loses no generality

The paper contracts the third mode with a functional `c' : eᵢ ↦ c'ᵢ` for arbitrary *nonzero*
scalars `c'ᵢ`.  Rescaling the decomposition by `aᵢ ↦ c'ᵢ aᵢ`, `cᵢ ↦ c'ᵢ⁻¹ cᵢ` turns any such
choice into the all-ones functional `coordinateSum` while preserving both `T` and `M`, so
quantifying over all restrictions `f` from `⟨r⟩` with the fixed all-ones contraction is the same
statement.

## Main results

* `coordinateSum`, `matrixFlatten_diagonalTensor`, `matrixRank_diagonalTensor`: the contracted
  slice of `⟨r⟩` at the all-ones functional is the identity matrix, of rank `r`.
* `restricts_diagonalTensor_of_rankLE`: a rank-`r` tensor is a restriction of `⟨r⟩`.
* `polynomialDegenerates_diagonalTensor_directSum_oneSlice`: **Theorem 6.1**, restriction form.
* `polynomialDegenerates_diagonalTensor_oneSlice_of_rankLE`: its `s = n` specialization, stated
  directly from `RankLE`.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Theorem 6.1, p. 19.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u v w

section CommSemiring

variable {K : Type u} [CommSemiring K]

/-- The all-ones functional `v ↦ ∑ᵢ vᵢ` on a finite coordinate space. -/
def coordinateSum (K : Type u) [CommSemiring K] (ι : Type v) [Fintype ι] :
    (ι → K) →ₗ[K] K :=
  ∑ i : ι, LinearMap.proj i

@[simp] theorem coordinateSum_apply {ι : Type v} [Fintype ι] (v : ι → K) :
    coordinateSum K ι v = ∑ i, v i := by
  simp [coordinateSum]

/-- **The contracted slice of the diagonal tensor `⟨r⟩`** at the all-ones functional is the
identity matrix: the `i`-th coordinate functional goes to the `i`-th basis vector. -/
theorem matrixFlatten_diagonalTensor (ι : Type v) [Fintype ι] [DecidableEq ι]
    (β : Dual K (ι → K)) :
    matrixFlatten (coordinateSum K ι) (diagonalTensor K ι) β =
      ∑ i : ι, β (Pi.single i 1) • (Pi.single i 1 : ι → K) := by
  classical
  rw [diagonalTensor, matrixFlatten_finset_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [matrixFlatten_pure]
  simp

end CommSemiring

section Field

variable {K : Type u} [Field K]

/-- The contracted slice of `⟨r⟩` at the all-ones functional has full rank. -/
theorem matrixRank_diagonalTensor (ι : Type v) [Fintype ι] [DecidableEq ι] :
    matrixRank (coordinateSum K ι) (diagonalTensor K ι) = Fintype.card ι := by
  classical
  have hsurj : LinearMap.range
      (matrixFlatten (coordinateSum K ι) (diagonalTensor K ι)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨∑ i : ι, v i • LinearMap.proj (R := K) (φ := fun _ : ι ↦ K) i, ?_⟩
    rw [matrixFlatten_diagonalTensor]
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [matrixRank, hsurj, finrank_top, Module.finrank_fintype_fun_eq_card]

variable {V : Leg → Type v} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]

/-- **A tensor of rank at most `r` is a restriction of the diagonal tensor `⟨r⟩`.**

This is the standard reading of a rank decomposition as a restriction; the shorter list of a
`RankLE` certificate is padded with zero terms, which contribute nothing. -/
theorem restricts_diagonalTensor_of_rankLE {T : Tensor3 K V} {r : ℕ} (h : RankLE r T) :
    Restricts (diagonalTensor K (Fin r)) T := by
  classical
  obtain ⟨terms, hlen, hT⟩ := h
  set terms' := terms ++ List.replicate (r - terms.length) (0 : ∀ i, V i) with hterms'
  have hlen' : terms'.length = r := by
    rw [hterms', List.length_append, List.length_replicate]
    omega
  have hzero : Tensor.pure (K := K) (0 : ∀ i, V i) = 0 :=
    (PiTensorProduct.tprod K).map_coord_zero .X rfl
  have hT' : T = (terms'.map (Tensor.pure (K := K))).sum := by
    rw [hterms', List.map_append, List.sum_append, ← hT, List.map_replicate, hzero]
    simp
  set x : Fin r → ∀ i, V i := fun j ↦ terms'.get (Fin.cast hlen'.symm j) with hx
  have hTsum : T = ∑ j : Fin r, Tensor.pure (K := K) (x j) := by
    rw [hT', Tensor.list_map_sum_eq_fin_sum]
    exact Fintype.sum_equiv (finCongr hlen') _ _ fun j ↦ rfl
  refine ⟨fun c ↦ ∑ j : Fin r, LinearMap.smulRight
    (LinearMap.proj (R := K) (φ := fun _ : Fin r ↦ K) j) (x j c), ?_⟩
  rw [diagonalTensor, map_sum, hTsum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Tensor.map_pure]
  congr 1
  funext c
  simp [hx, Pi.single_apply, eq_comm]

variable {W : Leg → Type w} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]

/-- **One-slice speedup for a nonminimal rank decomposition**
([AlmanLi2026], Theorem 6.1, p. 19, restriction form).

Let `f = (A,B,C)` restrict the diagonal tensor `⟨r⟩` to an `n × n × n` tensor `T = f ⟨r⟩` — that
is, `T = ∑ᵢ aᵢ bᵢ cᵢ` with `aᵢ = A eᵢ` and so on — and let `s` bound the rank of the contracted
matrix `M = ∑ᵢ aᵢ bᵢ`.  Then

```text
⟨r⟩ ⊕ ⟨1,s,1⟩  ⊵  T ⊕ ⟨1, r + s − 2n, 1⟩.
```

Nothing is added to the left-hand side beyond the `⟨1,s,1⟩` that the appended summand of
Proposition 5.4 requires. -/
theorem polynomialDegenerates_diagonalTensor_directSum_oneSlice
    [FiniteDimensional K (W .X)] [FiniteDimensional K (W .Y)]
    (n r s : ℕ) (f : ∀ c, (Fin r → K) →ₗ[K] W c)
    (hX : finrank K (W .X) = n) (hY : finrank K (W .Y) = n)
    (hs : finrank K (LinearMap.range (f .X ∘ₗ
        matrixFlatten (coordinateSum K (Fin r)) (diagonalTensor K (Fin r)) ∘ₗ
        (f .Y).dualMap)) ≤ s) :
    PolynomialDegenerates
      (Tensor.directSum (diagonalTensor K (Fin r)) (matrixMultiplication (K := K) 1 s 1))
      (Tensor.directSum (Tensor.map f (diagonalTensor K (Fin r)))
        (matrixMultiplication (K := K) 1 (r + s - 2 * n) 1)) := by
  have hmain := polynomialDegenerates_directSum_oneSliceAppend
    (diagonalTensor K (Fin r)) f (coordinateSum K (Fin r)) s hs
  rw [matrixRank_diagonalTensor, hX, hY] at hmain
  have hcard : Fintype.card (Fin r) = r := Fintype.card_fin r
  rw [hcard] at hmain
  have harith : r + s - n - n = r + s - 2 * n := by omega
  rwa [harith] at hmain

/-- **One-slice speedup for a nonminimal rank decomposition, the `s = n` clause**
([AlmanLi2026], Theorem 6.1, p. 19, "In particular").

For an `n × n × n` tensor of rank at most `r`,

```text
⟨r⟩ ⊕ ⟨1,n,1⟩  ⊵  T ⊕ ⟨1, r − n, 1⟩.
```

The choice `s = n` needs no hypothesis: the contracted matrix `M` lives in `U' ⊗ V'` with
`dim U' = dim V' = n`, so its rank is at most `n`. -/
theorem polynomialDegenerates_diagonalTensor_oneSlice_of_rankLE
    [FiniteDimensional K (W .X)] [FiniteDimensional K (W .Y)]
    (n r : ℕ) (T : Tensor3 K W)
    (hX : finrank K (W .X) = n) (hY : finrank K (W .Y) = n) (hT : RankLE r T) :
    PolynomialDegenerates
      (Tensor.directSum (diagonalTensor K (Fin r)) (matrixMultiplication (K := K) 1 n 1))
      (Tensor.directSum T (matrixMultiplication (K := K) 1 (r - n) 1)) := by
  obtain ⟨f, hf⟩ := restricts_diagonalTensor_of_rankLE hT
  have hs : finrank K (LinearMap.range (f .X ∘ₗ
      matrixFlatten (coordinateSum K (Fin r)) (diagonalTensor K (Fin r)) ∘ₗ
      (f .Y).dualMap)) ≤ n := by
    rw [← hX]
    exact Submodule.finrank_le _
  have hmain := polynomialDegenerates_diagonalTensor_directSum_oneSlice
    n r n f hX hY hs
  rw [hf] at hmain
  have harith : r + n - 2 * n = r - n := by omega
  rwa [harith] at hmain

end Field

end AlgebraicComplexity
