/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.MatrixMultiplication.NonminimalBorderRankSpeedup

/-!
# The grouped one-slice speedup for a border-rank decomposition

This file proves [AlmanLi2026, Theorem 6.3, p. 21], in the quantitative form displayed on p. 22:
if an `n × n × n` tensor `T` has border rank at most `r` and `3np ≤ r`, then

```text
⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)  ⊵  T ⊕ (p ⊙ ⟨1,2n,1⟩).
```

Each of the `p` appended slices of size `n` comes back twice as large.  This is the source of the
`r − Ω(r / n^{1/3})` asymptotic-rank bound of the paper.

## Why this is not Theorem 6.1 applied `p` times

The paper's first proof partitions the certificate into `p` groups of `3n` terms and applies
Theorem 6.1 to each.  For a *border*-rank certificate that does not typecheck: the sum of the
terms of one group is a polynomial tensor with no leading term of its own — only the sum over all
groups leads with `T`.  The core theorem
`Tensor.polynomialDegenerates_oneSliceFrameTensor_directSum_of_span` is therefore grouped from
the start: one polynomial family carries the whole certificate, and the kernel frames are chosen
group by group and brought to a common leading degree.  What is left for this file is
bookkeeping:

* the source `⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)`, written with indexed direct sums of matrix-multiplication
  tensors, restricts onto the framed source in standard coordinates
  (`restricts_directSum_standardOneSliceFrame`);
* the terms are grouped by `i ↦ ⌊i / 3n⌋`, with the terms beyond `3np` left ungrouped
  (`groupOfTerm`, `le_card_filter_groupOfTerm`);
* when `n = 0` the legs of `T` need not be finite-dimensional (`finrank = 0` does not say so), and
  no basis is available; that case is the span form of the core with every term ungrouped.

## Main results

* `standardOneSliceFrame`: `⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)` in standard coordinates, as a framed source.
* `restricts_directSum_standardOneSliceFrame`: the indexed-direct-sum presentation restricts onto
  it.
* `polynomialDegenerates_grouped_oneSlice_of_borderRankLE`: **Theorem 6.3**, border-rank form.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Theorem 6.3, pp. 21–22.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u v

section Frame

variable (K : Type u) [Field K]

/-- Coordinate indices of `⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)`: a diagonal index or a slice index on the `X` and
`Y` legs, a diagonal index or a slice number on the `Z` leg. -/
abbrev OneSliceFrameIndex (r p n : ℕ) : Leg → Type
  | .X => Fin r ⊕ Fin p × Fin n
  | .Y => Fin r ⊕ Fin p × Fin n
  | .Z => Fin r ⊕ Fin p

instance (r p n : ℕ) (c : Leg) : Fintype (OneSliceFrameIndex r p n c) := by
  cases c <;> infer_instance

instance (r p n : ℕ) (c : Leg) : DecidableEq (OneSliceFrameIndex r p n c) := by
  cases c <;> infer_instance

/-- `⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)` in standard coordinates, as a framed source. -/
noncomputable def standardOneSliceFrame (r p n : ℕ) :
    Tensor3 K (CoordinateSpace K (OneSliceFrameIndex r p n)) :=
  oneSliceFrameTensor (S := CoordinateSpace K (OneSliceFrameIndex r p n))
    (Pi.basisFun K (Fin r ⊕ Fin p × Fin n)) (Pi.basisFun K (Fin r ⊕ Fin p × Fin n))
    (Pi.basisFun K (Fin r ⊕ Fin p))

/-- The `i`-th summand `⟨1,1,1⟩` of `⟨r⟩` goes to the `i`-th diagonal coordinate on every leg. -/
noncomputable def unitToFrame (r p n : ℕ) (i : Fin r) :
    ∀ c, MMSpace K 1 1 1 c →ₗ[K] CoordinateSpace K (OneSliceFrameIndex r p n) c
  | .X => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
      (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin p × Fin n → K)
  | .Y => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
      (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin p × Fin n → K)
  | .Z => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
      (Pi.single (Sum.inl i) 1 : Fin r ⊕ Fin p → K)

/-- The `a`-th slice `⟨1,n,1⟩` goes to the slice coordinates `(a, j)` on the `X` and `Y` legs and
to the slice coordinate `a` on the `Z` leg. -/
noncomputable def sliceToFrame (r p n : ℕ) (a : Fin p) :
    ∀ c, MMSpace K 1 n 1 c →ₗ[K] CoordinateSpace K (OneSliceFrameIndex r p n) c
  | .X => ∑ j : Fin n, (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin n ↦ K) (0, j)).smulRight
      (Pi.single (Sum.inr (a, j)) 1 : Fin r ⊕ Fin p × Fin n → K)
  | .Y => ∑ j : Fin n, (LinearMap.proj (R := K) (φ := fun _ : Fin n × Fin 1 ↦ K) (j, 0)).smulRight
      (Pi.single (Sum.inr (a, j)) 1 : Fin r ⊕ Fin p × Fin n → K)
  | .Z => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
      (Pi.single (Sum.inr a) 1 : Fin r ⊕ Fin p → K)

/-- The indexed-direct-sum presentation of `⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)` restricts onto the framed source
in standard coordinates. -/
theorem restricts_directSum_standardOneSliceFrame (r p n : ℕ) :
    Restricts
      (Tensor.directSum
        (matrixMultiplicationDirectSum K (ι := Fin r) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1))
        (matrixMultiplicationDirectSum K (fun _ : Fin p ↦ 1) (fun _ ↦ n) (fun _ ↦ 1)))
      (standardOneSliceFrame K r p n) := by
  classical
  let FU := indexedFoldMap (K := K) (V := fun _ : Fin r ↦ MMSpace K 1 1 1)
    (fun i c ↦ unitToFrame K r p n i c)
  let FS := indexedFoldMap (K := K) (V := fun _ : Fin p ↦ MMSpace K 1 n 1)
    (fun a c ↦ sliceToFrame K r p n a c)
  refine ⟨fun c ↦ LinearMap.coprod (FU c) (FS c), ?_⟩
  have hL : ∀ X : Tensor3 K (MMDirectSumSpace K (ι := Fin r) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)),
      Tensor.map (fun c ↦ LinearMap.coprod (FU c) (FS c))
        (Tensor.map (Tensor.includeLeft (K := K)
          (W := MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ n) (fun _ ↦ 1))) X) =
        Tensor.map FU X := by
    intro X
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine congrArg (fun G ↦ Tensor.map G X) (funext fun c ↦ LinearMap.ext fun x ↦ ?_)
    simp
  have hR : ∀ X : Tensor3 K (MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ n) (fun _ ↦ 1)),
      Tensor.map (fun c ↦ LinearMap.coprod (FU c) (FS c))
        (Tensor.map (Tensor.includeRight (K := K)
          (V := MMDirectSumSpace K (ι := Fin r) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1))) X) =
        Tensor.map FS X := by
    intro X
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine congrArg (fun G ↦ Tensor.map G X) (funext fun c ↦ LinearMap.ext fun x ↦ ?_)
    simp
  rw [Tensor.directSum, map_add, hL, hR, matrixMultiplicationDirectSum,
    matrixMultiplicationDirectSum, map_indexedFoldMap_indexedDirectSum,
    map_indexedFoldMap_indexedDirectSum, standardOneSliceFrame, oneSliceFrameTensor]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [matrixMultiplication_outer_one, Fin.sum_univ_one, Tensor.map_pure]
    refine congrArg _ ?_
    funext c
    cases c <;> simp [unitToFrame, mmTerm]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [matrixMultiplication_outer_one, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Tensor.map_pure]
    refine congrArg _ ?_
    funext c
    cases c <;> simp [sliceToFrame, mmTerm, Pi.single_apply]

end Frame

section Grouping

/-- Group the first `N · p` of `r` certificate terms into `p` consecutive blocks of `N`; the
remaining terms belong to no group. -/
def groupOfTerm {r : ℕ} (N p : ℕ) (i : Fin r) : Option (Fin p) :=
  if h : (i : ℕ) < N * p then some ⟨i / N, Nat.div_lt_of_lt_mul h⟩ else none

/-- Every group of `groupOfTerm` has at least `N` terms as soon as `N · p ≤ r`. -/
theorem le_card_filter_groupOfTerm {r N p : ℕ} (hN : 0 < N) (hr : N * p ≤ r) (a : Fin p) :
    N ≤ (Finset.univ.filter fun i : Fin r ↦ groupOfTerm N p i = some a).card := by
  classical
  have hblock : ∀ k : Fin N, N * (a : ℕ) + k < N * p := fun k ↦ by
    have h1 : N * ((a : ℕ) + 1) ≤ N * p := Nat.mul_le_mul_left N (by omega)
    rw [Nat.mul_add_one] at h1
    omega
  let f : Fin N → Fin r := fun k ↦ ⟨N * (a : ℕ) + k, lt_of_lt_of_le (hblock k) hr⟩
  have hinj : Function.Injective f := fun k k' h ↦ by
    have h' := congrArg Fin.val h
    simp only [f] at h'
    exact Fin.ext (by omega)
  have hsub : Finset.univ.image f ⊆
      Finset.univ.filter fun i : Fin r ↦ groupOfTerm N p i = some a := by
    intro i hi
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hval : (N * (a : ℕ) + k) / N = a := by
      rw [Nat.mul_add_div hN, Nat.div_eq_of_lt k.2, Nat.add_zero]
    simp only [groupOfTerm, f, dif_pos (hblock k)]
    exact congrArg some (Fin.ext hval)
  calc N = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Finset.card_le_card hsub

end Grouping

section Main

variable {K : Type u} [Field K]
variable {V : Leg → Type v} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]

/-- **The grouped one-slice speedup for a border-rank decomposition**
([AlmanLi2026], Theorem 6.3, p. 21, in the quantitative form displayed on p. 22).

If the three legs of `T` have dimension `n`, `T` has border rank at most `r`, and `3np ≤ r`, then

```text
⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)  ⊵  T ⊕ (p ⊙ ⟨1,2n,1⟩).
```

Only the dimensions of the `X` and `Y` legs are used.  The legs are not assumed
finite-dimensional: for `n > 0` that follows from `finrank = n`, and for `n = 0` the statement
reduces to `⟨r⟩ ⊵ T`. -/
theorem polynomialDegenerates_grouped_oneSlice_of_borderRankLE
    (n r p : ℕ) (T : Tensor3 K V) (hV : ∀ c, finrank K (V c) = n) (hT : BorderRankLE r T)
    (hr : 3 * n * p ≤ r) :
    PolynomialDegenerates
      (Tensor.directSum
        (matrixMultiplicationDirectSum K (ι := Fin r) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1))
        (matrixMultiplicationDirectSum K (fun _ : Fin p ↦ 1) (fun _ ↦ n) (fun _ ↦ 1)))
      (Tensor.directSum T
        (matrixMultiplicationDirectSum K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1))) := by
  classical
  obtain ⟨d, x, hx⟩ := hT.exists_fin_family
  -- The target slices as sums of pure tensors.
  let x' : Fin p → Fin (2 * n) →
      MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1) .X :=
    fun a k ↦ indexedInclude (K := K) (V := fun _ : Fin p ↦ MMSpace K 1 (2 * n) 1) a .X
      (Pi.single ((0 : Fin 1), k) 1)
  let y' : Fin p → Fin (2 * n) →
      MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1) .Y :=
    fun a k ↦ indexedInclude (K := K) (V := fun _ : Fin p ↦ MMSpace K 1 (2 * n) 1) a .Y
      (Pi.single (k, (0 : Fin 1)) 1)
  let z' : Fin p → MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1) .Z :=
    fun a ↦ indexedInclude (K := K) (V := fun _ : Fin p ↦ MMSpace K 1 (2 * n) 1) a .Z
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1)
  have htgt : matrixMultiplicationDirectSum K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1) =
      ∑ a, ∑ k, Tensor.pure (K := K)
        (ofLegs (V := MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1))
          (x' a k) (y' a k) (z' a)) := by
    rw [matrixMultiplicationDirectSum, indexedDirectSum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [matrixMultiplication_outer_one, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Tensor.map_pure]
    refine congrArg _ ?_
    funext c
    cases c <;> rfl
  -- The framed source in standard coordinates degenerates to the target.
  have hframe : PolynomialDegenerates (standardOneSliceFrame K r p n)
      (Tensor.directSum T (∑ a, ∑ k, Tensor.pure (K := K)
        (ofLegs (V := MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1))
          (x' a k) (y' a k) (z' a)))) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact polynomialDegenerates_oneSliceFrameTensor_directSum_of_span
        (S := CoordinateSpace K (OneSliceFrameIndex r p 0))
        (W' := MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * 0) (fun _ ↦ 1))
        (nX := 0) (Pi.basisFun K (Fin r ⊕ Fin p × Fin 0)) (Pi.basisFun K (Fin r ⊕ Fin p × Fin 0))
        (Pi.basisFun K (Fin r ⊕ Fin p)) x hx (fun _ ↦ none)
        Fin.elim0 (fun _ _ ↦ 0) (fun i a h ↦ by simp at h)
        Fin.elim0 (fun _ _ ↦ 0) (fun i a h ↦ by simp at h)
        (fun a ↦ by simp) x' y' z'
    · haveI : Module.Finite K (V .X) := Module.finite_of_finrank_pos (by rw [hV]; exact hn)
      haveI : Module.Finite K (V .Y) := Module.finite_of_finrank_pos (by rw [hV]; exact hn)
      have hg : ∀ a : Fin p, 2 * n ≤
          (Finset.univ.filter fun i : Fin r ↦ groupOfTerm (3 * n) p i = some a).card - n := by
        intro a
        have h := le_card_filter_groupOfTerm (r := r) (N := 3 * n) (by omega) hr a
        omega
      exact polynomialDegenerates_oneSliceFrameTensor_directSum
        (S := CoordinateSpace K (OneSliceFrameIndex r p n))
        (W' := MMDirectSumSpace K (fun _ : Fin p ↦ 1) (fun _ ↦ 2 * n) (fun _ ↦ 1))
        (Pi.basisFun K (Fin r ⊕ Fin p × Fin n)) (Pi.basisFun K (Fin r ⊕ Fin p × Fin n))
        (Pi.basisFun K (Fin r ⊕ Fin p))
        (finBasisOfFinrankEq K (V .X) (hV .X)) (finBasisOfFinrankEq K (V .Y) (hV .Y)) x hx
        (groupOfTerm (3 * n) p) hg x' y' z'
  rw [htgt]
  exact (PolynomialDegenerates.of_restricts
    (restricts_directSum_standardOneSliceFrame K r p n)).trans hframe

end Main

end AlgebraicComplexity
