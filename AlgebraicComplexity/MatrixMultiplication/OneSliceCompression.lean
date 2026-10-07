/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.MatrixMultiplication.DirectSumIdentity
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# One-slice compression

This file proves [AlmanLi2026, Proposition 5.7, p. 18], which is [Strassen1988, Proposition 6.4]:
a linear map applied to one leg of a direct sum of one-slice tensors loses at most its corank.

Let `T = ⊕_{i<k} ⟨1, n i, 1⟩` and let `A` be an endomorphism of its `X` leg whose image has
codimension `p`.  Then there are `q i ≤ n i` with `∑ q i = p` such that

```text
(A ⊗ id ⊗ id) T   ≥   ⊕_{i<k} ⟨1, n i − q i, 1⟩.
```

## Proof

Write `T = ∑_{i,j} x_{ij} ⊗ y_{ij} ⊗ z_i`.  The vectors `A x_{ij}` span the image of `A`, so a
subfamily `D` of exactly `rank A = ∑ n i − p` of them is linearly independent.  Let `D_i` be the
positions of block `i` that belong to `D`, and `q i = n i − |D_i|`.  The restriction

* sends `A x_{ij}`, for `(i,j) ∈ D`, to the corresponding basis vector of the `i`-th target
  slice — possible because the family is linearly independent, and the only place where a field
  is used;
* sends `y_{ij}` to the corresponding basis vector if `(i,j) ∈ D` and to `0` otherwise;
* sends `z_i` to the `Z` vector of the `i`-th target slice.

The terms outside `D` die on the `Y` leg, and the terms in `D` are exactly the target.

## Main results

* `span_range_indexedSliceX`: the vectors `x_{ij}` span the `X` leg.
* `restricts_map_oneSliceDirectSum`: **Proposition 5.7**.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Proposition 5.7, p. 18.
* V. Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988)
  ([Strassen1988]), Proposition 6.4.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u

section OneSliceVectors

variable (K : Type u) [Field K] {k : ℕ} (n : Fin k → ℕ)

/-- The `X` basis vector `j` of the slice `i` of `⊕ ⟨1, n i, 1⟩`. -/
noncomputable def indexedSliceX (e : (i : Fin k) × Fin (n i)) :
    MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .X :=
  indexedInclude (K := K) (V := fun i : Fin k ↦ MMSpace K 1 (n i) 1) e.1 .X
    (Pi.single ((0 : Fin 1), e.2) 1)

/-- The `Y` basis vector `j` of the slice `i` of `⊕ ⟨1, n i, 1⟩`. -/
noncomputable def indexedSliceY (e : (i : Fin k) × Fin (n i)) :
    MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .Y :=
  indexedInclude (K := K) (V := fun i : Fin k ↦ MMSpace K 1 (n i) 1) e.1 .Y
    (Pi.single (e.2, (0 : Fin 1)) 1)

/-- The `Z` basis vector of the slice `i` of `⊕ ⟨1, n i, 1⟩`. -/
noncomputable def indexedSliceZ (i : Fin k) :
    MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .Z :=
  indexedInclude (K := K) (V := fun i : Fin k ↦ MMSpace K 1 (n i) 1) i .Z
    (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1)

/-- A direct sum of one-slice tensors as a sum of pure tensors. -/
theorem oneSliceDirectSum_eq_sum :
    matrixMultiplicationDirectSum K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) =
      ∑ i : Fin k, ∑ j : Fin (n i), Tensor.pure (K := K)
        (ofLegs (V := MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1))
          (indexedSliceX K n ⟨i, j⟩) (indexedSliceY K n ⟨i, j⟩) (indexedSliceZ K n i)) := by
  rw [matrixMultiplicationDirectSum, indexedDirectSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [matrixMultiplication_outer_one, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Tensor.map_pure]
  refine congrArg _ ?_
  funext c
  cases c <;> rfl

/-- The vectors `x_{ij}` span the `X` leg of `⊕ ⟨1, n i, 1⟩`. -/
theorem span_range_indexedSliceX :
    Submodule.span K (Set.range (indexedSliceX K n)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro u -
  induction u using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of i f =>
    have hf : f = ∑ j : Fin (n i), f ((0 : Fin 1), j) •
        (Pi.single ((0 : Fin 1), j) 1 : Fin 1 × Fin (n i) → K) := by
      funext cj
      obtain ⟨c, j⟩ := cj
      have hc : c = 0 := Subsingleton.elim _ _
      subst hc
      simp [Finset.sum_apply, Pi.single_apply]
    have hconv : DirectSum.of (fun i : Fin k ↦ MMSpace K 1 (n i) 1 .X) i f =
        indexedInclude (K := K) (V := fun i : Fin k ↦ MMSpace K 1 (n i) 1) i .X f := by
      rw [indexedInclude, DirectSum.lof_eq_of]
      congr
      exact Subsingleton.elim _ _
    rw [hconv, hf, map_sum]
    exact Submodule.sum_mem _ fun j _ ↦ by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, j⟩, rfl⟩)
  | add a b ha hb => exact add_mem ha hb

end OneSliceVectors

section Compression

variable {K : Type u} [Field K] {k : ℕ} (n : Fin k → ℕ)

/-- A linearly independent family can be sent to arbitrary prescribed values by a linear map. -/
theorem LinearIndependent.exists_linearMap_apply_eq {V W κ : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {w : κ → V} (hw : LinearIndependent K w) (t : κ → W) :
    ∃ L : V →ₗ[K] W, ∀ s, L (w s) = t s := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination K t).comp hw.repr)
  refine ⟨g, fun s ↦ ?_⟩
  have hmem : w s ∈ Submodule.span K (Set.range w) := Submodule.subset_span ⟨s, rfl⟩
  have h := congrArg (fun φ ↦ φ ⟨w s, hmem⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
  rw [h, hw.repr_eq_single s ⟨w s, hmem⟩ rfl, Finsupp.linearCombination_single, one_smul]

/-- **One-slice compression** ([AlmanLi2026], Proposition 5.7, p. 18; [Strassen1988],
Proposition 6.4).

Let `A` be an endomorphism of the `X` leg of `T = ⊕_{i<k} ⟨1, n i, 1⟩` whose image has codimension
`p`.  Then `(A ⊗ id ⊗ id) T` restricts onto `⊕_{i<k} ⟨1, n i − q i, 1⟩` for some `q i ≤ n i` with
`∑ q i = p`. -/
theorem restricts_map_oneSliceDirectSum (p : ℕ)
    (A : MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .X →ₗ[K]
      MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .X)
    (hA : finrank K (LinearMap.range A) + p = ∑ i, n i) :
    ∃ q : Fin k → ℕ, (∀ i, q i ≤ n i) ∧ (∑ i, q i = p) ∧
      Restricts
        (Tensor.map (ofLegs (V := fun c ↦
            MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) c →ₗ[K]
              MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) c)
            A LinearMap.id LinearMap.id)
          (matrixMultiplicationDirectSum K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1)))
        (matrixMultiplicationDirectSum K (fun _ : Fin k ↦ 1) (fun i ↦ n i - q i)
          (fun _ ↦ 1)) := by
  classical
  -- A linearly independent subfamily of the images spanning the range.
  let v : ((i : Fin k) × Fin (n i)) → MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .X :=
    fun e ↦ A (indexedSliceX K n e)
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hrange : Submodule.span K (Set.range v) = LinearMap.range A := by
    rw [show Set.range v = A '' Set.range (indexedSliceX K n) from (Set.range_comp A _),
      ← Submodule.map_span, span_range_indexedSliceX, Submodule.map_top]
  have hcardκ : Fintype.card κ = finrank K (LinearMap.range A) := by
    rw [← hrange, ← hspan, finrank_span_eq_card hli]
  -- The chosen positions, block by block.
  let D : ∀ i : Fin k, Finset (Fin (n i)) := fun i ↦
    Finset.univ.filter fun j ↦ (⟨i, j⟩ : (i : Fin k) × Fin (n i)) ∈ Set.range a
  have hDle : ∀ i, (D i).card ≤ n i := fun i ↦ by
    simpa using Finset.card_le_univ (D i)
  have hDsum : ∑ i, (D i).card = Fintype.card κ := by
    rw [← Finset.card_sigma, ← Finset.card_univ (α := κ),
      ← Finset.card_image_of_injective Finset.univ ha]
    refine congrArg Finset.card (Finset.ext fun e ↦ ?_)
    obtain ⟨i, j⟩ := e
    simp [D]
  refine ⟨fun i ↦ n i - (D i).card, fun i ↦ Nat.sub_le _ _, ?_, ?_⟩
  · show ∑ i, (n i - (D i).card) = p
    have h1 : ∑ i, (n i - (D i).card) + ∑ i, (D i).card = ∑ i, n i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (hDle i)
    omega
  -- The increasing enumeration of each block of chosen positions.
  have hsize : ∀ i, (D i).card = n i - (n i - (D i).card) := fun i ↦ by
    have := hDle i
    omega
  let φ : ∀ i : Fin k, Fin (n i - (n i - (D i).card)) → Fin (n i) :=
    fun i ↦ (D i).orderEmbOfFin (hsize i)
  have hφinj : ∀ i, Function.Injective (φ i) := fun i ↦ ((D i).orderEmbOfFin (hsize i)).injective
  have hφmem : ∀ i t, (⟨i, φ i t⟩ : (i : Fin k) × Fin (n i)) ∈ Set.range a := fun i t ↦ by
    exact (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem (D i) (hsize i) t)).2
  -- The chosen images form a linearly independent family indexed by the target positions.
  let b : ((i : Fin k) × Fin (n i - (n i - (D i).card))) → κ :=
    fun s ↦ (hφmem s.1 s.2).choose
  have hb : ∀ s, a (b s) = ⟨s.1, φ s.1 s.2⟩ := fun s ↦ (hφmem s.1 s.2).choose_spec
  have hbinj : Function.Injective b := by
    intro s s' h
    have h' : (⟨s.1, φ s.1 s.2⟩ : (i : Fin k) × Fin (n i)) = ⟨s'.1, φ s'.1 s'.2⟩ := by
      rw [← hb s, ← hb s', h]
    obtain ⟨i, t⟩ := s
    obtain ⟨i', t'⟩ := s'
    obtain rfl : i = i' := congrArg Sigma.fst h'
    have ht : φ i t = φ i t' := eq_of_heq (Sigma.mk.inj h').2
    rw [hφinj i ht]
  have hwli : LinearIndependent K fun s : (i : Fin k) × Fin (n i - (n i - (D i).card)) ↦
      v ⟨s.1, φ s.1 s.2⟩ := by
    have h := hli.comp b hbinj
    have heq : (fun s : (i : Fin k) × Fin (n i - (n i - (D i).card)) ↦ v ⟨s.1, φ s.1 s.2⟩) =
        (v ∘ a) ∘ b := funext fun s ↦ by simp only [Function.comp_apply, hb s]
    rw [heq]
    exact h
  -- The three leg maps.
  let n' : Fin k → ℕ := fun i ↦ n i - (n i - (D i).card)
  obtain ⟨L, hL⟩ := LinearIndependent.exists_linearMap_apply_eq hwli (indexedSliceX K n')
  let blockMap : ∀ (i : Fin k) (c : Leg), MMSpace K 1 (n i) 1 c →ₗ[K]
      MMDirectSumSpace K (fun _ : Fin k ↦ 1) n' (fun _ ↦ 1) c := fun i c ↦
    match c with
    | .X => 0
    | .Y => ∑ t : Fin (n' i),
        (LinearMap.proj (R := K) (φ := fun _ : Fin (n i) × Fin 1 ↦ K) (φ i t, 0)).smulRight
          (indexedSliceY K n' ⟨i, t⟩)
    | .Z => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
        (indexedSliceZ K n' i)
  let M := indexedFoldMap (K := K) (V := fun i : Fin k ↦ MMSpace K 1 (n i) 1) blockMap
  refine ⟨ofLegs (V := fun c ↦ MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) c →ₗ[K]
    MMDirectSumSpace K (fun _ : Fin k ↦ 1) n' (fun _ ↦ 1) c) L (M .Y) (M .Z), ?_⟩
  have hMY : ∀ (i : Fin k) (j : Fin (n i)), M .Y (indexedSliceY K n ⟨i, j⟩) =
      ∑ t : Fin (n' i), (if φ i t = j then (1 : K) else 0) • indexedSliceY K n' ⟨i, t⟩ := by
    intro i j
    have h := congrArg (fun g ↦ g (Pi.single (j, (0 : Fin 1)) 1 : Fin (n i) × Fin 1 → K))
      (indexedFoldMap_comp_indexedInclude (K := K)
        (V := fun i : Fin k ↦ MMSpace K 1 (n i) 1) blockMap i .Y)
    simp only [LinearMap.comp_apply] at h
    rw [indexedSliceY]
    refine h.trans ?_
    simp only [blockMap, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Pi.single_apply, Prod.mk.injEq, and_true]
  have hMZ : ∀ i : Fin k, M .Z (indexedSliceZ K n i) = indexedSliceZ K n' i := by
    intro i
    have h := congrArg (fun g ↦ g (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K))
      (indexedFoldMap_comp_indexedInclude (K := K)
        (V := fun i : Fin k ↦ MMSpace K 1 (n i) 1) blockMap i .Z)
    simp only [LinearMap.comp_apply] at h
    rw [indexedSliceZ]
    refine h.trans ?_
    simp [blockMap]
  rw [oneSliceDirectSum_eq_sum, oneSliceDirectSum_eq_sum]
  simp only [map_sum, map_pure_ofLegs, ofLegs, LinearMap.id_apply, hMY, hMZ, pure_ofLegs_sum_Y,
    pure_ofLegs_smul_Y]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.sum_eq_single (φ i t)]
  · rw [if_pos rfl, one_smul]
    have h := hL ⟨i, t⟩
    simp only [v] at h
    rw [h]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Compression

end AlgebraicComplexity
