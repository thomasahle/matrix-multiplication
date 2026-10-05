/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.MatrixMultiplication.CTensorCore
import AlgebraicComplexity.Tensor.Coordinates

/-!
# Fusing a one-slice C-tensor

A C-tensor keeps the X and Y blocks of its constituents independent while sharing one Z block.
When all constituents are the canonical one-slice matrix-multiplication tensor `⟨1,d,1⟩`, this
shared-leg sum is not a direct sum of `h` matrix products: it is the single larger tensor
`⟨1,h*d,1⟩`.  This file proves that identification by an explicit legwise coordinate equivalence.

This finite semantic law is the bridge needed by zero/easy recursive Coppersmith--Winograd
leaves.  In those leaves an entire exact type class contributes its cardinality to a matrix
dimension; selecting one representative would lose the type-class entropy.
-/

namespace AlgebraicComplexity

open Tensor
open scoped DirectSum

universe u

namespace CTensor

/-- The coordinate set obtained by adjoining a C-tensor block label to one local coordinate of
`⟨1,d,1⟩`. -/
abbrev OneSliceBlockCoordinate (h d : ℕ) (c : Leg) :=
  Σ _ : BlockIndex h c, MMIndex 1 d 1 c

/-- Concatenate the independent X/Y blocks of `h` copies of `⟨1,d,1⟩`.  The unique Z block and
its unique local coordinate stay unchanged. -/
def oneSliceBlockCoordinateEquiv (h d : ℕ) :
    ∀ c, OneSliceBlockCoordinate h d c ≃ MMIndex 1 (h * d) 1 c
  | .X =>
      { toFun := fun a ↦ (a.2.1, finProdFinEquiv (a.1, a.2.2))
        invFun := fun a ↦
          ⟨(finProdFinEquiv.symm a.2).1, (a.1, (finProdFinEquiv.symm a.2).2)⟩
        left_inv := by
          rintro ⟨i, a, j⟩
          simp
        right_inv := by
          rintro ⟨a, j⟩
          apply Prod.ext
          · rfl
          · exact finProdFinEquiv.apply_symm_apply j }
  | .Y =>
      { toFun := fun a ↦ (finProdFinEquiv (a.1, a.2.1), a.2.2)
        invFun := fun a ↦
          ⟨(finProdFinEquiv.symm a.1).1, ((finProdFinEquiv.symm a.1).2, a.2)⟩
        left_inv := by
          rintro ⟨i, j, a⟩
          simp
        right_inv := by
          rintro ⟨j, a⟩
          apply Prod.ext
          · exact finProdFinEquiv.apply_symm_apply j
          · rfl }
  | .Z =>
      { toFun := fun a ↦ a.2
        invFun := fun a ↦ ⟨(), a⟩
        left_inv := by
          rintro ⟨i, a⟩
          cases i
          rfl
        right_inv := fun _ ↦ rfl }

/-- A defining term of the canonical one-slice constituent, written in the common C-tensor leg
family. -/
def oneSliceConstituentTerm
    (K : Type u) [CommSemiring K] (d : ℕ) (j : Fin d) :
    ∀ c, ConstituentSpace
      (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) c
  | .X => Pi.single (0, j) 1
  | .Y => Pi.single (j, 0) 1
  | .Z => Pi.single (0, 0) 1

/-- The canonical one-slice matrix-multiplication constituent, retyped in the uniform C-tensor
leg family. -/
noncomputable def oneSliceConstituent
    (K : Type u) [CommSemiring K] (d : ℕ) :
    Tensor3 K (ConstituentSpace
      (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z)) :=
  ∑ j : Fin d, pure (K := K) (oneSliceConstituentTerm K d j)

/-- Forget the harmless case split in the common C-tensor leg family. -/
noncomputable def oneSliceConstituentEquiv
    (K : Type u) [CommSemiring K] (d : ℕ) : ∀ c,
    ConstituentSpace
        (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) c
      ≃ₗ[K] MMSpace K 1 d 1 c := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

@[simp] theorem oneSliceConstituentEquiv_term
    {K : Type u} [CommSemiring K] (d : ℕ) (j : Fin d) (c : Leg) :
    oneSliceConstituentEquiv K d c (oneSliceConstituentTerm K d j c) =
      mmTerm (K := K) 1 d 1 0 j 0 c := by
  cases c <;> rfl

/-- The retyped one-slice constituent is the ordinary matrix-multiplication tensor
`⟨1,d,1⟩`. -/
theorem oneSliceConstituent_isomorphic_matrixMultiplication
    {K : Type u} [CommSemiring K] (d : ℕ) :
    Isomorphic (oneSliceConstituent K d) (matrixMultiplication (K := K) 1 d 1) := by
  refine ⟨oneSliceConstituentEquiv K d, ?_⟩
  change map (fun c ↦ (oneSliceConstituentEquiv K d c).toLinearMap)
      (oneSliceConstituent K d) = matrixMultiplication (K := K) 1 d 1
  unfold oneSliceConstituent matrixMultiplication
  rw [map_sum]
  simp only [Tensor.map_pure]
  simp [Fintype.sum_prod_type]

private noncomputable def directSumCoordinateEquiv
    {K : Type u} [CommSemiring K]
    {A : Type*} [Fintype A] [DecidableEq A]
    {κ : A → Type*} {ι : Type*} (e : (Σ a, κ a) ≃ ι) :
    (⨁ a, κ a → K) ≃ₗ[K] (ι → K) :=
  (DirectSum.linearEquivFunOnFintype K A (fun a ↦ κ a → K)).trans
    ((LinearEquiv.piCurry K (fun a : A ↦ fun _ : κ a ↦ K)).symm.trans
      (LinearEquiv.funCongrLeft K K e.symm))

private theorem sigma_uncurry_single
    {K : Type u} [AddMonoidWithOne K]
    {A : Type*} [DecidableEq A] {κ : A → Type*} [∀ a, DecidableEq (κ a)]
    (a : A) (i : κ a) :
    Sigma.uncurry
        (Pi.single a (Pi.single i (1 : K)) : ∀ a, κ a → K) =
      (Pi.single ⟨a, i⟩ (1 : K) : (Σ a, κ a) → K) := by
  funext x
  rcases x with ⟨b, j⟩
  by_cases h : b = a
  · subst b
    simp [Sigma.uncurry, Pi.single_apply]
  · have hs : (⟨b, j⟩ : Σ b, κ b) ≠ ⟨a, i⟩ := by
      intro hs
      exact h (congrArg Sigma.fst hs)
    simp [Sigma.uncurry, h, hs]

@[simp] private theorem directSumCoordinateEquiv_lof_single
    {K : Type u} [CommSemiring K]
    {A : Type*} [Fintype A] [DecidableEq A]
    {κ : A → Type*} [∀ a, DecidableEq (κ a)]
    {ι : Type*} [DecidableEq ι] (e : (Σ a, κ a) ≃ ι)
    (a : A) (i : κ a) :
    directSumCoordinateEquiv (K := K) e
        (DirectSum.lof K A (fun a ↦ κ a → K) a (Pi.single i 1)) =
      Pi.single (e ⟨a, i⟩) 1 := by
  simp only [directSumCoordinateEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, LinearEquiv.piCurry_symm_apply]
  rw [sigma_uncurry_single]
  exact funCongrLeft_symm_single (K := K) e ⟨a, i⟩ 1

/-- Legwise coordinate equivalence from the realization space of the uniform C-tensor to the
coordinate spaces of `⟨1,h*d,1⟩`. -/
noncomputable def oneSliceFusionEquiv
    (K : Type u) [CommSemiring K] (h d : ℕ) : ∀ c,
    PartitionedSpace K
        (BlockSpace
          (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h) c
      ≃ₗ[K] MMSpace K 1 (h * d) 1 c := by
  intro c
  cases c <;>
    exact directSumCoordinateEquiv (K := K) (oneSliceBlockCoordinateEquiv h d _)

/-- Linear-map form of `oneSliceFusionEquiv`. -/
noncomputable def oneSliceFusionMap
    (K : Type u) [CommSemiring K] (h d : ℕ) : ∀ c,
    PartitionedSpace K
        (BlockSpace
          (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h) c
      →ₗ[K] MMSpace K 1 (h * d) 1 c :=
  fun c ↦ (oneSliceFusionEquiv K h d c).toLinearMap

/-- On a defining term of constituent `i`, the fusion equivalence concatenates the local middle
index `j` into the global middle index `(i,j)`. -/
theorem oneSliceFusionEquiv_block_mmTerm
    {K : Type u} [CommSemiring K] (h d : ℕ) (i : Fin h) (j : Fin d) (c : Leg) :
    oneSliceFusionEquiv K h d c
        (blockInclude
          (K := K)
          (V := BlockSpace
            (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h)
          (address i) c
          (constituentToBlock
            (K := K)
            (X := MMSpace K 1 d 1 .X)
            (Y := MMSpace K 1 d 1 .Y)
            (Z := MMSpace K 1 d 1 .Z)
            (address i) c
            (oneSliceConstituentTerm K d j c))) =
      mmTerm (K := K) 1 (h * d) 1 0 (finProdFinEquiv (i, j)) 0 c := by
  cases c <;>
    simp [oneSliceFusionEquiv, blockInclude, constituentToBlock,
      constituentToBlockEquiv, address, mmTerm, oneSliceConstituentTerm,
      oneSliceBlockCoordinateEquiv]

/-- Tensor form of `oneSliceFusionEquiv_block_mmTerm`. -/
theorem map_oneSliceFusionMap_embedded_mmTerm
    {K : Type u} [CommSemiring K] (h d : ℕ) (i : Fin h) (j : Fin d) :
    map (oneSliceFusionMap K h d)
        (map
          (blockInclude
            (K := K)
            (V := BlockSpace
              (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h)
            (address i))
          (map
            (constituentToBlock
              (K := K)
              (X := MMSpace K 1 d 1 .X)
              (Y := MMSpace K 1 d 1 .Y)
              (Z := MMSpace K 1 d 1 .Z)
              (address i))
            (pure (K := K) (oneSliceConstituentTerm K d j)))) =
      pure (K := K)
        (mmTerm (K := K) 1 (h * d) 1 0 (finProdFinEquiv (i, j)) 0) := by
  simp only [Tensor.map_pure]
  congr 1
  funext c
  exact oneSliceFusionEquiv_block_mmTerm h d i j c

/-- One embedded C-tensor constituent fuses to the contiguous block of `d` global middle
coordinates carrying its constituent index. -/
theorem map_oneSliceFusionMap_embedded_constituent
    {K : Type u} [CommSemiring K] (h d : ℕ) (i : Fin h) :
    map (oneSliceFusionMap K h d)
        (map
          (blockInclude
            (K := K)
            (V := BlockSpace
              (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h)
            (address i))
          ((partitioned (fun _ : Fin h ↦ oneSliceConstituent K d)).constituent
            (address i))) =
      ∑ j : Fin d, pure (K := K)
        (mmTerm (K := K) 1 (h * d) 1 0 (finProdFinEquiv (i, j)) 0) := by
  change
    map (oneSliceFusionMap K h d)
        (map
          (blockInclude
            (K := K)
            (V := BlockSpace
              (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h)
            (address i))
          (map
            (constituentToBlock
              (K := K)
              (X := MMSpace K 1 d 1 .X)
              (Y := MMSpace K 1 d 1 .Y)
              (Z := MMSpace K 1 d 1 .Z)
              (address i))
            (oneSliceConstituent K d))) = _
  unfold oneSliceConstituent
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact map_oneSliceFusionMap_embedded_mmTerm h d i j

/-- **One-slice C-tensor fusion.**  A C-tensor consisting of `h` canonical copies of
`⟨1,d,1⟩` is legwise isomorphic to the single matrix-multiplication tensor `⟨1,h*d,1⟩`.

Proof sketch: the explicit leg equivalence concatenates the constituent label and local middle
coordinate by `finProdFinEquiv` on X and Y, while leaving the shared scalar Z coordinate fixed.
It sends each defining term indexed by `(i,j)` to the corresponding defining term of the target;
reindexing the resulting double sum proves the identity. -/
theorem partitioned_oneSliceMatrixMultiplication_isomorphic
    {K : Type u} [CommSemiring K] (h d : ℕ) :
    Isomorphic
      (partitioned (fun _ : Fin h ↦ oneSliceConstituent K d)).realize
      (matrixMultiplication (K := K) 1 (h * d) 1) := by
  refine ⟨oneSliceFusionEquiv K h d, ?_⟩
  change
    map (oneSliceFusionMap K h d)
        (partitioned (fun _ : Fin h ↦ oneSliceConstituent K d)).realize =
      matrixMultiplication (K := K) 1 (h * d) 1
  classical
  unfold PartitionedTensor.realize realizePartition
  rw [map_sum]
  calc
    (∑ s ∈ (partitioned
          (fun _ : Fin h ↦ oneSliceConstituent K d)).support,
        map (oneSliceFusionMap K h d)
          (map
            (blockInclude
              (K := K)
              (V := BlockSpace
                (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h)
              s)
            ((partitioned
              (fun _ : Fin h ↦ oneSliceConstituent K d)).constituent s))) =
        ∑ i : Fin h,
          map (oneSliceFusionMap K h d)
            (map
              (blockInclude
                (K := K)
                (V := BlockSpace
                  (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y) (MMSpace K 1 d 1 .Z) h)
                (address i))
              ((partitioned
                (fun _ : Fin h ↦ oneSliceConstituent K d)).constituent
                  (address i))) := by
      unfold CTensor.partitioned CTensor.support
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl
    _ = ∑ i : Fin h, ∑ j : Fin d, pure (K := K)
          (mmTerm (K := K) 1 (h * d) 1 0 (finProdFinEquiv (i, j)) 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact map_oneSliceFusionMap_embedded_constituent h d i
    _ = ∑ j : Fin (h * d), pure (K := K)
          (mmTerm (K := K) 1 (h * d) 1 0 j 0) := by
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv finProdFinEquiv _ _ fun _ ↦ rfl
    _ = matrixMultiplication (K := K) 1 (h * d) 1 := by
      symm
      unfold matrixMultiplication
      simp [Fintype.sum_prod_type]

/-- Restriction form of `partitioned_oneSliceMatrixMultiplication_isomorphic`. -/
theorem partitioned_oneSliceMatrixMultiplication_restricts
    {K : Type u} [CommSemiring K] (h d : ℕ) :
    Restricts
      (partitioned (fun _ : Fin h ↦ oneSliceConstituent K d)).realize
      (matrixMultiplication (K := K) 1 (h * d) 1) :=
  (partitioned_oneSliceMatrixMultiplication_isomorphic h d).restricts

end CTensor

end AlgebraicComplexity
