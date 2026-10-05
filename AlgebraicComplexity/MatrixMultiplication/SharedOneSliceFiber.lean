/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorFiberEnumeration
import AlgebraicComplexity.MatrixMultiplication.CTensorOneSliceExtraction
import AlgebraicComplexity.MatrixMultiplication.OneSliceCTensor

/-!
# Retyping a shared fibre from coherent one-slice certificates

A family of constituentwise restrictions to `⟨1,d,1⟩` does not by itself define a restriction of
their sum: two constituents carrying the same source block must use the same map on that block.
For a C-tensor fibre the `X` and `Y` labels are injective, so their maps may depend on the selected
address.  The `Z` label is shared, and its map must be common.

`SharedOneSliceFiberData` records exactly that local information.  This module constructs the
global `CTensor.FiberRetyping` and proves that every target constituent is the canonical one-slice
constituent.  In particular, no restriction or degeneration of the assembled family is assumed.
-/

namespace AlgebraicComplexity

open Tensor

universe u w

namespace CTensor

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Per-constituent one-slice certificates on a shared fibre, with one coherent map on its common
`Z` block.  `HEq` expresses precisely the transport forced by the equality between each selected
address's `Z` label and `zLabel`. -/
structure SharedOneSliceFiberData
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A)) (zLabel : A .Z) (d : ℕ) where
  /-- Explicit restriction of every selected constituent. -/
  certificate : ∀ address : selected,
    OneSliceRestriction (P.constituent address.1) d
  /-- The one map applied to the block shared by the fibre. -/
  zMap : V .Z zLabel →ₗ[K] MMSpace K 1 d 1 .Z
  /-- Every constituent certificate uses `zMap` on the shared leg, up to the necessary dependent
  transport of its source block. -/
  z_coherent : ∀ address : selected,
    HEq ((certificate address).constituentMap .Z) zMap

namespace SharedOneSliceFiberData

variable {P : PartitionedTensor (K := K) (A := A) V}
variable {selected : Finset (BlockAddress A)} {zLabel : A .Z} {d : ℕ}

/-- The selected address represented by one index of the canonical shared-fibre enumeration.
Its `Z` component is normalized to the recorded common label. -/
noncomputable def enumeratedAddress
    (hz : ∀ address ∈ selected, address .Z = zLabel)
    (i : Fin selected.card) : selected := by
  classical
  let e : selected ≃ Fin selected.card := selected.equivFin
  let xLabel : Fin selected.card → A .X := fun j ↦ (e.symm j).1 .X
  let yLabel : Fin selected.card → A .Y := fun j ↦ (e.symm j).1 .Y
  let address := fiberAddress xLabel yLabel zLabel i
  have haddress : address = (e.symm i).1 := by
    funext c
    cases c with
    | X => rfl
    | Y => rfl
    | Z => exact (hz _ (e.symm i).2).symm
  exact ⟨address, haddress.symm ▸ (e.symm i).2⟩

/-- Turn coherent constituentwise one-slice certificates into one global C-tensor retyping. -/
noncomputable def toFiberRetyping
    (D : SharedOneSliceFiberData P selected zLabel d)
    (hx : Set.InjOn (fun address ↦ address .X) (selected : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (selected : Set (BlockAddress A)))
    (hz : ∀ address ∈ selected, address .Z = zLabel) :
    FiberRetyping
      (X := MMSpace K 1 d 1 .X)
      (Y := MMSpace K 1 d 1 .Y)
      (Z := MMSpace K 1 d 1 .Z)
      P selected selected.card := by
  classical
  let e : selected ≃ Fin selected.card := selected.equivFin
  let xLabel : Fin selected.card → A .X := fun i ↦ (e.symm i).1 .X
  let yLabel : Fin selected.card → A .Y := fun i ↦ (e.symm i).1 .Y
  have hxLabel : Function.Injective xLabel := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    exact hx (e.symm i).2 (e.symm j).2 hij
  have hyLabel : Function.Injective yLabel := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    exact hy (e.symm i).2 (e.symm j).2 hij
  have haddress (i : Fin selected.card) :
      fiberAddress xLabel yLabel zLabel i = (e.symm i).1 := by
    funext c
    cases c with
    | X => rfl
    | Y => rfl
    | Z => exact (hz _ (e.symm i).2).symm
  refine
    { xLabel := xLabel
      yLabel := yLabel
      x_injective := hxLabel
      y_injective := hyLabel
      zLabel := zLabel
      selected_eq := ?_
      xMap := fun i ↦ (D.certificate (enumeratedAddress hz i)).constituentMap .X
      yMap := fun i ↦ (D.certificate (enumeratedAddress hz i)).constituentMap .Y
      zMap := D.zMap }
  ext address
  constructor
  · intro hselected
    apply Finset.mem_map.mpr
    let i := e ⟨address, hselected⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    change fiberAddress xLabel yLabel zLabel i = address
    rw [haddress]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨address, hselected⟩)
  · intro hmapped
    obtain ⟨i, _hi, hi⟩ := Finset.mem_map.mp hmapped
    rw [fiberAddressEmbedding_apply, haddress] at hi
    rw [← hi]
    exact (e.symm i).2

/-- The canonical enumeration used by `toFiberRetyping` maps every index back to its selected
source address. -/
theorem toFiberRetyping_sourceAddress
    (D : SharedOneSliceFiberData P selected zLabel d)
    (hx : Set.InjOn (fun address ↦ address .X) (selected : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (selected : Set (BlockAddress A)))
    (hz : ∀ address ∈ selected, address .Z = zLabel)
    (i : Fin selected.card) :
    (D.toFiberRetyping hx hy hz).sourceAddress i = (enumeratedAddress hz i).1 := by
  rfl

/-- Every constituent of the global retyping is mapped by its original explicit certificate. -/
theorem toFiberRetyping_targetConstituent
    (D : SharedOneSliceFiberData P selected zLabel d)
    (hx : Set.InjOn (fun address ↦ address .X) (selected : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (selected : Set (BlockAddress A)))
    (hz : ∀ address ∈ selected, address .Z = zLabel)
    (i : Fin selected.card) :
    (D.toFiberRetyping hx hy hz).targetConstituent i =
      CTensor.oneSliceConstituent K d := by
  let address : selected := enumeratedAddress hz i
  let C := D.toFiberRetyping hx hy hz
  unfold FiberRetyping.targetConstituent
  change Tensor.map (C.constituentMap i) (P.constituent address.1) = _
  have hmap : C.constituentMap i = (D.certificate address).constituentMap := by
    funext c
    cases c with
    | X => rfl
    | Y => rfl
    | Z => exact eq_of_heq (D.z_coherent address).symm
  rw [hmap]
  exact (D.certificate address).map_constituentMap

/-- Coherent one-slice certificates on an arbitrary shared fibre fuse the whole selected family
into one matrix-multiplication tensor.  The source restriction is constructed by
`toFiberRetyping`; it is not a hypothesis of this theorem. -/
theorem restricts_oneSliceMatrixMultiplication
    (D : SharedOneSliceFiberData P selected zLabel d)
    (hx : Set.InjOn (fun address ↦ address .X) (selected : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (selected : Set (BlockAddress A)))
    (hz : ∀ address ∈ selected, address .Z = zLabel) :
    Restricts (P.withSupport selected).realize
      (matrixMultiplication (K := K) 1 (selected.card * d) 1) := by
  let C := D.toFiberRetyping hx hy hz
  exact C.restricts_oneSliceMatrixMultiplication
    (D.toFiberRetyping_targetConstituent hx hy hz)

/-- Full-support specialization of `restricts_oneSliceMatrixMultiplication`. -/
theorem restricts_oneSliceMatrixMultiplication_of_support
    (D : SharedOneSliceFiberData P P.support zLabel d)
    (hx : Set.InjOn (fun address ↦ address .X) (P.support : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (P.support : Set (BlockAddress A)))
    (hz : ∀ address ∈ P.support, address .Z = zLabel) :
    Restricts P.realize
      (matrixMultiplication (K := K) 1 (P.support.card * d) 1) := by
  let C := D.toFiberRetyping hx hy hz
  exact C.restricts_oneSliceMatrixMultiplication_of_support
    (D.toFiberRetyping_targetConstituent hx hy hz)

end SharedOneSliceFiberData

end CTensor

end AlgebraicComplexity
