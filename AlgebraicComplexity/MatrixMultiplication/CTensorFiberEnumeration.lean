/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorExtraction

/-!
# Canonical enumeration of shared-leg partition fibers

`CTensor.FiberRetyping` deliberately asks a client to enumerate its selected support by `Fin h`.
This module constructs that enumeration canonically from the finite support itself.  A client only
has to prove the semantic properties that matter: the `X` and `Y` labels are injective on the
selected support, the `Z` label is common, and the stated block maps exist.

The constructor is useful for exact type classes, where the whole finite family must be retained.
It neither chooses one representative nor assumes a degeneration of the assembled tensor.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace CTensor.FiberRetyping

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v w)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {X Y Z : Type (max u v w)}
variable [AddCommMonoid X] [Module K X]
variable [AddCommMonoid Y] [Module K Y]
variable [AddCommMonoid Z] [Module K Z]

/-- Construct a C-tensor retyping from an arbitrary finite shared-`Z` support.

The source maps are indexed by the subtype of selected addresses.  Internally, the constructor
uses the canonical equivalence from that subtype to `Fin selected.card`; no ordering property is
exposed or used. -/
noncomputable def ofSharedSupport
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A))
    (hx : Set.InjOn (fun address ↦ address .X) (selected : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (selected : Set (BlockAddress A)))
    (zLabel : A .Z)
    (hz : ∀ address ∈ selected, address .Z = zLabel)
    (xMap : ∀ address : selected, V .X (address.1 .X) →ₗ[K] X)
    (yMap : ∀ address : selected, V .Y (address.1 .Y) →ₗ[K] Y)
    (zMap : V .Z zLabel →ₗ[K] Z) :
    FiberRetyping (X := X) (Y := Y) (Z := Z) P selected selected.card := by
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
    | Z => exact (hz (e.symm i).1 (e.symm i).2).symm
  refine
    { xLabel := xLabel
      yLabel := yLabel
      x_injective := hxLabel
      y_injective := hyLabel
      zLabel := zLabel
      selected_eq := ?_
      xMap := fun i ↦ xMap (e.symm i)
      yMap := fun i ↦ yMap (e.symm i)
      zMap := zMap }
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

/-- Canonically embed every selected source block into the full ambient partitioned leg space.

This specialization needs no client-supplied linear maps.  It is the first semantic step in
recognizing a selected shared-leg support as a C-tensor; later maps may uniformly simplify its
constituents without revisiting the finite enumeration. -/
noncomputable def ofSharedSupportAmbient
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A))
    (hx : Set.InjOn (fun address ↦ address .X) (selected : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (selected : Set (BlockAddress A)))
    (zLabel : A .Z)
    (hz : ∀ address ∈ selected, address .Z = zLabel) :
    FiberRetyping
      (X := PartitionedSpace K V .X)
      (Y := PartitionedSpace K V .Y)
      (Z := PartitionedSpace K V .Z)
      P selected selected.card :=
  ofSharedSupport.{u, v, w} P selected hx hy zLabel hz
    (fun address ↦ blockInclude (K := K) (V := V) address.1 .X)
    (fun address ↦ blockInclude (K := K) (V := V) address.1 .Y)
    (DirectSum.lof K (A .Z) (V .Z) zLabel)

@[simp] theorem ofSharedSupportAmbient_zMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A))
    (hx : Set.InjOn (fun address ↦ address .X) (selected : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address .Y) (selected : Set (BlockAddress A)))
    (zLabel : A .Z)
    (hz : ∀ address ∈ selected, address .Z = zLabel) :
    (ofSharedSupportAmbient.{u, v, w} P selected hx hy zLabel hz).zMap =
      DirectSum.lof K (A .Z) (V .Z) zLabel :=
  rfl

end CTensor.FiberRetyping

end AlgebraicComplexity
