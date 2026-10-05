/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensor

/-!
# Retyping a shared-leg partition fiber as a C-tensor

Hashing for the exceptional Coppersmith--Winograd constituent isolates the X and Y block
labels but deliberately retains several addresses with one common Z label.  Such a fiber is a
C-tensor, although its source blocks generally live inside a larger ambient partition and its
constituents are not initially indexed by `Fin h`.

This file supplies the reusable semantic bridge.  A `FiberRetyping` enumerates a selected
support, records injectivity on X and Y, records the common Z block, and gives leg maps into
uniform C-tensor spaces.  The Z map is shared by every constituent; this is essential, because
one cannot apply a different linear map to the same source variable in different summands.  The
main theorem constructs one global legwise linear map and proves that the selected partition
restricts to the corresponding finite C-tensor realization.
-/

namespace AlgebraicComplexity

open Tensor
open scoped DirectSum

universe u v w

namespace CTensor

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w}
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {X Y Z : Type v}
variable [AddCommMonoid X] [Module K X]
variable [AddCommMonoid Y] [Module K Y]
variable [AddCommMonoid Z] [Module K Z]

/-- Source address with independently indexed X and Y labels and one definitionally shared Z
label. -/
def fiberAddress {h : ℕ}
    (xLabel : Fin h → A .X) (yLabel : Fin h → A .Y) (zLabel : A .Z)
    (i : Fin h) : BlockAddress A :=
  ofLegs (xLabel i) (yLabel i) zLabel

/-- The X coordinate of a fiber address is its recorded X label. -/
@[simp] theorem fiberAddress_X {h : ℕ}
    (xLabel : Fin h → A .X) (yLabel : Fin h → A .Y) (zLabel : A .Z)
    (i : Fin h) : fiberAddress xLabel yLabel zLabel i .X = xLabel i := rfl

/-- The Y coordinate of a fiber address is its recorded Y label. -/
@[simp] theorem fiberAddress_Y {h : ℕ}
    (xLabel : Fin h → A .X) (yLabel : Fin h → A .Y) (zLabel : A .Z)
    (i : Fin h) : fiberAddress xLabel yLabel zLabel i .Y = yLabel i := rfl

/-- The Z coordinate of every fiber address is the common recorded label. -/
@[simp] theorem fiberAddress_Z {h : ℕ}
    (xLabel : Fin h → A .X) (yLabel : Fin h → A .Y) (zLabel : A .Z)
    (i : Fin h) : fiberAddress xLabel yLabel zLabel i .Z = zLabel := rfl

/-- Injective address embedding induced by injective X labels. -/
def fiberAddressEmbedding {h : ℕ}
    (xLabel : Fin h → A .X) (yLabel : Fin h → A .Y) (zLabel : A .Z)
    (hx : Function.Injective xLabel) : Fin h ↪ BlockAddress A where
  toFun := fiberAddress xLabel yLabel zLabel
  inj' := by
    intro i j hij
    apply hx
    exact congrFun hij .X

/-- The address embedding evaluates to `fiberAddress`. -/
@[simp] theorem fiberAddressEmbedding_apply {h : ℕ}
    (xLabel : Fin h → A .X) (yLabel : Fin h → A .Y) (zLabel : A .Z)
    (hx : Function.Injective xLabel) (i : Fin h) :
    fiberAddressEmbedding xLabel yLabel zLabel hx i =
      fiberAddress xLabel yLabel zLabel i :=
  rfl

variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Certificate that a selected partition fiber can be uniformly retyped as an `h`-constituent
C-tensor.  The X and Y maps may depend on the constituent; the Z map is necessarily common.
-/
structure FiberRetyping
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A)) (h : ℕ) where
  /-- X label of constituent `i`. -/
  xLabel : Fin h → A .X
  /-- Y label of constituent `i`. -/
  yLabel : Fin h → A .Y
  /-- Selected X labels are pairwise distinct. -/
  x_injective : Function.Injective xLabel
  /-- Selected Y labels are pairwise distinct. -/
  y_injective : Function.Injective yLabel
  /-- The single Z block shared throughout the fiber. -/
  zLabel : A .Z
  /-- The selected support is exactly the finite family built from these labels. -/
  selected_eq : selected = Finset.univ.map
    (fiberAddressEmbedding xLabel yLabel zLabel x_injective)
  /-- Constituent-dependent map on its X block. -/
  xMap : ∀ i, V .X (xLabel i) →ₗ[K] X
  /-- Constituent-dependent map on its Y block. -/
  yMap : ∀ i, V .Y (yLabel i) →ₗ[K] Y
  /-- The one map applied to the common Z block. -/
  zMap : V .Z zLabel →ₗ[K] Z

namespace FiberRetyping

/-- The selected source address carrying C-tensor index `i`. -/
abbrev sourceAddress
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h)
    (i : Fin h) : BlockAddress A :=
  fiberAddress C.xLabel C.yLabel C.zLabel i

/-- The legwise map taking source constituent `i` to its uniformly typed C-tensor copy. -/
noncomputable def constituentMap
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h)
    (i : Fin h) : ∀ c,
      V c (C.sourceAddress i c) →ₗ[K] ConstituentSpace X Y Z c := by
  intro c
  cases c with
  | X => exact C.xMap i
  | Y => exact C.yMap i
  | Z => exact C.zMap

/-- Uniformly typed constituent family obtained from the selected source fiber. -/
noncomputable def targetConstituent
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h)
    (i : Fin h) : Tensor3 K (ConstituentSpace X Y Z) :=
  map (C.constituentMap i) (P.constituent (C.sourceAddress i))

/-- Global source-to-C-tensor map.  On X and Y it projects each selected source block and
includes its image into the block indexed by the corresponding `Fin h`; on Z it applies the
single common map and includes into the unique shared target block. -/
noncomputable def realizeMap
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h) : ∀ c,
      PartitionedSpace K V c →ₗ[K]
        PartitionedSpace K (BlockSpace X Y Z h) c := by
  classical
  intro c
  cases c with
  | X =>
      exact ∑ i : Fin h,
        DirectSum.lof K (Fin h) (fun _ ↦ X) i ∘ₗ C.xMap i ∘ₗ
          DirectSum.component K (A .X) (V .X) (C.xLabel i)
  | Y =>
      exact ∑ i : Fin h,
        DirectSum.lof K (Fin h) (fun _ ↦ Y) i ∘ₗ C.yMap i ∘ₗ
          DirectSum.component K (A .Y) (V .Y) (C.yLabel i)
  | Z =>
      exact DirectSum.lof K Unit (fun _ ↦ Z) () ∘ₗ C.zMap ∘ₗ
        DirectSum.component K (A .Z) (V .Z) C.zLabel

/-- The global retyping map acts on one selected block exactly as the corresponding C-tensor
block inclusion followed by the constituent map.

Proof sketch: on X and Y, injectivity makes every summand except index `i` vanish after the
source block inclusion.  On Z there is only one target block, and `address_z` identifies the
source block with the common recorded label. -/
theorem realizeMap_comp_blockInclude
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h)
    (i : Fin h) (c : Leg) :
    C.realizeMap c ∘ₗ blockInclude (K := K) (V := V) (C.sourceAddress i) c =
      blockInclude (K := K) (V := BlockSpace X Y Z h) (address i) c ∘ₗ
        constituentToBlock (K := K) (X := X) (Y := Y) (Z := Z) (address i) c ∘ₗ
          C.constituentMap i c := by
  classical
  cases c with
  | X =>
      change C.realizeMap .X ∘ₗ
          DirectSum.lof K (A .X) (V .X) (C.xLabel i) =
        DirectSum.lof K (Fin h) (fun _ ↦ X) i ∘ₗ C.xMap i
      ext x
      simp only [realizeMap, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have hlabel : C.xLabel i ≠ C.xLabel j := by
          intro hij
          exact hji (C.x_injective hij.symm)
        simp [DirectSum.component.of, hlabel]
      · simp
  | Y =>
      change C.realizeMap .Y ∘ₗ
          DirectSum.lof K (A .Y) (V .Y) (C.yLabel i) =
        DirectSum.lof K (Fin h) (fun _ ↦ Y) i ∘ₗ C.yMap i
      ext y
      simp only [realizeMap, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have hlabel : C.yLabel i ≠ C.yLabel j := by
          intro hij
          exact hji (C.y_injective hij.symm)
        simp [DirectSum.component.of, hlabel]
      · simp
  | Z =>
      change C.realizeMap .Z ∘ₗ
          DirectSum.lof K (A .Z) (V .Z) C.zLabel =
        DirectSum.lof K Unit (fun _ ↦ Z) () ∘ₗ C.zMap
      ext z
      simp [realizeMap, LinearMap.comp_apply]

/-- Mapping one embedded selected constituent gives the corresponding embedded C-tensor
constituent. -/
theorem map_realizeMap_block
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h)
    (i : Fin h) :
    map C.realizeMap
        (map (blockInclude (K := K) (V := V) (C.sourceAddress i))
          (P.constituent (C.sourceAddress i))) =
      map (blockInclude (K := K) (V := BlockSpace X Y Z h) (address i))
        ((partitioned C.targetConstituent).constituent (address i)) := by
  calc
    map C.realizeMap
        (map (blockInclude (K := K) (V := V) (C.sourceAddress i))
          (P.constituent (C.sourceAddress i))) =
        map (fun c ↦ C.realizeMap c ∘ₗ
          blockInclude (K := K) (V := V) (C.sourceAddress i) c)
          (P.constituent (C.sourceAddress i)) := by
            rw [map_comp]
            rfl
    _ = map (fun c ↦
          blockInclude (K := K) (V := BlockSpace X Y Z h) (address i) c ∘ₗ
            constituentToBlock (K := K) (X := X) (Y := Y) (Z := Z) (address i) c ∘ₗ
              C.constituentMap i c)
          (P.constituent (C.sourceAddress i)) := by
            have hmaps :
                (fun c ↦ C.realizeMap c ∘ₗ
                  blockInclude (K := K) (V := V) (C.sourceAddress i) c) =
                (fun c ↦
                  blockInclude (K := K) (V := BlockSpace X Y Z h) (address i) c ∘ₗ
                    constituentToBlock (K := K) (X := X) (Y := Y) (Z := Z)
                      (address i) c ∘ₗ C.constituentMap i c) := by
              funext c
              exact C.realizeMap_comp_blockInclude i c
            rw [hmaps]
    _ = map (blockInclude (K := K) (V := BlockSpace X Y Z h) (address i))
          ((partitioned C.targetConstituent).constituent (address i)) := by
            unfold CTensor.partitioned targetConstituent
            rw [map_comp, map_comp]
            simp only [LinearMap.comp_apply]
            simp [address]
            rfl

/-- A selected fixed-Z partition fiber restricts to its uniformly retyped C-tensor.

Proof sketch: enumerate the selected source sum through `addressEquiv`, apply
`map_realizeMap_block` termwise, and recognize the defining support sum of
`CTensor.partitioned`. -/
theorem restricts_partitioned
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h) :
    Restricts (P.withSupport selected).realize (partitioned C.targetConstituent).realize := by
  refine ⟨C.realizeMap, ?_⟩
  classical
  unfold PartitionedTensor.realize PartitionedTensor.withSupport realizePartition
  rw [map_sum]
  calc
    (∑ s ∈ selected,
        map C.realizeMap
          (map (blockInclude (K := K) (V := V) s) (P.constituent s))) =
        ∑ s ∈ Finset.univ.map
            (fiberAddressEmbedding C.xLabel C.yLabel C.zLabel C.x_injective),
          map C.realizeMap
            (map (blockInclude (K := K) (V := V) s) (P.constituent s)) := by
      exact congrArg (fun support : Finset (BlockAddress A) ↦
        ∑ s ∈ support,
          map C.realizeMap
            (map (blockInclude (K := K) (V := V) s) (P.constituent s))) C.selected_eq
    _ = ∑ i : Fin h,
          map C.realizeMap
            (map (blockInclude (K := K) (V := V) (C.sourceAddress i))
              (P.constituent (C.sourceAddress i))) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl
    _ = ∑ i : Fin h,
          map (blockInclude (K := K) (V := BlockSpace X Y Z h) (address i))
            ((partitioned C.targetConstituent).constituent (address i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact C.map_realizeMap_block i
    _ = ∑ s ∈ (partitioned C.targetConstituent).support,
          map (blockInclude (K := K) (V := BlockSpace X Y Z h) s)
            ((partitioned C.targetConstituent).constituent s) := by
      unfold CTensor.partitioned CTensor.support
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl

end FiberRetyping

end CTensor

end AlgebraicComplexity
