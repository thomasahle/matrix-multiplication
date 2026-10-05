/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PermutedCoherentOneSliceWord
import AlgebraicComplexity.MatrixMultiplication.SharedOneSliceFiber
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientationRetyping

/-!
# Fusing a shared fibre that sits on an arbitrary leg

`CTensor.SharedOneSliceFiberData` fuses coherent constituentwise one-slice certificates into a
single matrix-multiplication tensor, but it is hard-wired — as the committed `FiberRetyping` is —
to a fibre shared on **`Z`**, with injective labels on `X` and `Y`.  A laser certificate meets zero
blocks in all three orientations, so the same fusion is needed with the shared block on `X` and on
`Y`.

This module supplies that transport once, generically in the orientation `e`, by pairing the two
committed halves:

* `Tensor.PartitionedTensor.permute` (`Tensor/PartitionedPermutation.lean`) puts the shared block
  of `P` at leg `e.symm .Z` onto `Z`, and `CTensor.FiberRetyping.ofSharedSupportPermutedAmbient`
  (the items-1--2 tranche) already moves the two support hypotheses across that permutation;
* `OneSliceRestriction.precompose` (the item-3 tranche) transports one certificate along a legwise
  map, and `precompose_legMap` keeps the transported maps readable — which is exactly what the
  coherence field of `SharedOneSliceFiberData` reads.

## What has to be checked, and what does not

A constituent of `P.permute e` is not literally the rotated source constituent: it is the rotated
source constituent *retyped* along `Tensor.permuteBlockSpaceCast`, the dependent cast that
identifies the block sitting at the inverse-transported address with the block at the target
address.  `ofPermuteConstituent` transports a rotated certificate across that retyping, and
`ofPermuteConstituent_legMap` shows the cost is a composition with one linear equivalence.

On the shared leg that composition is invisible: `comp_cast_symm_heq` says composing with the
inverse of a dependent cast is the transport the `HEq` already expresses.  So a family that is
coherent in the rotated frame stays coherent after retyping, with **no new coherence proof** —
which is what makes this a mechanical assembly step rather than a second fusion theorem.

## The conclusion stays in the permuted frame

As in `ZeroCoordinateOrientationRetyping`, the restriction proved below is a restriction of
`Tensor.permute e P.realize`, and the orientation is named in the statement.  Rotating back is only
an isomorphism and belongs with the leaf packaging (`ZeroCoordinateMerge.mergeX / mergeY / mergeZ`),
so a client cannot pair a rotated tensor with an unrotated leaf dimension by accident.

No Coppersmith--Winograd constant, no certificate datum and no asymptotics occur here.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace OneSliceRestriction

/-! ## Transport across a legwise retyping -/

section MapEquiv

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
variable {S : Tensor3 K W} {d : ℕ}

/-- **Transport along a legwise equivalence.**  Retyping a certified tensor leaves it certified,
with the maps composed with the inverse retyping.  This is `precompose` at an equivalence, where no
hypothesis about the source is needed. -/
noncomputable def ofMapEquiv (C : OneSliceRestriction S d) (g : ∀ c, W c ≃ₗ[K] V c) :
    OneSliceRestriction (Tensor.map (fun c ↦ (g c).toLinearMap) S) d :=
  C.precompose (fun c ↦ (g c).symm.toLinearMap) (by
    have hcomp := Tensor.map_comp (K := K) (V := W) (W := V) (U := W)
      (fun c ↦ (g c).toLinearMap) (fun c ↦ (g c).symm.toLinearMap)
    have hid : (fun c ↦ (g c).symm.toLinearMap ∘ₗ (g c).toLinearMap) =
        fun c ↦ LinearMap.id (R := K) (M := W c) := by
      funext c
      ext x
      simp
    rw [hid, Tensor.map_id] at hcomp
    exact (LinearMap.congr_fun hcomp S).symm)

@[simp] theorem ofMapEquiv_legMap (C : OneSliceRestriction S d) (g : ∀ c, W c ≃ₗ[K] V c)
    (c : Leg) :
    (C.ofMapEquiv g).legMap c = C.legMap c ∘ₗ (g c).symm.toLinearMap :=
  rfl

end MapEquiv

/-! ## The dependent-cast toolkit -/

section Cast

variable {K : Type u} [CommSemiring K]

/-- Composing a map with the inverse of a dependent cast of its domain is exactly the transport
that a `HEq` between the two typings expresses. -/
theorem comp_cast_symm_heq {ι : Type*} {M : ι → Type v}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)]
    {N : Type w} [AddCommMonoid N] [Module K N]
    {a b : ι} (h : a = b) (f : M a →ₗ[K] N) :
    HEq (f ∘ₗ (LinearEquiv.cast (R := K) h).symm.toLinearMap) f := by
  subst h
  refine heq_of_eq ?_
  ext x
  rfl

/-- Composing on the left with one fixed map preserves heterogeneous equality of two maps whose
domains are the same dependent family at equal indices. -/
theorem comp_left_heq {ι : Type*} {M : ι → Type v}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)]
    {N : Type w} [AddCommMonoid N] [Module K N]
    {P : Type w} [AddCommMonoid P] [Module K P]
    (g : N →ₗ[K] P) {a b : ι} (h : a = b)
    {f : M a →ₗ[K] N} {f' : M b →ₗ[K] N} (hf : HEq f f') :
    HEq (g ∘ₗ f) (g ∘ₗ f') := by
  subst h
  rw [eq_of_heq hf]

end Cast

/-! ## Certificates for the constituents of a permuted partition -/

section Permuted

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **A rotated source certificate certifies the corresponding constituent of the permuted
partition.**  The two differ by the dependent retyping `permuteBlockSpaceCast`, which
`ofMapEquiv` absorbs. -/
noncomputable def ofPermuteConstituent
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (address : BlockAddress (PermutedBlockIndex e A)) {d : ℕ}
    (C : OneSliceRestriction
      (Tensor.permute e (P.constituent ((permuteBlockAddress e).symm address))) d) :
    OneSliceRestriction ((P.permute e).constituent address) d :=
  (C.ofMapEquiv fun c ↦ permuteBlockSpaceCast (K := K) (V := V) e address c).congrTensor
    (P.permute_constituent e address).symm

@[simp] theorem ofPermuteConstituent_legMap
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (address : BlockAddress (PermutedBlockIndex e A)) {d : ℕ}
    (C : OneSliceRestriction
      (Tensor.permute e (P.constituent ((permuteBlockAddress e).symm address))) d)
    (c : Leg) :
    (ofPermuteConstituent P e address C).legMap c =
      C.legMap c ∘ₗ (permuteBlockSpaceCast (K := K) (V := V) e address c).symm.toLinearMap := by
  rw [ofPermuteConstituent, congrTensor_legMap, ofMapEquiv_legMap]

end Permuted

end OneSliceRestriction

namespace CTensor

open OneSliceRestriction

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Per-constituent one-slice certificates **in the frame that rotates the shared leg onto `Z`**,
with one coherent map on the shared block.

This is `SharedOneSliceFiberData` with the shared block at leg `e.symm .Z` instead of at `.Z`; the
certificates are certificates of the rotated constituents, exactly as the rotated word recursion of
`OneSliceRestrictionTransport` and `PermutedCoherentOneSliceWord` produces them. -/
structure PermutedSharedOneSliceFiberData
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (zLabel : A (e.symm .Z)) (d : ℕ) where
  /-- Explicit restriction of every rotated supported constituent. -/
  certificate : ∀ address : P.support,
    OneSliceRestriction (Tensor.permute e (P.constituent address.1)) d
  /-- The one map applied to the block shared by the whole fibre. -/
  zMap : V (e.symm .Z) zLabel →ₗ[K] MMSpace K 1 d 1 .Z
  /-- Every constituent certificate uses `zMap` on the shared leg, up to the transport forced by
  the equality between its own shared label and `zLabel`. -/
  z_coherent : ∀ address : P.support, HEq ((certificate address).legMap .Z) zMap

namespace PermutedSharedOneSliceFiberData

variable {P : PartitionedTensor (K := K) (A := A) V} {e : Orientation}
variable {zLabel : A (e.symm .Z)} {d : ℕ}

/-- The source address of one address of a permuted support. -/
def sourceAddress (address : (P.permute e).support) : P.support :=
  ⟨(permuteBlockAddress e).symm address.1, by
    obtain ⟨source, hsource, hmapped⟩ := Finset.mem_map.mp address.2
    have hback : (permuteBlockAddress e).symm address.1 = source := by
      rw [← hmapped]
      simp
    rw [hback]
    exact hsource⟩

@[simp] theorem sourceAddress_coe (address : (P.permute e).support) :
    (sourceAddress address).1 = (permuteBlockAddress e).symm address.1 := rfl

/-- **The rotated coherent family, read in the canonical shared-`Z` frame.**  Every hypothesis of
the committed fusion is discharged by the committed permutation transport; no coherence is
re-proved. -/
noncomputable def toSharedOneSliceFiberData
    (D : PermutedSharedOneSliceFiberData P e zLabel d)
    (hz : ∀ address ∈ P.support, address (e.symm .Z) = zLabel) :
    SharedOneSliceFiberData (P.permute e) (P.permute e).support zLabel d where
  certificate := fun address ↦
    OneSliceRestriction.ofPermuteConstituent P e address.1 (D.certificate (sourceAddress address))
  zMap := (CTensor.oneSliceConstituentEquiv K d .Z).symm.toLinearMap ∘ₗ D.zMap
  z_coherent := by
    intro address
    have hlabel : address.1 .Z = zLabel :=
      FiberRetyping.forall_map_permuteBlockAddress_eq e P.support .Z zLabel hz address.1 address.2
    have hlegMap := OneSliceRestriction.ofPermuteConstituent_legMap P e address.1
      (D.certificate (sourceAddress address)) .Z
    have hshared : HEq
        ((OneSliceRestriction.ofPermuteConstituent P e address.1
          (D.certificate (sourceAddress address))).legMap .Z) D.zMap :=
      HEq.trans (heq_of_eq hlegMap)
        (HEq.trans
          (OneSliceRestriction.comp_cast_symm_heq
            (permuteBlockAddress_symm_apply_apply e address.1 .Z) _)
          (D.z_coherent (sourceAddress address)))
    exact OneSliceRestriction.comp_left_heq _ hlabel hshared

/-- **Exact fusion of a fibre shared on an arbitrary leg.**  The whole rotated partitioned tensor
restricts to `⟨1, |support| · d, 1⟩`, with no representative selection and no loss factor.

At `e = 1` this is the committed
`SharedOneSliceFiberData.restricts_oneSliceMatrixMultiplication_of_support`. -/
theorem restricts_permute_oneSliceMatrixMultiplication
    (D : PermutedSharedOneSliceFiberData P e zLabel d)
    (hx : Set.InjOn (fun address ↦ address (e.symm .X)) (P.support : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address (e.symm .Y)) (P.support : Set (BlockAddress A)))
    (hz : ∀ address ∈ P.support, address (e.symm .Z) = zLabel) :
    Restricts (Tensor.permute e P.realize)
      (matrixMultiplication (K := K) 1 (P.support.card * d) 1) := by
  have hfused := (D.toSharedOneSliceFiberData hz).restricts_oneSliceMatrixMultiplication_of_support
    (FiberRetyping.injOn_map_permuteBlockAddress e P.support .X hx)
    (FiberRetyping.injOn_map_permuteBlockAddress e P.support .Y hy)
    (FiberRetyping.forall_map_permuteBlockAddress_eq e P.support .Z zLabel hz)
  have hcard : (P.permute e).support.card = P.support.card := Finset.card_map _
  rw [PartitionedTensor.permute_realize, hcard] at hfused
  exact hfused

end PermutedSharedOneSliceFiberData

end CTensor

end AlgebraicComplexity
