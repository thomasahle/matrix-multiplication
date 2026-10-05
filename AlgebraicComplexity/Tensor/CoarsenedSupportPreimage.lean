/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedCoarsening
import AlgebraicComplexity.Tensor.PartitionedExtraction
import AlgebraicComplexity.Tensor.PartitionedCoarseningPower

set_option autoImplicit false

/-!
# Cutting a coarsened tensor down to a set of coarse addresses

`Tensor/LocalizedCoarsenedSelection.lean` transports **one** coarse constituent to its fine fiber
(`coarsen_constituent_to_fineFiberSelect`).  This module does the whole-support form: cutting the
coarsened tensor down to a finite set `S` of coarse addresses is the same as cutting the *fine*
tensor down to the preimage of `S`.

The point is that the preimage cut is a statement about each fine address alone --- its coarse
image lies in `S` --- and, when `S` is a set of addresses rather than a product of leg sets, that
single condition forces all three coarse leg words of a supported fine address to be the legs of
**one** member of `S`.  Uncrossing therefore comes for free from a cut made upstream at the coarse
level, which is exactly what a legwise cut made downstream at the fine level cannot do.

The isomorphism is free: coarsening does not move the realized tensor
(`Isomorphic.partitionedCoarsen`), and the two partitions agree on their common support, so
`PartitionedTensor.realize_eq_of_support_eq` closes the gap.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y z

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The fine addresses whose coarse image lies in `S`. -/
noncomputable def coarseningPreimageSupport
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (S : Finset (BlockAddress B)) : Finset (BlockAddress A) := by
  classical
  exact P.support.filter fun s ↦ coarsenBlockAddress f s ∈ S

omit [∀ c, Fintype (B c)] in
@[simp] theorem mem_coarseningPreimageSupport
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (S : Finset (BlockAddress B)) (s : BlockAddress A) :
    s ∈ coarseningPreimageSupport P f S ↔
      s ∈ P.support ∧ coarsenBlockAddress f s ∈ S := by
  classical
  simp [coarseningPreimageSupport]

/-- Coarsening the preimage cut gives back the coarse cut, on the nose. -/
theorem coarsen_withSupport_preimage_realize_eq
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (S : Finset (BlockAddress B)) (hS : S ⊆ (P.coarsen f).support) :
    ((P.withSupport (coarseningPreimageSupport P f S)).coarsen f).realize =
      ((P.coarsen f).withSupport S).realize := by
  classical
  have hsupport :
      ((P.withSupport (coarseningPreimageSupport P f S)).coarsen f).support = S := by
    ext t
    rw [PartitionedTensor.coarsen_support, PartitionedTensor.withSupport_support,
      Finset.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ((mem_coarseningPreimageSupport P f S s).1 hs).2
    · intro ht
      have ht' := hS ht
      rw [PartitionedTensor.coarsen_support, Finset.mem_image] at ht'
      obtain ⟨s, hs, hst⟩ := ht'
      exact ⟨s, (mem_coarseningPreimageSupport P f S s).2 ⟨hs, hst ▸ ht⟩, hst⟩
  refine PartitionedTensor.realize_eq_of_support_eq _ _ ?_ ?_
  · rw [hsupport, PartitionedTensor.withSupport_support]
  · intro t ht
    rw [hsupport] at ht
    rw [PartitionedTensor.coarsen_constituent, PartitionedTensor.withSupport_constituent,
      PartitionedTensor.coarsen_constituent,
      coarsenedConstituent_eq_sum_filter, coarsenedConstituent_eq_sum_filter,
      PartitionedTensor.withSupport_support]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext s
    rw [Finset.mem_filter, Finset.mem_filter, mem_coarseningPreimageSupport]
    constructor
    · rintro ⟨⟨hs, _⟩, hst⟩
      exact ⟨hs, hst⟩
    · rintro ⟨hs, hst⟩
      exact ⟨⟨hs, hst ▸ ht⟩, hst⟩

namespace Isomorphic

/-- **The coarse cut is the fine preimage cut.**

Restricting a coarsened tensor to a finite set `S` of coarse addresses realizes the same tensor as
restricting the fine tensor to the fine addresses whose coarse image lies in `S`. -/
theorem coarsen_withSupport_preimage
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (S : Finset (BlockAddress B)) (hS : S ⊆ (P.coarsen f).support) :
    Isomorphic ((P.coarsen f).withSupport S).realize
      (P.withSupport (coarseningPreimageSupport P f S)).realize :=
  (Isomorphic.of_eq (coarsen_withSupport_preimage_realize_eq P f S hS).symm).trans
    (Isomorphic.partitionedCoarsen
      (P.withSupport (coarseningPreimageSupport P f S)) f).symm

end Isomorphic

namespace Restricts

/-- The restriction corollary: the coarse cut reaches the fine preimage cut. -/
theorem coarsen_withSupport_to_preimage
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c)
    (S : Finset (BlockAddress B)) (hS : S ⊆ (P.coarsen f).support) :
    Restricts ((P.coarsen f).withSupport S).realize
      (P.withSupport (coarseningPreimageSupport P f S)).realize :=
  (Isomorphic.coarsen_withSupport_preimage P f S hS).restricts

end Restricts

/-! ## Crossing the power/coarsening reindex seam -/

section ReindexSeam

variable {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
variable {V' : ∀ c, C c → Type y} {W' : ∀ c, C c → Type z}
variable [∀ c a, AddCommMonoid (V' c a)] [∀ c a, Module K (V' c a)]
variable [∀ c a, AddCommMonoid (W' c a)] [∀ c a, Module K (W' c a)]

/-- Relabelling by the identity commutes with cutting the support. -/
theorem withSupport_reindex_refl
    (P : PartitionedTensor (K := K) (A := C) V') (S : Finset (BlockAddress C))
    (be : ∀ c a, V' c ((Equiv.refl (C c)).symm a) ≃ₗ[K] W' c a) :
    (P.withSupport S).reindex (fun c ↦ Equiv.refl (C c)) be =
      (P.reindex (fun c ↦ Equiv.refl (C c)) be).withSupport
        (S.map (blockAddressCongr (fun c ↦ Equiv.refl (C c))).toEmbedding) := rfl

omit [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)] in
@[simp] theorem map_blockAddressCongr_refl (S : Finset (BlockAddress C)) :
    S.map (blockAddressCongr (fun c ↦ Equiv.refl (C c))).toEmbedding = S := by
  ext s
  rw [Finset.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    exact ⟨s, hs, rfl⟩

end ReindexSeam

/-- Transport a support cut across an identity relabelling, given the relabelling equation. -/
theorem Isomorphic.withSupport_of_reindex_refl
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    {V' : ∀ c, C c → Type y} {W' : ∀ c, C c → Type z}
    [∀ c a, AddCommMonoid (V' c a)] [∀ c a, Module K (V' c a)]
    [∀ c a, AddCommMonoid (W' c a)] [∀ c a, Module K (W' c a)]
    (Q : PartitionedTensor (K := K) (A := C) V')
    {be : ∀ c b, V' c ((Equiv.refl (C c)).symm b) ≃ₗ[K] W' c b}
    {R : PartitionedTensor (K := K) (A := C) W'}
    (hR : Q.reindex (fun c ↦ Equiv.refl (C c)) be = R)
    (S : Finset (BlockAddress C)) :
    Isomorphic (Q.withSupport S).realize (R.withSupport S).realize := by
  have h := Isomorphic.partitionedReindex (Q.withSupport S)
    (fun c ↦ Equiv.refl (C c)) be
  rwa [withSupport_reindex_refl, map_blockAddressCongr_refl, hR] at h

/-- **The coarse cut of a quotient-first power reaches the fine preimage cut.**

The composite of `Restricts.coarsen_withSupport_to_preimage` with the power/coarsening reindex
`positivePower_coarsen_reindex`.  This is the form the plain route needs: the count lane's hash
delivers a cut of `P.coarsenedPositivePower f n`, and the leaf lane needs it on the fine power. -/
theorem Restricts.coarsenedPositivePower_withSupport_to_preimage
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) (n : ℕ)
    (S : Finset (BlockAddress fun c ↦ PositiveWord (B c) n))
    (hS : S ⊆ ((P.positivePower n).coarsen
      (fun c ↦ positiveWordMap (f c) n)).support) :
    Restricts ((P.coarsenedPositivePower f n).withSupport S).realize
      ((P.positivePower n).withSupport
        (coarseningPreimageSupport (P.positivePower n)
          (fun c ↦ positiveWordMap (f c) n) S)).realize :=
  (Isomorphic.withSupport_of_reindex_refl _
    (P.positivePower_coarsen_reindex f n) S).restricts.trans
    (Restricts.coarsen_withSupport_to_preimage (P.positivePower n)
      (fun c ↦ positiveWordMap (f c) n) S hS)

end AlgebraicComplexity.Tensor
