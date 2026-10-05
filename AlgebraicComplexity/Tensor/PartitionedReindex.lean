/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Partitioned

/-!
# Reindexing partitioned tensors

A partition is unchanged, up to legwise linear isomorphism, when its block labels are renamed and
the corresponding block spaces are replaced by linearly equivalent spaces.  This module packages
that elementary operation once, including its action on supported constituents and realizations.

The construction is deliberately independent of tensor powers.  Recursive laser clients use it
to replace a pair of regional block words by their concatenation, while other clients can use the
same API for coordinate encodings or canonical changes of block representation.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x y z t

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v} {W : ∀ c, B c → Type y}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- Rename one block label independently on every tensor leg. -/
def blockAddressCongr (e : ∀ c, A c ≃ B c) : BlockAddress A ≃ BlockAddress B :=
  Equiv.piCongrRight e

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem blockAddressCongr_apply (e : ∀ c, A c ≃ B c)
    (address : BlockAddress A) (c : Leg) :
    blockAddressCongr e address c = e c (address c) :=
  rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem blockAddressCongr_symm_apply (e : ∀ c, A c ≃ B c)
    (address : BlockAddress B) (c : Leg) :
    (blockAddressCongr e).symm address c = (e c).symm (address c) :=
  rfl

/-- Rename direct-sum block labels and apply the supplied equivalence inside each renamed block. -/
noncomputable def partitionedSpaceReindexEquiv (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b) :
    ∀ c, PartitionedSpace K V c ≃ₗ[K] PartitionedSpace K W c :=
  fun c ↦
    (DirectSum.lequivCongrLeft K (e c)).trans
      (DirectSum.congrLinearEquiv (f c))

/-- Pull a dependent function on renamed blocks back to the source labels, applying the inverse
local block equivalence at every coordinate. -/
noncomputable def piUnreindexLinearMap
    {I : Type w} {J : Type x} {M : I → Type v} {N : J → Type y}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)]
    [∀ j, AddCommMonoid (N j)] [∀ j, Module K (N j)]
    (e : I ≃ J) (g : ∀ i, M i ≃ₗ[K] N (e i)) :
    (∀ j, N j) →ₗ[K] (∀ i, M i) :=
  LinearMap.pi fun a ↦
    (g a).symm.toLinearMap ∘ₗ LinearMap.proj (e a)

/-- Linear map from a renamed partitioned space back to its source-labelled direct sum.

This source-indexed formulation avoids any chosen inverse inside dependent block types.  It is
the natural map for proving that a selected family of renamed blocks is a restriction of its
ambient partition. -/
noncomputable def partitionedSpaceUnreindexLinearMap
    (e : ∀ c, A c ≃ B c)
    (g : ∀ c a, V c a ≃ₗ[K] W c (e c a)) :
    ∀ c, PartitionedSpace K W c →ₗ[K] PartitionedSpace K V c :=
  fun c ↦
    (DirectSum.linearEquivFunOnFintype K (A c) (V c)).symm.toLinearMap ∘ₗ
      (piUnreindexLinearMap (K := K) (M := V c) (N := W c) (e c) (g c) ∘ₗ
        (DirectSum.linearEquivFunOnFintype K (B c) (W c)).toLinearMap)

/-- Pulling back an included renamed block returns the corresponding source block after applying
the inverse local equivalence. -/
theorem partitionedSpaceUnreindexLinearMap_comp_blockInclude
    (e : ∀ c, A c ≃ B c)
    (g : ∀ c a, V c a ≃ₗ[K] W c (e c a))
    (address : BlockAddress A) (c : Leg) :
    partitionedSpaceUnreindexLinearMap e g c ∘ₗ
        blockInclude (K := K) (V := W) (blockAddressCongr e address) c =
      blockInclude (K := K) (V := V) address c ∘ₗ
        (g c (address c)).symm.toLinearMap := by
  change partitionedSpaceUnreindexLinearMap e g c ∘ₗ
        blockInclude (K := K) (V := W) (fun c ↦ e c (address c)) c =
      blockInclude (K := K) (V := V) address c ∘ₗ
        (g c (address c)).symm.toLinearMap
  apply LinearMap.ext
  intro value
  change
    (DirectSum.linearEquivFunOnFintype K (A c) (V c)).symm
        (piUnreindexLinearMap (K := K) (M := V c) (N := W c) (e c) (g c)
          ((DirectSum.linearEquivFunOnFintype K (B c) (W c))
            (DirectSum.lof K (B c) (W c) (e c (address c)) value))) =
      DirectSum.lof K (A c) (V c) (address c) ((g c (address c)).symm value)
  rw [DirectSum.linearEquivFunOnFintype_lof]
  have hfunction :
      piUnreindexLinearMap (K := K) (M := V c) (N := W c) (e c) (g c)
          (Pi.single (e c (address c)) value) =
        Pi.single (address c) ((g c (address c)).symm value) := by
    funext source
    by_cases hsource : source = address c
    · subst source
      simp [piUnreindexLinearMap]
    · have hrenamed : e c source ≠ e c (address c) := fun h ↦
        hsource ((e c).injective h)
      simp [piUnreindexLinearMap, hsource, hrenamed]
  rw [hfunction, DirectSum.linearEquivFunOnFintype_symm_single]

/-- Tensor-level cancellation law for one renamed block.  After a constituent is transported
forward by the local block equivalences and included at the renamed address, pulling the ambient
partition back recovers the original embedded constituent. -/
theorem map_partitionedSpaceUnreindex_block
    (e : ∀ c, A c ≃ B c)
    (g : ∀ c a, V c a ≃ₗ[K] W c (e c a))
    (address : BlockAddress A)
    (T : Tensor3 K (fun c ↦ V c (address c))) :
    map (partitionedSpaceUnreindexLinearMap e g)
        (map (blockInclude (K := K) (V := W) (blockAddressCongr e address))
          (map (fun c ↦ (g c (address c)).toLinearMap) T)) =
      map (blockInclude (K := K) (V := V) address) T := by
  change map (partitionedSpaceUnreindexLinearMap e g)
      (map (blockInclude (K := K) (V := W) (fun c ↦ e c (address c)))
        (map (fun c ↦ (g c (address c)).toLinearMap) T)) =
    map (blockInclude (K := K) (V := V) address) T
  change
    (map (partitionedSpaceUnreindexLinearMap e g) ∘ₗ
        map (blockInclude (K := K) (V := W) (fun c ↦ e c (address c))))
      (map (fun c ↦ (g c (address c)).toLinearMap) T) = _
  rw [← map_comp]
  have hcomponents :
      (fun c ↦ partitionedSpaceUnreindexLinearMap e g c ∘ₗ
        blockInclude (K := K) (V := W) (fun c ↦ e c (address c)) c) =
      (fun c ↦ blockInclude (K := K) (V := V) address c ∘ₗ
        (g c (address c)).symm.toLinearMap) := by
    funext c
    exact partitionedSpaceUnreindexLinearMap_comp_blockInclude e g address c
  rw [hcomponents, map_comp]
  change map (blockInclude (K := K) (V := V) address)
      ((PiTensorProduct.congr (fun c ↦ g c (address c))).symm
        ((PiTensorProduct.congr (fun c ↦ g c (address c))) T)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Reindex a partitioned tensor, transporting every constituent through the corresponding
block-space equivalences. -/
noncomputable def PartitionedTensor.reindex
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b) :
    PartitionedTensor (K := K) (A := B) W where
  support := P.support.map (blockAddressCongr e).toEmbedding
  constituent address :=
    map (fun c ↦ (f c (address c)).toLinearMap)
      (P.constituent ((blockAddressCongr e).symm address))

@[simp] theorem PartitionedTensor.reindex_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b) :
    (P.reindex e f).support =
      P.support.map (blockAddressCongr e).toEmbedding :=
  rfl

@[simp] theorem PartitionedTensor.reindex_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (address : BlockAddress B) :
    (P.reindex e f).constituent address =
      map (fun c ↦ (f c (address c)).toLinearMap)
      (P.constituent ((blockAddressCongr e).symm address)) :=
  rfl

/-- Two successive block reindexings are the single reindexing by the composite label and block
equivalences.  This is the coherence law needed to compose structure-preserving relabelings. -/
theorem PartitionedTensor.reindex_trans
    {C : Leg → Type z}
    [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    {X : ∀ c, C c → Type t}
    [∀ c d, AddCommMonoid (X c d)] [∀ c d, Module K (X c d)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (g : ∀ c, B c ≃ C c)
    (h : ∀ c d, W c ((g c).symm d) ≃ₗ[K] X c d) :
    (P.reindex e f).reindex g h =
      P.reindex (fun c ↦ (e c).trans (g c))
        (fun c d ↦ (f c ((g c).symm d)).trans (h c d)) := by
  classical
  apply PartitionedTensor.ext
  · simp only [PartitionedTensor.reindex_support, Finset.map_map]
    congr 1
  · funext address
    change
      map (fun c ↦ (h c (address c)).toLinearMap)
          (map (fun c ↦ (f c ((g c).symm (address c))).toLinearMap)
            (P.constituent
              (fun c ↦ (e c).symm ((g c).symm (address c))))) =
        map (fun c ↦ (h c (address c)).toLinearMap ∘ₗ
            (f c ((g c).symm (address c))).toLinearMap)
          (P.constituent
            (fun c ↦ (e c).symm ((g c).symm (address c))))
    rw [map_comp]
    rfl

/-- Reindexing by identity label and block equivalences leaves a partitioned tensor unchanged. -/
theorem PartitionedTensor.reindex_refl
    (P : PartitionedTensor (K := K) (A := A) V) :
    P.reindex (fun _ ↦ Equiv.refl _)
        (fun c a ↦ LinearEquiv.refl K (V c a)) = P := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.reindex, blockAddressCongr]
  · funext address
    change map (fun c ↦ LinearMap.id) (P.constituent address) =
      P.constituent address
    exact LinearMap.congr_fun map_id _

/-- Transport a finite set of block labels through a reindexing equivalence. -/
def relabelParts (e : ∀ c, A c ≃ B c) (parts : ∀ c, Finset (A c)) :
    ∀ c, Finset (B c) :=
  fun c ↦ (parts c).image (e c)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] [∀ c, Fintype (B c)] in
@[simp] theorem mem_relabelParts
    (e : ∀ c, A c ≃ B c) (parts : ∀ c, Finset (A c))
    (c : Leg) (b : B c) :
    b ∈ relabelParts e parts c ↔ (e c).symm b ∈ parts c := by
  classical
  change b ∈ (parts c).image (e c) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hb
    exact ⟨(e c).symm b, hb, (e c).apply_symm_apply b⟩

/-- Reindexing commutes with variable zeroing, with the selected block sets transported along
the same legwise equivalences. -/
theorem PartitionedTensor.reindex_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    (P.select keep).reindex e f =
      (P.reindex e f).select (fun c b ↦ keep c ((e c).symm b)) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.select, PartitionedTensor.reindex]
  · rfl

omit [∀ c, Fintype (A c)] [∀ c, Fintype (B c)] in
/-- On a single block, ambient reindexing is exactly block inclusion after the local
block-space equivalence. -/
theorem partitionedSpaceReindexEquiv_comp_blockInclude
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (address : BlockAddress B) (c : Leg) :
    (partitionedSpaceReindexEquiv e f c).toLinearMap ∘ₗ
        blockInclude (K := K) (V := V) ((blockAddressCongr e).symm address) c =
      blockInclude (K := K) (V := W) address c ∘ₗ
        (f c (address c)).toLinearMap := by
  change (partitionedSpaceReindexEquiv e f c).toLinearMap ∘ₗ
        blockInclude (K := K) (V := V)
          (fun c ↦ (e c).symm (address c)) c =
      blockInclude (K := K) (V := W) address c ∘ₗ
        (f c (address c)).toLinearMap
  apply LinearMap.ext
  intro value
  change
    (DirectSum.congrLinearEquiv (f c))
        ((DirectSum.lequivCongrLeft K (e c))
          (DirectSum.lof K (A c) (V c) ((e c).symm (address c)) value)) =
      DirectSum.lof K (B c) (W c) (address c) (f c (address c) value)
  rw [DirectSum.lequivCongrLeft_lof K rfl value value rfl]
  change DirectSum.lmap (fun b ↦ (f c b).toLinearMap)
      (DirectSum.lof K (B c) (fun b ↦ V c ((e c).symm b))
        (address c) value) = _
  rw [DirectSum.lmap_lof]
  rfl

/-- Tensor-level form of `partitionedSpaceReindexEquiv_comp_blockInclude`. -/
theorem map_partitionedSpaceReindexEquiv_block
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (address : BlockAddress B) :
    map (fun c ↦ (partitionedSpaceReindexEquiv e f c).toLinearMap)
        (map (blockInclude (K := K) (V := V) ((blockAddressCongr e).symm address))
          (P.constituent ((blockAddressCongr e).symm address))) =
      map (blockInclude (K := K) (V := W) address)
        ((P.reindex e f).constituent address) := by
  rw [PartitionedTensor.reindex_constituent]
  change
    map (fun c ↦ (partitionedSpaceReindexEquiv e f c).toLinearMap)
        (map (blockInclude (K := K) (V := V)
          (fun c ↦ (e c).symm (address c)))
          (P.constituent (fun c ↦ (e c).symm (address c)))) =
      map (blockInclude (K := K) (V := W) address)
        (map (fun c ↦ (f c (address c)).toLinearMap)
          (P.constituent (fun c ↦ (e c).symm (address c))))
  let source := P.constituent (fun c ↦ (e c).symm (address c))
  have hmaps :
      map (fun c ↦ (partitionedSpaceReindexEquiv e f c).toLinearMap) ∘ₗ
          map (blockInclude (K := K) (V := V)
            (fun c ↦ (e c).symm (address c))) =
        map (blockInclude (K := K) (V := W) address) ∘ₗ
          map (fun c ↦ (f c (address c)).toLinearMap) := by
    rw [← map_comp, ← map_comp]
    congr 1
    funext c
    exact partitionedSpaceReindexEquiv_comp_blockInclude e f address c
  exact LinearMap.congr_fun hmaps source

/-- Reindexing a partitioned tensor carries its realization to the reindexed realization. -/
theorem map_partitionedSpaceReindexEquiv_realize
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b) :
    map (fun c ↦ (partitionedSpaceReindexEquiv e f c).toLinearMap) P.realize =
      (P.reindex e f).realize := by
  classical
  unfold PartitionedTensor.realize realizePartition
  rw [map_sum]
  unfold PartitionedTensor.reindex
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro address haddress
  have hblock := map_partitionedSpaceReindexEquiv_block (W := W) P e f
    (blockAddressCongr e address)
  have hinverse :
      (blockAddressCongr e).symm (blockAddressCongr e address) = address :=
    (blockAddressCongr e).symm_apply_apply address
  rw [hinverse] at hblock
  exact hblock

namespace Isomorphic

/-- Relation-level API: renaming partition blocks and replacing them with equivalent spaces does
not change the realized tensor. -/
theorem partitionedReindex
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b) :
    Isomorphic P.realize (P.reindex e f).realize := by
  refine ⟨partitionedSpaceReindexEquiv e f, ?_⟩
  exact map_partitionedSpaceReindexEquiv_realize P e f

end Isomorphic

end AlgebraicComplexity.Tensor
