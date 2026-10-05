/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Partitioned
import Mathlib.LinearAlgebra.Pi

/-!
# Coarsening finite tensor partitions

A coarsening merges several blocks of a finite partition into one larger block.  The larger block
is the direct sum of the source blocks in one fiber of the coarsening map.  This operation does not
change the realized tensor: it only regroups variables.

The file defines the direct-sum space attached to a coarsened block, the canonical equivalence
between the old and new partitioned leg spaces, transported terms and constituents, and the
coarsened `PartitionedTensor`.  Its main theorem says that realizing a partitioned tensor before
or after coarsening gives isomorphic tensors.

The proof follows the finite fibers of the block-label map.  First it checks the canonical
direct-sum equivalence on a single source-block inclusion.  It then transports each embedded
constituent, expands the finite realization sum, and regroups that sum by the fibers of the
coarsening map.

Unlike `PartitionedTensor.reindex`, the maps on block labels need not be injective.  This is the
operation used in the tensor-square Coppersmith--Winograd construction, where a pair of ternary
block degrees is replaced by its sum in `{0,1,2,3,4}`.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Source labels lying over one coarsened block label. -/
abbrev BlockFiber (f : ∀ c, A c → B c) (c : Leg) (b : B c) :=
  {a : A c // f c a = b}

/-- A coarsened block is the direct sum of all source blocks in one map fiber. -/
abbrev CoarsenedBlockSpace (f : ∀ c, A c → B c) (c : Leg) (b : B c) :=
  ⨁ a : BlockFiber f c b, V c a.1

/-- Regroup a dependent family of vectors by the fibers of a finite map. -/
noncomputable def piCoarsenEquiv (f : ∀ c, A c → B c) (c : Leg) :
    (∀ a, V c a) ≃ₗ[K]
      (∀ b, ∀ a : BlockFiber f c b, V c a.1) where
  toFun x _b a := x a.1
  invFun x a := x (f c a) ⟨a, rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext b a
    rcases a with ⟨a, ha⟩
    subst b
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical equivalence between the original partitioned space and the same space grouped by
the fibers of `f`. -/
noncomputable def partitionedSpaceCoarsenEquiv (f : ∀ c, A c → B c) (c : Leg) :
    PartitionedSpace K V c ≃ₗ[K]
      PartitionedSpace K (CoarsenedBlockSpace (V := V) f) c :=
  (DirectSum.linearEquivFunOnFintype K (A c) (V c)).trans
    ((piCoarsenEquiv (K := K) (V := V) f c).trans
      ((LinearEquiv.piCongrRight fun b ↦
        (DirectSum.linearEquivFunOnFintype K
          (BlockFiber f c b) (fun a ↦ V c a.1)).symm).trans
        (DirectSum.linearEquivFunOnFintype K (B c)
          (CoarsenedBlockSpace (V := V) f c)).symm))

/-- The equivalence sends a source block inclusion to the corresponding nested inclusion in its
coarsened fiber. -/
theorem partitionedSpaceCoarsenEquiv_lof (f : ∀ c, A c → B c) (c : Leg)
    (a : A c) (x : V c a) :
    partitionedSpaceCoarsenEquiv (K := K) (V := V) f c
        (DirectSum.lof K (A c) (V c) a x) =
      DirectSum.lof K (B c) (CoarsenedBlockSpace (V := V) f c) (f c a)
        (DirectSum.lof K (BlockFiber f c (f c a))
          (fun a' ↦ V c a'.1) ⟨a, rfl⟩ x) := by
  apply (DirectSum.linearEquivFunOnFintype K (B c)
    (CoarsenedBlockSpace (V := V) f c)).injective
  funext b
  rw [DirectSum.linearEquivFunOnFintype_lof]
  simp only [partitionedSpaceCoarsenEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, LinearEquiv.apply_symm_apply,
    LinearEquiv.piCongrRight_apply, piCoarsenEquiv]
  by_cases hb : b = f c a
  · subst b
    have hsingle :
        (fun a' : BlockFiber f c (f c a) ↦ (Pi.single a x) a'.1) =
          Pi.single (⟨a, rfl⟩ : BlockFiber f c (f c a)) x := by
      funext a'
      by_cases ha : a'.1 = a
      · have ha' : a' = (⟨a, rfl⟩ : BlockFiber f c (f c a)) := Subtype.ext ha
        subst a'
        simp
      · have ha' : a' ≠ (⟨a, rfl⟩ : BlockFiber f c (f c a)) := by
          intro h
          exact ha (congrArg Subtype.val h)
        simp [ha, ha']
    change (DirectSum.linearEquivFunOnFintype K
      (BlockFiber f c (f c a)) (fun a' ↦ V c a'.1)).symm
        (fun a' ↦ (Pi.single a x) a'.1) = _
    rw [hsingle, DirectSum.linearEquivFunOnFintype_symm_single]
    simp
  · have hfiber : ∀ a' : BlockFiber f c b, a'.1 ≠ a := by
      intro a' ha'
      subst a
      exact hb a'.2.symm
    have hz : (fun a' : BlockFiber f c b ↦ (Pi.single a x) a'.1) = 0 := by
      funext a'
      simp [hfiber a']
    change (DirectSum.linearEquivFunOnFintype K
      (BlockFiber f c b) (fun a' ↦ V c a'.1)).symm
        (fun a' ↦ (Pi.single a x) a'.1) = _
    rw [hz]
    simp [hb]

/-- Apply a block-label coarsening to a full three-leg address. -/
def coarsenBlockAddress (f : ∀ c, A c → B c) (address : BlockAddress A) :
    BlockAddress B :=
  fun c ↦ f c (address c)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- Evaluating a coarsened address on one leg applies that leg's block-label map. -/
@[simp] theorem coarsenBlockAddress_apply (f : ∀ c, A c → B c)
    (address : BlockAddress A) (c : Leg) :
    coarsenBlockAddress f address c = f c (address c) :=
  rfl

/-- Include a source block into a specified coarsened block, using the proof that the source label
lies in the required fiber. -/
noncomputable def coarsenedBlockIncludeAt (f : ∀ c, A c → B c)
    (source : BlockAddress A) (target : BlockAddress B)
    (h : coarsenBlockAddress f source = target) :
    ∀ c, V c (source c) →ₗ[K] CoarsenedBlockSpace (V := V) f c (target c) :=
  fun c ↦ DirectSum.lof K (BlockFiber f c (target c)) (fun a ↦ V c a.1)
    ⟨source c, congrFun h c⟩

/-- Canonical inclusion of a source block into its own coarsening fiber. -/
noncomputable def coarsenedBlockInclude (f : ∀ c, A c → B c)
    (source : BlockAddress A) :
    ∀ c, V c (source c) →ₗ[K]
      CoarsenedBlockSpace (V := V) f c (coarsenBlockAddress f source c) :=
  coarsenedBlockIncludeAt (K := K) (V := V) f source (coarsenBlockAddress f source) rfl

/-- Project a specified coarsened fiber back to one of its source blocks. -/
noncomputable def coarsenedBlockComponentAt (f : ∀ c, A c → B c)
    (source : BlockAddress A) (target : BlockAddress B)
    (h : coarsenBlockAddress f source = target) :
    ∀ c, CoarsenedBlockSpace (V := V) f c (target c) →ₗ[K] V c (source c) :=
  fun c ↦ DirectSum.component K (BlockFiber f c (target c))
    (fun a ↦ V c a.1) ⟨source c, congrFun h c⟩

omit [∀ c, Fintype (A c)] [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- Projecting immediately after the corresponding fiber inclusion is the identity. -/
theorem coarsenedBlockComponentAt_comp_includeAt
    (f : ∀ c, A c → B c)
    (source : BlockAddress A) (target : BlockAddress B)
    (h : coarsenBlockAddress f source = target) (c : Leg) :
    coarsenedBlockComponentAt (K := K) (V := V) f source target h c ∘ₗ
        coarsenedBlockIncludeAt (K := K) (V := V) f source target h c =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [coarsenedBlockComponentAt, coarsenedBlockIncludeAt]

omit [∀ c, Fintype (A c)] [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- Tensor-level cancellation of a coarsened fiber inclusion and its component projection. -/
theorem map_coarsenedBlockComponentAt_includeAt
    (f : ∀ c, A c → B c)
    (source : BlockAddress A) (target : BlockAddress B)
    (h : coarsenBlockAddress f source = target)
    (T : Tensor3 K (fun c ↦ V c (source c))) :
    map (coarsenedBlockComponentAt (K := K) (V := V) f source target h)
        (map (coarsenedBlockIncludeAt (K := K) (V := V) f source target h) T) = T := by
  change
    (map (coarsenedBlockComponentAt (K := K) (V := V) f source target h) ∘ₗ
      map (coarsenedBlockIncludeAt (K := K) (V := V) f source target h)) T = T
  rw [← map_comp]
  have hmaps :
      (fun c ↦
        coarsenedBlockComponentAt (K := K) (V := V) f source target h c ∘ₗ
          coarsenedBlockIncludeAt (K := K) (V := V) f source target h c) =
        (fun _ ↦ LinearMap.id) := by
    funext c
    exact coarsenedBlockComponentAt_comp_includeAt f source target h c
  rw [hmaps, map_id]
  rfl

/-- Space-level compatibility of block inclusion with coarsening. -/
theorem partitionedSpaceCoarsenEquiv_comp_blockInclude
    (f : ∀ c, A c → B c) (source : BlockAddress A) (c : Leg) :
    (partitionedSpaceCoarsenEquiv (K := K) (V := V) f c).toLinearMap ∘ₗ
        blockInclude (K := K) (V := V) source c =
      blockInclude (K := K) (V := CoarsenedBlockSpace (V := V) f)
          (coarsenBlockAddress f source) c ∘ₗ
        coarsenedBlockInclude (K := K) (V := V) f source c := by
  apply LinearMap.ext
  intro x
  exact partitionedSpaceCoarsenEquiv_lof f c (source c) x

/-- Tensor-level compatibility of one embedded constituent with coarsening. -/
theorem map_partitionedSpaceCoarsenEquiv_block
    (f : ∀ c, A c → B c) (source : BlockAddress A)
    (T : Tensor3 K (fun c ↦ V c (source c))) :
    map (fun c ↦
        (partitionedSpaceCoarsenEquiv (K := K) (V := V) f c).toLinearMap)
        (map (blockInclude (K := K) (V := V) source) T) =
      map (blockInclude (K := K) (V := CoarsenedBlockSpace (V := V) f)
          (coarsenBlockAddress f source))
        (map (coarsenedBlockInclude (K := K) (V := V) f source) T) := by
  change
    (map (fun c ↦
        (partitionedSpaceCoarsenEquiv (K := K) (V := V) f c).toLinearMap) ∘ₗ
      map (blockInclude (K := K) (V := V) source)) T =
    (map (blockInclude (K := K) (V := CoarsenedBlockSpace (V := V) f)
        (coarsenBlockAddress f source)) ∘ₗ
      map (coarsenedBlockInclude (K := K) (V := V) f source)) T
  rw [← map_comp, ← map_comp]
  congr 1
  congr 1
  funext c
  exact partitionedSpaceCoarsenEquiv_comp_blockInclude f source c

/-- One source constituent transported into a specified coarse block, or zero when its address
does not map to that block. -/
noncomputable def coarsenedTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (source : BlockAddress A) :
    Tensor3 K (fun c ↦ CoarsenedBlockSpace (V := V) f c (target c)) :=
  if h : coarsenBlockAddress f source = target then
    map (coarsenedBlockIncludeAt (K := K) (V := V) f source target h)
      (P.constituent source)
  else 0

omit [∀ c, Fintype (B c)] in
/-- Computation rule for a source address known to lie over the requested coarse address. -/
theorem coarsenedTerm_eq_map_of_eq
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (source : BlockAddress A) (h : coarsenBlockAddress f source = target) :
    coarsenedTerm P f target source =
      map (coarsenedBlockIncludeAt (K := K) (V := V) f source target h)
        (P.constituent source) := by
  simp [coarsenedTerm, h]

omit [∀ c, Fintype (B c)] in
/-- A leg permutation and compatible fine/coarse coordinate changes carry one nonzero
coarsened term to another.

This is the naturality theorem needed when a symmetric partitioned tensor is regrouped by a
coarsening map.  The hypotheses deliberately expose only the two local compatibility facts a
client must prove: `hraw` identifies the fine constituents, and `hinclude` says that this
identification commutes with inclusion into the corresponding coarse direct-sum blocks.

Proof sketch: expand both coarsened terms, commute the source inclusion through the leg
permutation using `PiTensorProduct.map_reindex`, and fuse the two successive leg maps on each
side.  The resulting maps agree by `hinclude`, while their tensor arguments agree by `hraw`. -/
theorem map_permute_coarsenedTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (source target : BlockAddress A)
    (coarseSource coarseTarget : BlockAddress B)
    (hsource : coarsenBlockAddress f source = coarseSource)
    (htarget : coarsenBlockAddress f target = coarseTarget)
    (e : Orientation)
    (rawMap : ∀ c,
      V (e.symm c) (source (e.symm c)) →ₗ[K] V c (target c))
    (coarseEquiv : ∀ c,
      CoarsenedBlockSpace (V := V) f (e.symm c) (coarseSource (e.symm c)) ≃ₗ[K]
        CoarsenedBlockSpace (V := V) f c (coarseTarget c))
    (hraw : map rawMap (Tensor.permute e (P.constituent source)) =
      P.constituent target)
    (hinclude : ∀ c (x : V (e.symm c) (source (e.symm c))),
      coarseEquiv c
          (coarsenedBlockIncludeAt (K := K) (V := V)
            f source coarseSource hsource (e.symm c) x) =
        coarsenedBlockIncludeAt (K := K) (V := V)
          f target coarseTarget htarget c (rawMap c x)) :
    map (fun c ↦ (coarseEquiv c).toLinearMap)
        (Tensor.permute e (coarsenedTerm P f coarseSource source)) =
      coarsenedTerm P f coarseTarget target := by
  rw [coarsenedTerm_eq_map_of_eq P f coarseSource source hsource,
    coarsenedTerm_eq_map_of_eq P f coarseTarget target htarget]
  rw [← PiTensorProduct.map_reindex
    (coarsenedBlockIncludeAt (K := K) (V := V)
      f source coarseSource hsource) e]
  rw [← hraw]
  change
    (map (fun c ↦ (coarseEquiv c).toLinearMap) ∘ₗ
      map (fun c ↦ coarsenedBlockIncludeAt (K := K) (V := V)
        f source coarseSource hsource (e.symm c)))
        (Tensor.permute e (P.constituent source)) =
      (map (coarsenedBlockIncludeAt (K := K) (V := V)
          f target coarseTarget htarget) ∘ₗ map rawMap)
        (Tensor.permute e (P.constituent source))
  rw [← map_comp, ← map_comp]
  have hmaps :
      (fun c ↦ (coarseEquiv c).toLinearMap ∘ₗ
          coarsenedBlockIncludeAt (K := K) (V := V)
            f source coarseSource hsource (e.symm c)) =
        (fun c ↦ coarsenedBlockIncludeAt (K := K) (V := V)
            f target coarseTarget htarget c ∘ₗ rawMap c) := by
    funext c
    apply LinearMap.ext
    exact hinclude c
  rw [hmaps]

/-- Sum all source constituents mapping to one coarsened address. -/
noncomputable def coarsenedConstituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B) :
    Tensor3 K (fun c ↦ CoarsenedBlockSpace (V := V) f c (target c)) :=
  ∑ source ∈ P.support, coarsenedTerm P f target source

omit [∀ c, Fintype (B c)] in
/-- Fiberwise form of a coarsened constituent.  This exposes exactly the source addresses that a
concrete client must analyze. -/
lemma coarsenedConstituent_eq_sum_filter
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B) :
    coarsenedConstituent P f target =
      ∑ source ∈ P.support.filter
          (fun source ↦ coarsenBlockAddress f source = target),
        coarsenedTerm P f target source := by
  classical
  unfold coarsenedConstituent
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro source hsource
  by_cases h : coarsenBlockAddress f source = target <;>
    simp [h, coarsenedTerm]

namespace Restricts

omit [∀ c, Fintype (B c)] in
/-- A nonzero transported term of a coarsened constituent restricts back to its source
constituent by projecting the appropriate direct-sum component on every leg. -/
theorem coarsenedTerm_of_eq
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (source : BlockAddress A) (h : coarsenBlockAddress f source = target) :
    Restricts (coarsenedTerm P f target source) (P.constituent source) := by
  refine ⟨coarsenedBlockComponentAt (K := K) (V := V) f source target h, ?_⟩
  unfold coarsenedTerm
  simp only [dif_pos h]
  exact map_coarsenedBlockComponentAt_includeAt f source target h (P.constituent source)

end Restricts

/-- Merge the block labels of a partitioned tensor along arbitrary finite maps. -/
noncomputable def PartitionedTensor.coarsen
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) :
    PartitionedTensor (K := K) (A := B) (CoarsenedBlockSpace (V := V) f) where
  support := P.support.image (coarsenBlockAddress f)
  constituent := coarsenedConstituent P f

/-- The support of the coarsened tensor is the image of the original support. -/
@[simp] theorem PartitionedTensor.coarsen_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) :
    (P.coarsen f).support = P.support.image (coarsenBlockAddress f) :=
  rfl

/-- A constituent of the coarsened tensor is the sum of the transported source constituents in
its fiber. -/
@[simp] theorem PartitionedTensor.coarsen_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B) :
    (P.coarsen f).constituent target = coarsenedConstituent P f target :=
  rfl

/-- Regrouping blocks does not change the realized tensor, up to the canonical direct-sum
equivalences on its three legs.

Proof sketch: expand both realizations as finite sums of embedded constituents.  The
single-constituent compatibility theorem moves each source embedding through the canonical
coarsening equivalence.  Finally, exchange the two finite sums and regroup source addresses by
their image under `coarsenBlockAddress`. -/
theorem map_partitionedSpaceCoarsenEquiv_realize
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) :
    map (fun c ↦
        (partitionedSpaceCoarsenEquiv (K := K) (V := V) f c).toLinearMap)
        P.realize =
      (P.coarsen f).realize := by
  classical
  let embedded : BlockAddress A →
      Tensor3 K (PartitionedSpace K (CoarsenedBlockSpace (V := V) f)) :=
    fun source ↦
      map (blockInclude (K := K) (V := CoarsenedBlockSpace (V := V) f)
          (coarsenBlockAddress f source))
        (map (coarsenedBlockInclude (K := K) (V := V) f source)
          (P.constituent source))
  have hleft :
      map (fun c ↦
          (partitionedSpaceCoarsenEquiv (K := K) (V := V) f c).toLinearMap)
          P.realize =
        ∑ source ∈ P.support, embedded source := by
    unfold PartitionedTensor.realize realizePartition
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro source hsource
    simpa only [embedded] using
      map_partitionedSpaceCoarsenEquiv_block f source (P.constituent source)
  have hright :
      (P.coarsen f).realize =
        ∑ target ∈ P.support.image (coarsenBlockAddress f),
          ∑ source ∈ P.support with coarsenBlockAddress f source = target,
            embedded source := by
    unfold PartitionedTensor.realize realizePartition PartitionedTensor.coarsen
      coarsenedConstituent coarsenedTerm
    apply Finset.sum_congr rfl
    intro target htarget
    rw [map_sum]
    calc
      (∑ source ∈ P.support,
          map (blockInclude (K := K) (V := CoarsenedBlockSpace (V := V) f)
            target)
            (if h : coarsenBlockAddress f source = target then
              map (coarsenedBlockIncludeAt (K := K) (V := V) f source target h)
                (P.constituent source)
            else 0)) =
        ∑ source ∈ P.support,
          if coarsenBlockAddress f source = target then embedded source else 0 := by
            apply Finset.sum_congr rfl
            intro source hsource
            by_cases h : coarsenBlockAddress f source = target
            · simp only [h, dif_pos, if_pos]
              subst target
              simp only [embedded, coarsenedBlockInclude]
            · simp [h]
      _ = ∑ source ∈ P.support with coarsenBlockAddress f source = target,
          embedded source := by
            rw [Finset.sum_filter]
  rw [hleft, hright]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun source hsource ↦ Finset.mem_image.mpr ⟨source, hsource, rfl⟩)
    embedded).symm

namespace Isomorphic

/-- Relation-level API: coarsening a finite block partition preserves the realized tensor. -/
theorem partitionedCoarsen
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) :
    Isomorphic P.realize (P.coarsen f).realize := by
  refine ⟨partitionedSpaceCoarsenEquiv (K := K) (V := V) f, ?_⟩
  exact map_partitionedSpaceCoarsenEquiv_realize P f

end Isomorphic

end AlgebraicComplexity.Tensor
