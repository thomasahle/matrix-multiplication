/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedCoarseningInterface
import AlgebraicComplexity.Tensor.PartitionedProduct

/-!
# Coarsening commutes with partitioned positive powers

Tensoring blocks which are themselves finite direct sums canonically distributes into the
direct sum of all tensor products.  This module records that equivalence with its quotient-word
labels, so a type selection performed on `(P.coarsen f).positivePower n` can be transported to
the equivalent selection obtained by coarsening `P.positivePower n` along `positiveWordMap f n`.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

-- The dependent direct-sum families in this file are definitionally equal only after reducing
-- their fiber equivalences.  Permit the elaborator to see through those reducibility barriers.
set_option backward.isDefEq.respectTransparency false

universe u v w x y z t s r

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable {C : Leg → Type y} {D : Leg → Type z}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
variable [∀ c, Fintype (D c)] [∀ c, DecidableEq (D c)]
variable {V : ∀ c, A c → Type (max u v)}
variable {W : ∀ c, C c → Type (max u t)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable [∀ c a, AddCommMonoid (W c a)] [∀ c a, Module K (W c a)]

/-- Apply two coarsening maps to the two labels of a product block. -/
def productCoarseningMap (f : ∀ c, A c → B c) (g : ∀ c, C c → D c) :
    ∀ c, ProductBlockIndex A C c → ProductBlockIndex B D c :=
  fun c q ↦ (f c q.1, g c q.2)

/-- Coarsening a paired address by the product map is componentwise coarsening. -/
@[simp] theorem coarsenBlockAddress_productCoarseningMap
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (left : BlockAddress A) (right : BlockAddress C) :
    coarsenBlockAddress (productCoarseningMap f g)
        (fun c ↦ (left c, right c)) =
      fun c ↦ (coarsenBlockAddress f left c,
        coarsenBlockAddress g right c) :=
  rfl

/-- A fiber of a product map is canonically the product of the two fibers. -/
def productBlockFiberEquiv
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (c : Leg) (target : ProductBlockIndex B D c) :
    BlockFiber f c target.1 × BlockFiber g c target.2 ≃
      BlockFiber (productCoarseningMap f g) c target where
  toFun q := ⟨(q.1.1, q.2.1), by
    ext <;> simp [productCoarseningMap, q.1.2, q.2.2]⟩
  invFun q :=
    (⟨q.1.1, congrArg Prod.fst q.2⟩, ⟨q.1.2, congrArg Prod.snd q.2⟩)
  left_inv q := by rcases q with ⟨⟨a, ha⟩, ⟨d, hd⟩⟩; rfl
  right_inv q := by rcases q with ⟨⟨a, d⟩, h⟩; rfl

/-- Reindex dependent functions along `productBlockFiberEquiv`.  Writing this equivalence
directly avoids casts between the two proposition-valued fiber witnesses. -/
noncomputable def piProductBlockFiberEquiv
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (c : Leg) (target : ProductBlockIndex B D c) :
    (∀ q : BlockFiber f c target.1 × BlockFiber g c target.2,
        TensorProduct K (V c q.1.1) (W c q.2.1)) ≃ₗ[K]
      (∀ q : BlockFiber (productCoarseningMap f g) c target,
        ProductBlockSpace K V W c q.1) where
  toFun value q := value ((productBlockFiberEquiv f g c target).symm q)
  invFun value q := value (productBlockFiberEquiv f g c target q)
  left_inv value := by
    funext q
    rcases q with ⟨⟨a, ha⟩, ⟨d, hd⟩⟩
    rfl
  right_inv value := by
    funext q
    rcases q with ⟨⟨a, d⟩, h⟩
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Blockwise distributivity: the tensor product of two coarsened blocks is the coarsening of
the corresponding product block. -/
noncomputable def coarsenedExternalBlockEquiv
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (c : Leg) (target : ProductBlockIndex B D c) :
    ProductBlockSpace K (CoarsenedBlockSpace (V := V) f)
        (CoarsenedBlockSpace (V := W) g) c target ≃ₗ[K]
      CoarsenedBlockSpace (V := ProductBlockSpace K V W)
        (productCoarseningMap f g) c target :=
  (TensorProduct.directSum K K
      (fun a : BlockFiber f c target.1 ↦ V c a.1)
      (fun d : BlockFiber g c target.2 ↦ W c d.1)).trans <|
    (DirectSum.linearEquivFunOnFintype K
      (BlockFiber f c target.1 × BlockFiber g c target.2)
      (fun q ↦ TensorProduct K (V c q.1.1) (W c q.2.1))).trans <|
    (piProductBlockFiberEquiv (K := K) (V := V) (W := W) f g c target).trans <|
    (DirectSum.linearEquivFunOnFintype K
      (BlockFiber (productCoarseningMap f g) c target)
      (fun q ↦ ProductBlockSpace K V W c q.1)).symm

/-- The distributivity equivalence sends a tensor of the two fiber inclusions to the inclusion
indexed by their paired fine labels. -/
theorem coarsenedExternalBlockEquiv_tmul_lof
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (c : Leg) (target : ProductBlockIndex B D c)
    (a : BlockFiber f c target.1) (d : BlockFiber g c target.2)
    (x : V c a.1) (y : W c d.1) :
    coarsenedExternalBlockEquiv (K := K) (V := V) (W := W)
        f g c target
        (DirectSum.lof K _ _ a x ⊗ₜ[K] DirectSum.lof K _ _ d y) =
      DirectSum.lof K _ _
        (productBlockFiberEquiv f g c target (a, d)) (x ⊗ₜ[K] y) := by
  unfold coarsenedExternalBlockEquiv
  simp only [LinearEquiv.trans_apply, TensorProduct.directSum_lof_tmul_lof]
  apply (DirectSum.linearEquivFunOnFintype K
    (BlockFiber (productCoarseningMap f g) c target)
    (fun q ↦ ProductBlockSpace K V W c q.1)).injective
  funext q
  simp only [LinearEquiv.apply_symm_apply,
    DirectSum.linearEquivFunOnFintype_lof, piProductBlockFiberEquiv]
  by_cases hq : q = productBlockFiberEquiv f g c target (a, d)
  · subst q
    rcases a with ⟨a, ha⟩
    rcases d with ⟨d, hd⟩
    simp [productBlockFiberEquiv]
  · have hpreimage :
        (productBlockFiberEquiv f g c target).symm q ≠ (a, d) := by
      intro h
      apply hq
      rw [← h, (productBlockFiberEquiv f g c target).apply_symm_apply]
    simp [hq, hpreimage]

/-- Include one fine block in the fiber indexed by its image.  This is the canonical coarsening
inclusion with a target type that is visibly `f c (source c)`. -/
noncomputable def fiberBlockInclude
    (f : ∀ c, A c → B c) (source : BlockAddress A) (c : Leg) :
    V c (source c) →ₗ[K] CoarsenedBlockSpace (V := V) f c (f c (source c)) :=
  DirectSum.lof K (BlockFiber f c (f c (source c)))
    (fun q ↦ V c q.1) (⟨source c, rfl⟩ : BlockFiber f c (f c (source c)))

/-- Include one product block in the product-map fiber indexed by the componentwise coarse
labels.  Naming this map keeps proof-dependent casts out of the distributivity interface. -/
noncomputable def pairedCoarsenedBlockInclude
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (left : BlockAddress A) (right : BlockAddress C) (c : Leg) :
    ProductBlockSpace K V W c (left c, right c) →ₗ[K]
      CoarsenedBlockSpace (V := ProductBlockSpace K V W)
        (productCoarseningMap f g) c (f c (left c), g c (right c)) :=
  DirectSum.lof K
    (BlockFiber (productCoarseningMap f g) c
      (f c (left c), g c (right c)))
    (fun q ↦ ProductBlockSpace K V W c q.1)
    (⟨(left c, right c), rfl⟩ : BlockFiber (productCoarseningMap f g) c
      (f c (left c), g c (right c)))

@[simp] theorem fiberBlockInclude_eq_coarsenedBlockInclude
    (f : ∀ c, A c → B c) (source : BlockAddress A) (c : Leg) :
    fiberBlockInclude (K := K) (V := V) f source c =
      coarsenedBlockInclude (K := K) (V := V) f source c :=
  rfl

@[simp] theorem pairedCoarsenedBlockInclude_eq_coarsenedBlockInclude
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (left : BlockAddress A) (right : BlockAddress C) (c : Leg) :
    pairedCoarsenedBlockInclude (K := K) (V := V) (W := W)
        f g left right c =
      coarsenedBlockInclude (K := K) (V := ProductBlockSpace K V W)
        (productCoarseningMap f g) (fun d ↦ (left d, right d)) c :=
  rfl

/-- The distributivity equivalence intertwines the two separate canonical inclusions with the
canonical paired inclusion. -/
theorem coarsenedExternalBlockEquiv_comp_includes
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (left : BlockAddress A) (right : BlockAddress C) (c : Leg) :
    (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
        (f c (left c), g c (right c))).toLinearMap ∘ₗ
      TensorProduct.map
        (fiberBlockInclude (K := K) (V := V) f left c)
        (fiberBlockInclude (K := K) (V := W) g right c) =
      pairedCoarsenedBlockInclude (K := K) (V := V) (W := W)
        f g left right c := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
    fiberBlockInclude, pairedCoarsenedBlockInclude]
  let a : BlockFiber f c (f c (left c)) := ⟨left c, rfl⟩
  let d : BlockFiber g c (g c (right c)) := ⟨right c, rfl⟩
  have h := coarsenedExternalBlockEquiv_tmul_lof
    (K := K) (V := V) (W := W) f g c
    (f c (left c), g c (right c)) a d x y
  have hindex :
      productBlockFiberEquiv f g c (f c (left c), g c (right c)) (a, d) =
        (⟨(left c, right c), rfl⟩ : BlockFiber (productCoarseningMap f g) c
          (f c (left c), g c (right c))) := by
    apply Subtype.ext
    rfl
  cases hindex
  exact h

/-- Tensor-level form of the paired inclusion calculation. -/
theorem map_coarsenedExternalBlockEquiv_external_includes
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (left : BlockAddress A) (right : BlockAddress C)
    (T : Tensor3 K (fun c ↦ V c (left c)))
    (S : Tensor3 K (fun c ↦ W c (right c))) :
    map (fun c ↦
        (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
          (f c (left c), g c (right c))).toLinearMap)
      (Tensor.external
        (map (fiberBlockInclude (K := K) (V := V) f left) T)
        (map (fiberBlockInclude (K := K) (V := W) g right) S)) =
      map (pairedCoarsenedBlockInclude (K := K) (V := V) (W := W)
        f g left right)
        (Tensor.external T S) := by
  rw [← map_external]
  change
    (map (fun c ↦
        (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
          (f c (left c), g c (right c))).toLinearMap) ∘ₗ
      map (fun c ↦ TensorProduct.map
        (fiberBlockInclude (K := K) (V := V) f left c)
        (fiberBlockInclude (K := K) (V := W) g right c)))
      (Tensor.external T S) = _
  rw [← map_comp]
  congr 1
  congr 1
  funext c
  exact coarsenedExternalBlockEquiv_comp_includes
    (K := K) (V := V) (W := W) f g left right c

/-- One pair of source constituents is transported compatibly whether the factors are coarsened
before or after taking their external product. -/
theorem map_coarsenedExternalBlockEquiv_external_coarsenedTerms
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (left : BlockAddress A) (right : BlockAddress C) :
    map (fun c ↦
        (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
          (coarsenBlockAddress f left c,
            coarsenBlockAddress g right c)).toLinearMap)
      (Tensor.external
        (coarsenedTerm P f (coarsenBlockAddress f left) left)
        (coarsenedTerm Q g (coarsenBlockAddress g right) right)) =
      coarsenedTerm (P.external Q) (productCoarseningMap f g)
        (coarsenBlockAddress (productCoarseningMap f g)
          (fun c ↦ (left c, right c)))
        (fun c ↦ (left c, right c)) := by
  rw [coarsenedTerm_eq_map_of_eq P f _ left rfl,
    coarsenedTerm_eq_map_of_eq Q g _ right rfl,
    coarsenedTerm_eq_map_of_eq (P.external Q) (productCoarseningMap f g)
      _ (fun c ↦ (left c, right c)) rfl]
  change
    map (fun c ↦
        (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
          (f c (left c), g c (right c))).toLinearMap)
      (Tensor.external
        (map (coarsenedBlockInclude (K := K) (V := V) f left)
          (P.constituent left))
        (map (coarsenedBlockInclude (K := K) (V := W) g right)
          (Q.constituent right))) =
      map (coarsenedBlockInclude (K := K) (V := ProductBlockSpace K V W)
        (productCoarseningMap f g) (fun c ↦ (left c, right c)))
        (Tensor.external (P.constituent left) (Q.constituent right))
  have hleftInclude :
      coarsenedBlockInclude (K := K) (V := V) f left =
        fiberBlockInclude (K := K) (V := V) f left := by
    funext c
    exact (fiberBlockInclude_eq_coarsenedBlockInclude
      (K := K) (V := V) f left c).symm
  have hrightInclude :
      coarsenedBlockInclude (K := K) (V := W) g right =
        fiberBlockInclude (K := K) (V := W) g right := by
    funext c
    exact (fiberBlockInclude_eq_coarsenedBlockInclude
      (K := K) (V := W) g right c).symm
  have hpairInclude :
      coarsenedBlockInclude (K := K) (V := ProductBlockSpace K V W)
          (productCoarseningMap f g) (fun c ↦ (left c, right c)) =
        pairedCoarsenedBlockInclude (K := K) (V := V) (W := W)
          f g left right := by
    funext c
    exact (pairedCoarsenedBlockInclude_eq_coarsenedBlockInclude
      (K := K) (V := V) (W := W) f g left right c).symm
  rw [hleftInclude, hrightInclude, hpairInclude]
  exact map_coarsenedExternalBlockEquiv_external_includes
    (K := K) (V := V) (W := W) f g left right
    (P.constituent left) (Q.constituent right)

/-- Explicit-target form of the term calculation.  If either source address lies outside its
requested fiber, both sides vanish. -/
theorem map_coarsenedExternalBlockEquiv_external_coarsenedTermsAt
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (leftTarget : BlockAddress B) (rightTarget : BlockAddress D)
    (left : BlockAddress A) (right : BlockAddress C) :
    map (fun c ↦
        (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
          (leftTarget c, rightTarget c)).toLinearMap)
      (Tensor.external
        (coarsenedTerm P f leftTarget left)
        (coarsenedTerm Q g rightTarget right)) =
      coarsenedTerm (P.external Q) (productCoarseningMap f g)
        (fun c ↦ (leftTarget c, rightTarget c))
        (fun c ↦ (left c, right c)) := by
  by_cases hleft : coarsenBlockAddress f left = leftTarget
  · by_cases hright : coarsenBlockAddress g right = rightTarget
    · subst leftTarget
      subst rightTarget
      simpa only [coarsenBlockAddress_productCoarseningMap] using
        map_coarsenedExternalBlockEquiv_external_coarsenedTerms
          (K := K) (V := V) (W := W) P Q f g left right
    · have hpair :
          (fun c ↦ (f c (left c), g c (right c))) ≠
            (fun c ↦ (leftTarget c, rightTarget c)) := by
        intro h
        apply hright
        funext c
        exact congrArg Prod.snd (congrFun h c)
      simp [coarsenedTerm, hright, hpair]
  · have hpair :
        (fun c ↦ (f c (left c), g c (right c))) ≠
          (fun c ↦ (leftTarget c, rightTarget c)) := by
      intro h
      apply hleft
      funext c
      exact congrArg Prod.fst (congrFun h c)
    simp [coarsenedTerm, hleft, hpair]

/-- Coarsening commutes with one partitioned external product, constituent by constituent,
through the canonical blockwise distributivity equivalence. -/
theorem map_coarsenedExternalBlockEquiv_external_coarsenedConstituents
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (leftTarget : BlockAddress B) (rightTarget : BlockAddress D) :
    map (fun c ↦
        (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
          (leftTarget c, rightTarget c)).toLinearMap)
      (Tensor.external
        ((P.coarsen f).constituent leftTarget)
        ((Q.coarsen g).constituent rightTarget)) =
      ((P.external Q).coarsen (productCoarseningMap f g)).constituent
        (fun c ↦ (leftTarget c, rightTarget c)) := by
  classical
  unfold PartitionedTensor.coarsen coarsenedConstituent
  rw [LinearMap.map_sum₂, map_sum]
  simp_rw [map_sum,
    map_coarsenedExternalBlockEquiv_external_coarsenedTermsAt
      (K := K) (V := V) (W := W) P Q f g leftTarget rightTarget]
  change
    (∑ left ∈ P.support, ∑ right ∈ Q.support,
      coarsenedTerm (P.external Q) (productCoarseningMap f g)
        (fun c ↦ (leftTarget c, rightTarget c))
        (blockAddressProductEquiv (A := A) (B := C) (left, right))) =
      ∑ source ∈ (P.support.product Q.support).map
          (blockAddressProductEquiv (A := A) (B := C)).toEmbedding,
        coarsenedTerm (P.external Q) (productCoarseningMap f g)
          (fun c ↦ (leftTarget c, rightTarget c)) source
  rw [Finset.sum_map]
  exact (Finset.sum_product P.support Q.support
    (fun q ↦ coarsenedTerm (P.external Q) (productCoarseningMap f g)
      (fun c ↦ (leftTarget c, rightTarget c))
      (blockAddressProductEquiv (A := A) (B := C) q))).symm

/-- Partition-level distributivity: taking an external product after coarsening is a blockwise
reindexing of coarsening the external product by the product map. -/
theorem PartitionedTensor.external_coarsen_reindex
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c) :
    ((P.coarsen f).external (Q.coarsen g)).reindex
        (fun _ ↦ Equiv.refl _)
        (fun c target ↦
          coarsenedExternalBlockEquiv (K := K) (V := V) (W := W)
            f g c target) =
      (P.external Q).coarsen (productCoarseningMap f g) := by
  classical
  apply PartitionedTensor.ext
  · ext target
    simp only [PartitionedTensor.reindex_support, Finset.mem_map,
      blockAddressCongr, PartitionedTensor.mem_external_support,
      PartitionedTensor.coarsen_support, Finset.mem_image]
    constructor
    · rintro ⟨renamed, ⟨⟨left, hleftSupport, hleft⟩,
          ⟨right, hrightSupport, hright⟩⟩, hrenamed⟩
      change renamed = target at hrenamed
      subst target
      refine ⟨blockAddressProductEquiv (A := A) (B := C) (left, right), ?_, ?_⟩
      · exact ⟨hleftSupport, hrightSupport⟩
      · funext c
        exact Prod.ext (congrFun hleft c) (congrFun hright c)
    · rintro ⟨source, hsource, hsourceMap⟩
      refine ⟨target, ?_, rfl⟩
      refine ⟨⟨(fun c ↦ (source c).1), hsource.1, ?_⟩,
        ⟨(fun c ↦ (source c).2), hsource.2, ?_⟩⟩
      · funext c
        exact congrArg Prod.fst (congrFun hsourceMap c)
      · funext c
        exact congrArg Prod.snd (congrFun hsourceMap c)
  · funext target
    have htarget : (fun c ↦ ((target c).1, (target c).2)) = target := by
      funext c
      exact Prod.eta (target c)
    rw [← htarget]
    change
      map (fun c ↦
          (coarsenedExternalBlockEquiv (K := K) (V := V) (W := W) f g c
            ((target c).1, (target c).2)).toLinearMap)
        (Tensor.external
          ((P.coarsen f).constituent (fun c ↦ (target c).1))
          ((Q.coarsen g).constituent (fun c ↦ (target c).2))) =
        ((P.external Q).coarsen (productCoarseningMap f g)).constituent
          (fun c ↦ ((target c).1, (target c).2))
    exact map_coarsenedExternalBlockEquiv_external_coarsenedConstituents
      (K := K) (V := V) (W := W) P Q f g
      (fun c ↦ (target c).1) (fun c ↦ (target c).2)

/-- Any coordinatewise block selection is preserved by external/coarsening distributivity. -/
theorem Isomorphic.select_external_coarsen
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (keep : ∀ c, ProductBlockIndex B D c → Prop)
    [∀ c q, Decidable (keep c q)] :
    Isomorphic
      ((((P.coarsen f).external (Q.coarsen g)).select keep).realize)
      ((((P.external Q).coarsen (productCoarseningMap f g)).select keep).realize) := by
  let source := (P.coarsen f).external (Q.coarsen g)
  let e : ∀ c, Equiv.Perm (ProductBlockIndex B D c) := fun _ ↦ Equiv.refl _
  let blockEquiv : ∀ c target,
      ProductBlockSpace K (CoarsenedBlockSpace (V := V) f)
          (CoarsenedBlockSpace (V := W) g) c ((e c).symm target) ≃ₗ[K]
        CoarsenedBlockSpace (V := ProductBlockSpace K V W)
          (productCoarseningMap f g) c target :=
    fun c target ↦ coarsenedExternalBlockEquiv
      (K := K) (V := V) (W := W) f g c target
  have hreindex : source.reindex e blockEquiv =
      (P.external Q).coarsen (productCoarseningMap f g) := by
    exact P.external_coarsen_reindex Q f g
  have hselected : (source.select keep).reindex e blockEquiv =
      ((P.external Q).coarsen (productCoarseningMap f g)).select keep := by
    rw [PartitionedTensor.reindex_select, hreindex]
    simp only [e, Equiv.refl_symm, Equiv.refl_apply]
  have hiso := Isomorphic.partitionedReindex (source.select keep) e blockEquiv
  rw [hselected] at hiso
  exact hiso

/-- Coherence for first reindexing the left factor of an external product and then applying a
second blockwise reindexing.  This is the induction step behind power/coarsening
distributivity. -/
theorem PartitionedTensor.external_reindex_left_then_reindex
    {X : ∀ c, A c → Type (max u s)}
    [∀ c a, AddCommMonoid (X c a)] [∀ c a, Module K (X c a)]
    {Y : ∀ c, ProductBlockIndex A C c → Type (max u r)}
    [∀ c q, AddCommMonoid (Y c q)] [∀ c q, Module K (Y c q)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (leftEquiv : ∀ c a, V c a ≃ₗ[K] X c a)
    (afterEquiv : ∀ c q, ProductBlockSpace K X W c q ≃ₗ[K] Y c q) :
    (P.external Q).reindex (fun _ ↦ Equiv.refl _)
        (fun c q ↦
          (TensorProduct.congr (leftEquiv c q.1)
            (LinearEquiv.refl K _)).trans (afterEquiv c q)) =
      ((P.reindex (fun _ ↦ Equiv.refl _) leftEquiv).external Q).reindex
        (fun _ ↦ Equiv.refl _) afterEquiv := by
  classical
  apply PartitionedTensor.ext
  · ext target
    simp [PartitionedTensor.reindex, PartitionedTensor.external,
      blockAddressCongr]
  · funext target
    have htarget : (fun c ↦ ((target c).1, (target c).2)) = target := by
      funext c
      exact Prod.eta (target c)
    rw [← htarget]
    change
      map (fun c ↦
          (afterEquiv c ((target c).1, (target c).2)).toLinearMap ∘ₗ
            TensorProduct.map
              (leftEquiv c (target c).1).toLinearMap LinearMap.id)
        (Tensor.external
          (P.constituent (fun c ↦ (target c).1))
          (Q.constituent (fun c ↦ (target c).2))) =
      map (fun c ↦ (afterEquiv c ((target c).1, (target c).2)).toLinearMap)
        (Tensor.external
          (map (fun c ↦ (leftEquiv c (target c).1).toLinearMap)
            (P.constituent (fun c ↦ (target c).1)))
          (Q.constituent (fun c ↦ (target c).2)))
    have hexternal :
        map (fun c ↦ TensorProduct.map
            (leftEquiv c (target c).1).toLinearMap LinearMap.id)
          (Tensor.external
            (P.constituent (fun c ↦ (target c).1))
            (Q.constituent (fun c ↦ (target c).2))) =
          Tensor.external
            (map (fun c ↦ (leftEquiv c (target c).1).toLinearMap)
              (P.constituent (fun c ↦ (target c).1)))
            (Q.constituent (fun c ↦ (target c).2)) := by
      rw [map_external]
      exact congrArg
        (fun R ↦ Tensor.external
          (map (fun c ↦ (leftEquiv c (target c).1).toLinearMap)
            (P.constituent (fun c ↦ (target c).1))) R)
        (LinearMap.congr_fun
          (map_id (K := K) (V := fun c ↦ W c (target c).2))
          (Q.constituent (fun c ↦ (target c).2)))
    rw [← hexternal]
    exact LinearMap.congr_fun
      (map_comp
        (V := fun c ↦ ProductBlockSpace K V W c
          ((target c).1, (target c).2))
        (W := fun c ↦ ProductBlockSpace K X W c
          ((target c).1, (target c).2))
        (U := fun c ↦ Y c ((target c).1, (target c).2))
        (fun c ↦ TensorProduct.map
          (leftEquiv c (target c).1).toLinearMap LinearMap.id)
        (fun c ↦ (afterEquiv c ((target c).1, (target c).2)).toLinearMap))
      (Tensor.external
        (P.constituent (fun c ↦ (target c).1))
        (Q.constituent (fun c ↦ (target c).2)))

/-! ## Iterated positive powers -/

/-- Universe-explicit block family of a positive power formed after coarsening. -/
abbrev CoarsenedPositivePowerBlockSpace
    (f : ∀ c, A c → B c) (n : ℕ) :=
  @PositivePowerBlockSpace.{u, max v w, x} B K _
    (CoarsenedBlockSpace (V := V) f) _ _ n

/-- Blockwise distributivity iterated through a positive power.  A word of coarsened blocks is
canonically equivalent to the direct sum of all fine block words mapping to it. -/
noncomputable def positivePowerCoarseningBlockEquiv
    (f : ∀ c, A c → B c) :
    (n : ℕ) → (c : Leg) → (target : PositiveWord (B c) n) →
      CoarsenedPositivePowerBlockSpace (K := K) (V := V) f n c target ≃ₗ[K]
        CoarsenedBlockSpace (V := PositivePowerBlockSpace K V n)
          (fun c ↦ positiveWordMap (f c) n) c target
  | 0, _c, _target => LinearEquiv.refl K _
  | n + 1, c, target =>
      (TensorProduct.congr
        (positivePowerCoarseningBlockEquiv f n c target.1)
        (LinearEquiv.refl K _)).trans
      (coarsenedExternalBlockEquiv
        (K := K)
        (V := PositivePowerBlockSpace K V n)
        (W := V)
        (fun c ↦ positiveWordMap (f c) n) f c target)

@[simp] theorem positivePowerCoarseningBlockEquiv_zero
    (f : ∀ c, A c → B c) (c : Leg) (target : B c) :
    positivePowerCoarseningBlockEquiv (K := K) (V := V) f 0 c target =
      LinearEquiv.refl K _ :=
  rfl

@[simp] theorem positivePowerCoarseningBlockEquiv_succ
    (f : ∀ c, A c → B c) (n : ℕ) (c : Leg)
    (target : PositiveWord (B c) (n + 1)) :
    positivePowerCoarseningBlockEquiv (K := K) (V := V) f (n + 1) c target =
      (TensorProduct.congr
        (positivePowerCoarseningBlockEquiv (K := K) (V := V)
          f n c target.1)
        (LinearEquiv.refl K _)).trans
      (coarsenedExternalBlockEquiv
        (K := K)
        (V := PositivePowerBlockSpace K V n)
        (W := V)
        (fun c ↦ positiveWordMap (f c) n) f c target) :=
  rfl

/-- Forming a positive partitioned power after coarsening is exactly a blockwise reindexing of
forming the fine positive power first and then coarsening its words letterwise. -/
theorem PartitionedTensor.positivePower_coarsen_reindex
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) :
    (P.coarsenedPositivePower f n).reindex
        (fun _ ↦ Equiv.refl _)
        (positivePowerCoarseningBlockEquiv (K := K) (V := V) f n) =
      (P.positivePower n).coarsen (fun c ↦ positiveWordMap (f c) n) := by
  induction n with
  | zero =>
      change (P.coarsen f).reindex (fun _ ↦ Equiv.refl _)
          (fun c target ↦ LinearEquiv.refl K
            (CoarsenedBlockSpace (V := V) f c target)) = P.coarsen f
      exact PartitionedTensor.reindex_refl (P.coarsen f)
  | succ n ih =>
      let prefixMap : ∀ c, PositiveWord (A c) n → PositiveWord (B c) n :=
        fun c ↦ positiveWordMap (f c) n
      let prefixEquiv :=
        positivePowerCoarseningBlockEquiv (K := K) (V := V) f n
      let afterEquiv : ∀ c target,
          ProductBlockSpace K
              (CoarsenedBlockSpace (V := PositivePowerBlockSpace K V n) prefixMap)
              (CoarsenedBlockSpace (V := V) f) c target ≃ₗ[K]
            CoarsenedBlockSpace
              (V := ProductBlockSpace K (PositivePowerBlockSpace K V n) V)
              (productCoarseningMap prefixMap f) c target :=
        fun c target ↦ coarsenedExternalBlockEquiv
          (K := K) (V := PositivePowerBlockSpace K V n) (W := V)
          prefixMap f c target
      calc
        (P.coarsenedPositivePower f (n + 1)).reindex
            (fun _ ↦ Equiv.refl _)
            (positivePowerCoarseningBlockEquiv (K := K) (V := V) f (n + 1)) =
          (((P.coarsenedPositivePower f n).reindex
              (fun _ ↦ Equiv.refl _) prefixEquiv).external (P.coarsen f)).reindex
            (fun _ ↦ Equiv.refl _) afterEquiv := by
              change
                (((P.coarsenedPositivePower f n).external (P.coarsen f)).reindex
                    (fun _ ↦ Equiv.refl _)
                    (fun c target ↦
                      (TensorProduct.congr (prefixEquiv c target.1)
                        (LinearEquiv.refl K _)).trans (afterEquiv c target))) =
                  (((P.coarsenedPositivePower f n).reindex
                    (fun _ ↦ Equiv.refl _) prefixEquiv).external
                    (P.coarsen f)).reindex (fun _ ↦ Equiv.refl _) afterEquiv
              exact
                PartitionedTensor.external_reindex_left_then_reindex.{
                  u, max v w, x, x, max v w, max v w, max v w}
                (K := K)
                (A := fun c ↦ PositiveWord (B c) n) (C := B)
                (V := CoarsenedPositivePowerBlockSpace (K := K) (V := V) f n)
                (W := CoarsenedBlockSpace (V := V) f)
                (X := CoarsenedBlockSpace
                  (V := PositivePowerBlockSpace K V n) prefixMap)
                (Y := CoarsenedBlockSpace
                  (V := ProductBlockSpace K (PositivePowerBlockSpace K V n) V)
                  (productCoarseningMap prefixMap f))
                (P.coarsenedPositivePower f n) (P.coarsen f)
                prefixEquiv afterEquiv
        _ = (((P.positivePower n).coarsen prefixMap).external
              (P.coarsen f)).reindex (fun _ ↦ Equiv.refl _) afterEquiv := by
              rw [ih]
        _ = (P.positivePower (n + 1)).coarsen
              (fun c ↦ positiveWordMap (f c) (n + 1)) := by
              change
                (((P.positivePower n).coarsen prefixMap).external
                    (P.coarsen f)).reindex (fun _ ↦ Equiv.refl _) afterEquiv =
                  ((P.positivePower n).external P).coarsen
                    (productCoarseningMap prefixMap f)
              exact
                PartitionedTensor.external_coarsen_reindex.{u, v, w, x, w, x, v}
                (K := K)
                (A := fun c ↦ PositiveWord (A c) n)
                (B := fun c ↦ PositiveWord (B c) n)
                (C := A) (D := B)
                (V := PositivePowerBlockSpace K V n) (W := V)
                (P.positivePower n) P prefixMap f

/-- Any legwise selection on quotient words is preserved by the canonical equivalence between
`(P.coarsen f).positivePower n` and `P.positivePower n` coarsened letterwise.  In particular,
this transports a whole selected type class, rather than choosing one fine representative in
each quotient fiber. -/
theorem Isomorphic.select_positivePower_coarsen
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (keep : ∀ c, PositiveWord (B c) n → Prop)
    [∀ c word, Decidable (keep c word)] :
    Isomorphic
      (((P.coarsenedPositivePower f n).select keep).realize)
      (((((P.positivePower n).coarsen
        (fun c ↦ positiveWordMap (f c) n)).select keep)).realize) := by
  let source := P.coarsenedPositivePower f n
  let e : ∀ c, Equiv.Perm (PositiveWord (B c) n) := fun _ ↦ Equiv.refl _
  let blockEquiv : ∀ c target,
      CoarsenedPositivePowerBlockSpace (K := K) (V := V) f n c
          ((e c).symm target) ≃ₗ[K]
        CoarsenedBlockSpace (V := PositivePowerBlockSpace K V n)
          (fun c ↦ positiveWordMap (f c) n) c target :=
    fun c target ↦ positivePowerCoarseningBlockEquiv
      (K := K) (V := V) f n c target
  have hreindex : source.reindex e blockEquiv =
      (P.positivePower n).coarsen (fun c ↦ positiveWordMap (f c) n) := by
    exact P.positivePower_coarsen_reindex f n
  have hselected : (source.select keep).reindex e blockEquiv =
      ((P.positivePower n).coarsen
        (fun c ↦ positiveWordMap (f c) n)).select keep := by
    rw [PartitionedTensor.reindex_select, hreindex]
    simp only [e, Equiv.refl_symm, Equiv.refl_apply]
  have hiso := Isomorphic.partitionedReindex (source.select keep) e blockEquiv
  rw [hselected] at hiso
  exact hiso

/-- Exact-type specialization of `Isomorphic.select_positivePower_coarsen`.  The left side is
the public quotient-first API `selectCoarsenedPositiveTypes`; the right side forms the full fine
power first, regroups its words by their quotient images, and selects the same quotient type. -/
theorem Isomorphic.selectCoarsenedPositiveTypes_to_afterPowerCoarsenedTypes
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (a : ∀ c, B c → ℕ) :
    Isomorphic
      ((P.selectCoarsenedPositiveTypes f n a).realize)
      (((((P.positivePower n).coarsen
          (fun c ↦ positiveWordMap (f c) n)).select
        (fun c word ↦ word ∈ positiveTypeClass (B c) n (a c)))).realize) := by
  classical
  simpa [PartitionedTensor.selectCoarsenedPositiveTypes] using
    Isomorphic.select_positivePower_coarsen P f n
      (fun c word ↦ word ∈ positiveTypeClass (B c) n (a c))

/-- The fine addresses over one coarse product address are exactly the Cartesian product of the
two separate fine-address fibers. -/
theorem PartitionedTensor.external_support_filter_productCoarseningMap_eq
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (target : BlockAddress (ProductBlockIndex B D)) :
    (P.external Q).support.filter
        (fun source ↦ coarsenBlockAddress (productCoarseningMap f g) source = target) =
      ((P.support.filter (fun source ↦
          coarsenBlockAddress f source = fun c ↦ (target c).1)).product
        (Q.support.filter (fun source ↦
          coarsenBlockAddress g source = fun c ↦ (target c).2))).map
        (blockAddressProductEquiv (A := A) (B := C)).toEmbedding := by
  classical
  ext source
  simp [PartitionedTensor.mem_external_support, blockAddressProductEquiv,
    productCoarseningMap, coarsenBlockAddress, funext_iff]
  constructor
  · rintro ⟨⟨hleft, hright⟩, hmap⟩
    exact ⟨⟨hleft, fun c ↦ congrArg Prod.fst (hmap c)⟩,
      hright, fun c ↦ congrArg Prod.snd (hmap c)⟩
  · rintro ⟨⟨hleft, hleftMap⟩, hright, hrightMap⟩
    exact ⟨⟨hleft, hright⟩,
      fun c ↦ Prod.ext (hleftMap c) (hrightMap c)⟩

end AlgebraicComplexity.Tensor
