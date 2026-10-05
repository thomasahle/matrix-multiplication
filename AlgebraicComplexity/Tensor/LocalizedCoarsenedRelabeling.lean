/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection

set_option autoImplicit false

/-!
# Localized fine selection under a position relabeling that moves the predicate

`Tensor/LocalizedCoarsenedSelection.lean` transports a localized fine selection along a common
permutation of word positions, but only when the fine keep predicate is *invariant* under that
permutation (`positivePower_localizedCoarseningFiberSelect_position`).  That is the right premise
for a keep predicate defined from a pooled type, which sees no position structure.

A *segmented* keep predicate is not invariant: permuting positions carries the segmentation along
with the word, so the predicate at the permuted target is the predicate at the original target
composed with the permutation.  This module records the two-predicate form, where the source and
target keeps are related by exactly the relabeling being applied.  The proof is the committed one
with `hkeep` weakened; nothing else changes.

`[DuanWuZhou2022]`, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Position relabeling transports localized box parts between *two* fine keep predicates, given
that the relabeling carries the source predicate to the target one. -/
theorem relabelParts_coarseningFiberSelectParts_two
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (keepSource keepTarget : ∀ c, PositiveWord (A c) n → Prop)
    [∀ c word, Decidable (keepSource c word)]
    [∀ c word, Decidable (keepTarget c word)]
    (sigma : Equiv.Perm (Fin (n + 1)))
    (hkeep : ∀ c word,
      keepSource c ((positiveWordPositionEquiv (A c) n sigma).symm word) ↔
        keepTarget c word) :
    relabelParts
        (fun c ↦ positiveWordPositionEquiv (A c) n sigma)
        (coarseningFiberSelectParts
          (fun c ↦ positiveWordMap (f c) n) target keepSource) =
      coarseningFiberSelectParts (fun c ↦ positiveWordMap (f c) n)
        (positionRelabelBlockAddress B n sigma target) keepTarget := by
  classical
  funext c
  ext word
  rw [mem_relabelParts, mem_coarseningFiberSelectParts,
    mem_coarseningFiberSelectParts]
  exact and_congr
    (positiveWordMap_position_symm_eq_iff (f c) n sigma word (target c))
    (hkeep c word)

namespace Isomorphic

/-- **Uniformity of localized fine fibers, with a moving keep predicate.**

A common position permutation carries the localized selected tensor over one coarse address to
the corresponding tensor over the permuted coarse address, transporting the fine keep predicate
along with it.  With `keepSource = keepTarget` this is the committed
`positivePower_localizedCoarseningFiberSelect_position`. -/
theorem positivePower_localizedCoarseningFiberSelect_position_two
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (keepSource keepTarget : ∀ c, PositiveWord (A c) n → Prop)
    [∀ c word, Decidable (keepSource c word)]
    [∀ c word, Decidable (keepTarget c word)]
    (sigma : Equiv.Perm (Fin (n + 1)))
    (hkeep : ∀ c word,
      keepSource c ((positiveWordPositionEquiv (A c) n sigma).symm word) ↔
        keepTarget c word) :
    Isomorphic
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n) target).select keepSource).realize)
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n)
          (positionRelabelBlockAddress B n sigma target)).select keepTarget).realize) := by
  let R := P.positivePower n
  let r := PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
    P n sigma
  let parts := coarseningFiberSelectParts
    (fun c ↦ positiveWordMap (f c) n) target keepSource
  have hparts : relabelParts r.partEquiv parts =
      coarseningFiberSelectParts (fun c ↦ positiveWordMap (f c) n)
        (positionRelabelBlockAddress B n sigma target) keepTarget := by
    rw [show r.partEquiv =
        fun c ↦ positiveWordPositionEquiv (A c) n sigma by
      funext c
      exact PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
        P n sigma c]
    exact relabelParts_coarseningFiberSelectParts_two
      f n target keepSource keepTarget sigma hkeep
  have h := r.box_isomorphic parts
  rw [hparts] at h
  simpa only [R, parts,
    PartitionedTensor.coarseningFiber_select_eq_box] using h

end Isomorphic

end AlgebraicComplexity.Tensor
