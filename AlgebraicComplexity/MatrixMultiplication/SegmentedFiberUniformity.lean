/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.LocalizedCoarsenedRelabeling
import AlgebraicComplexity.MatrixMultiplication.SegmentedHoleRepair

set_option autoImplicit false

/-!
# One common leaf: segmented fine fibers over targets of the same type

The batched segmented Hole Lemma
(`restricts_indexedDirectSum_segmentedHoleRepair_batched`) delivers a direct sum of copies of
**one** leaf.  The leaf supplied by `hleaf` is localized: it is the segmented selection inside the
fine fiber over a particular coarse target, and both the fiber and the segmentation depend on that
target.  This module supplies the missing uniformity: any two coarse targets related by a
permutation of word positions --- equivalently, any two coarse words of the same type --- have
*isomorphic* segmented fine fibers, so there is a single leaf up to isomorphism.

The engine's `Isomorphic.positivePower_localizedCoarseningFiberSelect_position` cannot be used
directly, because it requires the fine keep predicate to be invariant under the permutation.  A
segmented predicate is not: permuting positions carries the segmentation along.  What is true, and
what is proved here, is that the predicate moves *exactly* by the same permutation, which is the
premise of the two-predicate form in `Tensor/LocalizedCoarsenedRelabeling.lean`.

`[DuanWuZhou2022]`, `hole_lemma.tex` Claim 1 and `global_value.tex`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w x

/-! ## Claim 1 without the segment-preservation premise -/

section SegmentMultiplicity

variable {I : Type w} [DecidableEq I] {n m : ℕ}

/-- **Claim 1, general form.**  Permuting word positions in *both* the segmentation and the word
leaves every segment multiplicity unchanged.  The committed `segmentMultiplicity_comp_perm` is the
special case where the permutation preserves the segmentation, so `seg ∘ σ` collapses to `seg`. -/
theorem segmentMultiplicity_comp_perm_general (seg : Fin n → Fin m)
    (σ : Equiv.Perm (Fin n)) (word : Fin n → I) (t : Fin m) :
    segmentMultiplicity (seg ∘ σ) (word ∘ σ) t = segmentMultiplicity seg word t := by
  classical
  funext a
  unfold segmentMultiplicity
  refine Finset.card_nbij' (fun i ↦ σ i) (fun j ↦ σ.symm j) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi.2.1, hi.2.2⟩
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_filter] at hj
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · show seg (σ (σ.symm j)) = t
      rw [Equiv.apply_symm_apply]
      exact hj.2.1
    · show word (σ (σ.symm j)) = a
      rw [Equiv.apply_symm_apply]
      exact hj.2.2
  · intro i _
    simp
  · intro j _
    simp

/-- The inverse form: the permutation may be moved off the word and onto the segmentation. -/
theorem segmentMultiplicity_comp_perm_symm (seg : Fin n → Fin m)
    (σ : Equiv.Perm (Fin n)) (word : Fin n → I) (t : Fin m) :
    segmentMultiplicity seg (word ∘ ⇑σ.symm) t =
      segmentMultiplicity (seg ∘ ⇑σ) word t := by
  have h := segmentMultiplicity_comp_perm_general (seg ∘ ⇑σ) σ.symm word t
  simpa [Function.comp_assoc] using h

end SegmentMultiplicity

/-! ## The keep predicate moves by the same permutation -/

section Keeps

variable {A : Leg → Type w} [∀ c, DecidableEq (A c)] {m : ℕ}

/-- **The segmented keep predicate transports.**  Relabeling word positions by `σ` sends the
predicate segmented by `seg` to the predicate segmented by `seg ∘ σ`.  With `σ` segment-preserving
this is the committed `SegmentedSplitRestriction.keeps_positionEquiv_symm`. -/
theorem SegmentedSplitRestriction.keeps_comp_perm
    (profile : SegmentedSplitRestriction A m) (n : ℕ) (seg : Fin (n + 1) → Fin m)
    (σ : Equiv.Perm (Fin (n + 1))) (c : Leg) (word : PositiveWord (A c) n) :
    profile.Keeps n seg c ((positiveWordPositionEquiv (A c) n σ).symm word) ↔
      profile.Keeps n (seg ∘ ⇑σ) c word := by
  classical
  unfold SegmentedSplitRestriction.Keeps
  refine forall_congr' fun t ↦ ?_
  rw [positiveWordPositionEquiv_symm, positiveWordEquiv_position_apply,
    segmentMultiplicity_comp_perm_symm seg σ (positiveWordEquiv (A c) n word) t]

end Keeps

/-! ## Uniformity of the localized segmented leaf -/

section Uniformity

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **One common leaf.**

Two coarse targets related by a permutation `σ` of word positions have isomorphic segmented fine
fibers, once the segmentation is transported by the same `σ`.  In the `[DuanWuZhou2022]`
application the segmentation *is* read off the coarse target, so `seg ∘ σ` is literally the
segmentation of the permuted target, and this says: the leaf depends on the coarse target only
through its type.  That is exactly what the batched Hole Lemma needs. -/
theorem segmentedLocalizedFiber_isomorphic_position
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Isomorphic
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n) target).select
        (profile.Keeps n seg)).realize)
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n)
          (positionRelabelBlockAddress B n σ target)).select
        (profile.Keeps n (seg ∘ ⇑σ))).realize) :=
  Tensor.Isomorphic.positivePower_localizedCoarseningFiberSelect_position_two
    P f n target (profile.Keeps n seg) (profile.Keeps n (seg ∘ ⇑σ)) σ
    (SegmentedSplitRestriction.keeps_comp_perm profile n seg σ)

end Uniformity

end AlgebraicComplexity
