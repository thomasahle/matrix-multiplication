/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivisionIterated
import AlgebraicComplexity.MatrixMultiplication.SegmentedFiberUniformity

set_option autoImplicit false

/-!
# Sorting a segmentation into consecutive blocks

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean` divides a localized segmented leaf
over a list of **consecutive** regions.  A segmentation read off a word --- `[duan2023faster]`'s
`dwz63Seg`, which labels a position by the coarse cell sitting there --- is not consecutive: the
fifteen cells are scattered through the word.  This module supplies the missing permutation.

## The route: same type, hence a position permutation

Nothing here sorts anything by an order.  The canonical consecutive segmentation
`SegmentRegionBlock.seg` is *built* from the block sizes, its letter multiplicities are computed
(`SegmentRegionBlock.multiplicity_seg`), and then the committed
`WordType.positionPermOfSameMultiplicity` --- two words of the same multiplicity type differ by a
permutation of their positions --- produces the permutation outright.  That is why there is no
monotonicity argument and no sorted-list machinery: "consecutive" is a *construction*, and being
conjugate to it is a statement about multiplicities only.

`Tensor.Isomorphic.segmentedLocalizedSplittingPower_position` then absorbs that permutation, moving
`seg` to `seg ∘ σ` and the coarse target to `positionRelabelBlockAddress B n σ target` together.
It is the committed `segmentedLocalizedFiber_isomorphic_position` read in the
`segmentedLocalizedSplittingPower` spelling, through the committed bridge
`coarseningFiber_select_eq_segmentedLocalizedSplittingPower`; no new mathematics.

## Why the blocks carry a label as well as a spec

A `SegmentRegionSpec` (`SegmentedLocalizedDivisionIterated.lean`) says how many positions a region
holds, which per-segment type it prescribes and which weight it carries.  For the division that is
all that is needed.  To *build* a consecutive segmentation one also has to say which segment each
region's positions belong to, and that is the `label` field added here.  The two
`segmentationLeft` / `segmentationRight` lemmas below are what make the block segmentation match
the recursion of the division: peeling the head region off `SegmentRegionBlock.seg` leaves the
constant segmentation on that region and the block segmentation of the tail on the rest.  The
constant segmentation is exactly where `SegmentedSplitRestriction.keeps_const_seg_iff` applies, so
each factor is a one-segment power.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `hole_lemma.tex` and `global_value.tex` section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/hole_lemma.tex:1-168` (whole file).
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-! ## Regional segmentations of a concatenated segmentation -/

section Append

variable {M : ℕ}

/-- The left region of a concatenated segmentation carries the left factor. -/
theorem segmentationLeft_append (n p : ℕ) (u : Fin (n + 1) → Fin M) (v : Fin (p + 1) → Fin M)
    (h : n + p + 1 + 1 = n + 1 + (p + 1)) :
    segmentationLeft n p (Fin.append u v ∘ Fin.cast h) = u := by
  funext i
  unfold segmentationLeft
  simp only [Function.comp_apply]
  rw [show Fin.cast h (Fin.cast (show n + 1 + (p + 1) = n + p + 1 + 1 from by omega)
      (Fin.castAdd (p + 1) i)) = Fin.castAdd (p + 1) i from Fin.ext (by simp)]
  exact Fin.append_left u v i

/-- The right region of a concatenated segmentation carries the right factor. -/
theorem segmentationRight_append (n p : ℕ) (u : Fin (n + 1) → Fin M) (v : Fin (p + 1) → Fin M)
    (h : n + p + 1 + 1 = n + 1 + (p + 1)) :
    segmentationRight n p (Fin.append u v ∘ Fin.cast h) = v := by
  funext j
  unfold segmentationRight
  simp only [Function.comp_apply]
  rw [show Fin.cast h (Fin.cast (show n + 1 + (p + 1) = n + p + 1 + 1 from by omega)
      (Fin.natAdd (n + 1) j)) = Fin.natAdd (n + 1) j from Fin.ext (by simp)]
  exact Fin.append_right u v j

end Append

/-! ## Labelled regions and their consecutive segmentation -/

/-- **A consecutive region together with the segment its positions belong to.**  The spec is what
the division consumes; the label is what the segmentation is built from. -/
structure SegmentRegionBlock (A : Leg → Type w) (c₀ : Leg) (M : ℕ) extends
    SegmentRegionSpec A c₀ M where
  /-- Every position of this region belongs to segment `label`. -/
  label : Fin M

namespace SegmentRegionBlock

variable {A : Leg → Type w} {c₀ : Leg} {M : ℕ}

/-- The underlying region specs, which is what the division of
`SegmentedLocalizedDivisionIterated.lean` consumes. -/
abbrev specs (rest : List (SegmentRegionBlock A c₀ M)) : List (SegmentRegionSpec A c₀ M) :=
  rest.map SegmentRegionBlock.toSegmentRegionSpec

/-- The additional-letter parameter of a head block followed by a tail of blocks. -/
abbrev total (b : SegmentRegionBlock A c₀ M) (rest : List (SegmentRegionBlock A c₀ M)) : ℕ :=
  SegmentRegionSpec.total b.toSegmentRegionSpec (specs rest)

@[simp] theorem total_nil (b : SegmentRegionBlock A c₀ M) : total b [] = b.size := rfl

@[simp] theorem total_cons (b t : SegmentRegionBlock A c₀ M)
    (rest : List (SegmentRegionBlock A c₀ M)) :
    total b (t :: rest) = b.size + total t rest + 1 := rfl

/-- The length equality the concatenation of the head block with the tail needs. -/
theorem total_cons_succ (b t : SegmentRegionBlock A c₀ M)
    (rest : List (SegmentRegionBlock A c₀ M)) :
    total b (t :: rest) + 1 = b.size + 1 + (total t rest + 1) := by
  rw [total_cons]
  omega

/-- **The canonical consecutive segmentation.**  Every position of a block carries that block's
label, blocks laid end to end in list order. -/
def seg : (b : SegmentRegionBlock A c₀ M) → (rest : List (SegmentRegionBlock A c₀ M)) →
    (Fin (total b rest + 1) → Fin M)
  | b, [] => fun _ ↦ b.label
  | b, t :: rest =>
      Fin.append (fun _ : Fin (b.size + 1) ↦ b.label) (seg t rest) ∘
        Fin.cast (total_cons_succ b t rest)

@[simp] theorem seg_nil (b : SegmentRegionBlock A c₀ M) : seg b [] = fun _ ↦ b.label := rfl

theorem seg_cons (b t : SegmentRegionBlock A c₀ M) (rest : List (SegmentRegionBlock A c₀ M)) :
    seg b (t :: rest) =
      Fin.append (fun _ : Fin (b.size + 1) ↦ b.label) (seg t rest) ∘
        Fin.cast (total_cons_succ b t rest) := rfl

/-- Peeling the head block leaves the constant segmentation on it. -/
@[simp] theorem segmentationLeft_seg (b t : SegmentRegionBlock A c₀ M)
    (rest : List (SegmentRegionBlock A c₀ M)) :
    segmentationLeft b.size (total t rest) (seg b (t :: rest)) = fun _ ↦ b.label := by
  rw [seg_cons]
  exact segmentationLeft_append b.size (total t rest) _ _ _

/-- Peeling the head block leaves the tail's block segmentation on the rest. -/
@[simp] theorem segmentationRight_seg (b t : SegmentRegionBlock A c₀ M)
    (rest : List (SegmentRegionBlock A c₀ M)) :
    segmentationRight b.size (total t rest) (seg b (t :: rest)) = seg t rest := by
  rw [seg_cons]
  exact segmentationRight_append b.size (total t rest) _ _ _

/-- The multiplicity profile of the block segmentation: each block contributes `size + 1`
occurrences of its own label. -/
def multiplicityProfile : (b : SegmentRegionBlock A c₀ M) →
    (rest : List (SegmentRegionBlock A c₀ M)) → (Fin M → ℕ)
  | b, [] => fun t ↦ if t = b.label then b.size + 1 else 0
  | b, u :: rest => (fun t ↦ if t = b.label then b.size + 1 else 0) + multiplicityProfile u rest

@[simp] theorem multiplicityProfile_nil (b : SegmentRegionBlock A c₀ M) :
    multiplicityProfile b [] = fun t ↦ if t = b.label then b.size + 1 else 0 := rfl

@[simp] theorem multiplicityProfile_cons (b u : SegmentRegionBlock A c₀ M)
    (rest : List (SegmentRegionBlock A c₀ M)) :
    multiplicityProfile b (u :: rest) =
      (fun t ↦ if t = b.label then b.size + 1 else 0) + multiplicityProfile u rest := rfl

/-- **The multiplicities of the block segmentation are computed.**  Nothing is sorted; the
profile is read off the block sizes and labels. -/
theorem multiplicity_seg :
    ∀ (b : SegmentRegionBlock A c₀ M) (rest : List (SegmentRegionBlock A c₀ M)),
      WordType.multiplicity (seg b rest) = multiplicityProfile b rest
  | b, [] => by
      rw [seg_nil, multiplicityProfile_nil]
      funext t
      exact WordType.multiplicity_const (b.size + 1) b.label t
  | b, t :: rest => by
      rw [seg_cons, multiplicityProfile_cons,
        WordType.multiplicity_cast (total_cons_succ b t rest)
          (Fin.append (fun _ : Fin (b.size + 1) ↦ b.label) (seg t rest)),
        WordType.multiplicity_append, multiplicity_seg t rest]
      congr 1
      funext a
      exact WordType.multiplicity_const (b.size + 1) b.label a

/-- **The blocks account for exactly the word's positions.**  Both segmentations have the same
multiplicity profile, and the total mass of a profile is the length of the word. -/
theorem total_eq_of_multiplicityProfile {N : ℕ} (b : SegmentRegionBlock A c₀ M)
    (rest : List (SegmentRegionBlock A c₀ M)) (w : Fin (N + 1) → Fin M)
    (h : multiplicityProfile b rest = WordType.multiplicity w) :
    total b rest = N := by
  have h1 : ∑ t, WordType.multiplicity (seg b rest) t = total b rest + 1 :=
    WordType.sum_multiplicity (seg b rest)
  have h2 : ∑ t, WordType.multiplicity w t = N + 1 := WordType.sum_multiplicity w
  rw [multiplicity_seg, h] at h1
  omega

/-- **A word with the block multiplicity profile is a position relabelling of the block
segmentation.**  The committed `WordType.positionPermOfSameMultiplicity` does the work; the
permutation is produced, not searched for. -/
theorem exists_perm_comp_eq_seg (b : SegmentRegionBlock A c₀ M)
    (rest : List (SegmentRegionBlock A c₀ M))
    (w : Fin (total b rest + 1) → Fin M)
    (hmult : WordType.multiplicity w = multiplicityProfile b rest) :
    ∃ σ : Equiv.Perm (Fin (total b rest + 1)), w ∘ ⇑σ = seg b rest :=
  ⟨WordType.positionPermOfSameMultiplicity (seg b rest) w
      (by rw [multiplicity_seg, hmult]),
    WordType.positionPermOfSameMultiplicity_map (seg b rest) w
      (by rw [multiplicity_seg, hmult])⟩

end SegmentRegionBlock

/-! ## The position permutation, in the splitting-power spelling -/

section Position

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The committed uniformity isomorphism, in the `segmentedLocalizedSplittingPower` spelling.**

`segmentedLocalizedFiber_isomorphic_position` (`MatrixMultiplication/SegmentedFiberUniformity.lean`)
states it as a fiber followed by a selection; the division and the value law both speak
`segmentedLocalizedSplittingPower`.  The committed
`coarseningFiber_select_eq_segmentedLocalizedSplittingPower` converts, and that is the whole
content of this corollary. -/
theorem Tensor.Isomorphic.segmentedLocalizedSplittingPower_position
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Isomorphic (P.segmentedLocalizedSplittingPower f n m seg profile target).realize
      (P.segmentedLocalizedSplittingPower f n m (seg ∘ ⇑σ) profile
        (positionRelabelBlockAddress B n σ target)).realize := by
  rw [← PartitionedTensor.coarseningFiber_select_eq_segmentedLocalizedSplittingPower,
    ← PartitionedTensor.coarseningFiber_select_eq_segmentedLocalizedSplittingPower]
  exact segmentedLocalizedFiber_isomorphic_position P f n m seg profile target σ

end Position

end AlgebraicComplexity
