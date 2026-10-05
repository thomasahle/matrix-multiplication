/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivision
import AlgebraicComplexity.Tensor.PositiveWordAppendConst

set_option autoImplicit false

/-!
# The regional pieces of a coarse target

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  The regional division
(`MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean`) asks, at every peel, for the two
regional coarse targets and for the parent target to be their concatenation.  That obligation is
**not** discharged by defining the parent target as a concatenation: the parent target of
`[duan2023faster]`'s section 6.3 leaf is the coarse address of the (position-relabelled) reference
word, fixed long before any region is peeled.  It has to be *proved* that its regional pieces are
the constant words the per-cell weights are stated at.

Two observations make that routine.

* Splitting is free.  `positiveWordAppendEquiv` is an equivalence, so every word **is** the
  concatenation of its two pieces (`Equiv.apply_symm_apply`); the concatenation conjunct of
  `SegmentedRegionalWeights` costs nothing once the pieces are taken to be those.
* The content is that a piece is *constant*.  A region of the section 6.3 leaf sits inside one
  coarse cell, so every position it sees carries the same coarse letter on each leg; the piece is
  then `positiveWordConst` of that letter, and that is what
  `positiveWordAppendEquiv_symm_fst_eq_const` says.

`regionIndexLeft` and `regionIndexRight` name the position embeddings that `segmentationLeft` and
`segmentationRight` already use, so "every position this region sees" is literally the region's
index set and the two readings cannot drift apart
(`segmentationLeft_eq_comp_regionIndexLeft`).

`Tensor/PositiveWordAppendConst.lean`'s `positiveWordAppend_const` is the converse direction, for a
target that is constant on the *whole* word; it is not what a fifteen-cell leaf needs, whose target
is constant only inside each region.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-! ## The positions a region sees -/

section RegionIndex

variable {M : ℕ}

/-- The positions of the left region, inside the parent's position set. -/
def regionIndexLeft (n p : ℕ) (i : Fin (n + 1)) : Fin (n + p + 1 + 1) :=
  Fin.cast (by omega) (Fin.castAdd (p + 1) i)

/-- The positions of the right region, inside the parent's position set. -/
def regionIndexRight (n p : ℕ) (j : Fin (p + 1)) : Fin (n + p + 1 + 1) :=
  Fin.cast (by omega) (Fin.natAdd (n + 1) j)

/-- The left region's segmentation is the parent segmentation read on the left region's
positions. -/
theorem segmentationLeft_eq_comp_regionIndexLeft (n p : ℕ)
    (seg : Fin (n + p + 1 + 1) → Fin M) :
    segmentationLeft n p seg = seg ∘ regionIndexLeft n p := rfl

/-- The right region's segmentation is the parent segmentation read on the right region's
positions. -/
theorem segmentationRight_eq_comp_regionIndexRight (n p : ℕ)
    (seg : Fin (n + p + 1 + 1) → Fin M) :
    segmentationRight n p seg = seg ∘ regionIndexRight n p := rfl

end RegionIndex

/-! ## A region that sees only one letter -/

namespace Tensor

/-- **The left regional piece of a word that is constant on the left region is constant.**

Proof sketch: `positiveWordAppendEquiv` is an equivalence, so re-appending the two pieces returns
the word (`Equiv.apply_symm_apply`).  Comparing the left piece with `positiveWordConst a n` is
then a pointwise question, and `positiveWordEquiv_append` reads the re-appended word at
`regionIndexLeft n p i` as `Fin.append` at `Fin.castAdd (p + 1) i` --- the two position
embeddings agree by `Fin.ext` and `omega` on the index arithmetic --- so `Fin.append_left` returns
the left piece's letter at `i`, which the hypothesis says is `a`. -/
theorem positiveWordAppendEquiv_symm_fst_eq_const {I : Type w} (n p : ℕ)
    (word : PositiveWord I (n + p + 1)) (a : I)
    (h : ∀ i : Fin (n + 1),
      positiveWordEquiv I (n + p + 1) word (regionIndexLeft n p i) = a) :
    ((positiveWordAppendEquiv I n p).symm word).1 = positiveWordConst a n := by
  have happend : positiveWordAppend ((positiveWordAppendEquiv I n p).symm word).1 p
      ((positiveWordAppendEquiv I n p).symm word).2 = word := by
    rw [← positiveWordAppendEquiv_apply]
    exact (positiveWordAppendEquiv I n p).apply_symm_apply word
  apply (positiveWordEquiv I n).injective
  funext i
  rw [positiveWordEquiv_const]
  have hi := h i
  rw [← happend, positiveWordEquiv_append, Function.comp_apply,
    show Fin.cast (show n + p + 1 + 1 = n + 1 + (p + 1) from by omega)
        (regionIndexLeft n p i) = Fin.castAdd (p + 1) i from Fin.ext (by simp [regionIndexLeft]),
    Fin.append_left] at hi
  exact hi

/-- **The right regional piece of a word that is constant on the right region is constant.** -/
theorem positiveWordAppendEquiv_symm_snd_eq_const {I : Type w} (n p : ℕ)
    (word : PositiveWord I (n + p + 1)) (a : I)
    (h : ∀ j : Fin (p + 1),
      positiveWordEquiv I (n + p + 1) word (regionIndexRight n p j) = a) :
    ((positiveWordAppendEquiv I n p).symm word).2 = positiveWordConst a p := by
  have happend : positiveWordAppend ((positiveWordAppendEquiv I n p).symm word).1 p
      ((positiveWordAppendEquiv I n p).symm word).2 = word := by
    rw [← positiveWordAppendEquiv_apply]
    exact (positiveWordAppendEquiv I n p).apply_symm_apply word
  apply (positiveWordEquiv I p).injective
  funext j
  rw [positiveWordEquiv_const]
  have hj := h j
  rw [← happend, positiveWordEquiv_append, Function.comp_apply,
    show Fin.cast (show n + p + 1 + 1 = n + 1 + (p + 1) from by omega)
        (regionIndexRight n p j) = Fin.natAdd (n + 1) j from Fin.ext (by simp [regionIndexRight]),
    Fin.append_right] at hj
  exact hj

end Tensor

/-! ## The concatenation obligation, discharged -/

section BlockAddress

variable {B : Leg → Type x}

/-- **The concatenation obligation of a regional division, at a region that sees one letter per
leg.**

The head piece is the constant word of that letter --- which is the shape the per-cell weights are
stated at --- and the tail piece is whatever the split leaves; the parent target is untouched.

Proof sketch: leg by leg.  `positiveWordAppendEquiv_symm_fst_eq_const` at the hypothesis `h c`
rewrites the head piece into `positiveWordConst (a c) n`, and `Equiv.apply_symm_apply` for
`positiveWordAppendEquiv` says the parent leg word is the concatenation of its own two pieces.  So
the equation is an identity, not a construction: nothing is chosen and the parent target is never
redefined. -/
theorem blockAddress_eq_append_const_of_regionConst (n p : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) (n + p + 1)))
    (a : ∀ c, B c)
    (h : ∀ (c : Leg) (i : Fin (n + 1)),
      positiveWordEquiv (B c) (n + p + 1) (target c) (regionIndexLeft n p i) = a c) :
    ∀ c, target c = positiveWordAppend (positiveWordConst (a c) n) p
      ((positiveWordAppendEquiv (B c) n p).symm (target c)).2 := by
  intro c
  rw [← Tensor.positiveWordAppendEquiv_symm_fst_eq_const n p (target c) (a c) (h c),
    ← positiveWordAppendEquiv_apply]
  exact ((positiveWordAppendEquiv (B c) n p).apply_symm_apply (target c)).symm

end BlockAddress

end AlgebraicComplexity
