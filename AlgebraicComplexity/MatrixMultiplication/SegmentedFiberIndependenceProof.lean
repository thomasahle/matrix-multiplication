/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.DomainWordShuffle
import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWordShuffle

/-!
# Claim 3 for segmented available blocks, proved

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `SegmentedAvailableWordShuffle.lean:129`
states `SegmentedFiberIndependence` --- the segmented form of Claim 3 of

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, §5 (`hole_lemma.tex`) (`[duan2023faster]`)

--- and carries it as a hypothesis, because whether the *product* group
`Sym[n_1] x ... x Sym[n_m]` acting with independent per-component shuffles is the group the Hole
Lemma's union bound needs was left open.  This module discharges it: `segmentedFiberIndependence`
proves the statement for **every** segmentation `seg` and every per-segment type `α`, with no side
condition.

## The proof

`hole_lemma.tex:115-121` proves Claim 3 by one displayed count: the number of `φ ∈ G` carrying
one
available block to another is `∏_t ∏_{k'} (α̃_t(k') n_t)!`, visibly independent of both
blocks.
That is the order of a Young subgroup, and the mechanised form of the same argument is

* the fibre of a target factors over the segments --- `comp_segmentPermToPerm_eq_iff` turns
  `v ∘ segmentPermToPerm seg φ = w` into a condition on each `φ t` separately, so
  `filter_segmentedAvailableWordShuffle_eq_piFinset` presents the fibre as a
  `Fintype.piFinset` of per-segment transporters, exactly as
  `HoleRepair.UniformOnParts.pi` (`Combinatorics/ProductUniformOnParts.lean:51`) does for the
  product family;
* each factor is a translate of a stabilizer --- `card_domainTransporter_eq_card_stabilizer`
  (`Combinatorics/DomainWordShuffle.lean`), applied at the permutation supplied by
  `domainPermOfSameFiberCard` from the two blocks' *equal* segment types.

No factorial is computed: as in the committed pooled case
(`RestrictedSplittingShuffle.lean:205`, `Combinatorics/ShufflingGroup.lean:102`) only the
independence of the target is used.  Nothing here is probabilistic; `[duan2023faster]`'s
"uniformly random `φ ∈ G`" is exact `Finset.card` counting throughout, and no independence
estimate enters.

## Why the segmented case is not the committed pooled one

`WordShuffle.transporter` (`Combinatorics/ShufflingGroup.lean:271`) permutes `Fin n`, whereas
`[duan2023faster]`'s group permutes the *fibres of the segmentation*, `{i // seg i = t}`
(`SegmentedAvailableWord.lean:88`).  `Combinatorics/DomainWordShuffle.lean` restates the two facts
about transporters over an arbitrary finite position domain; this module supplies the segmentation
bookkeeping (`segmentRestrict`, `card_fiber_segmentRestrict`) that identifies the per-segment
letter fibres with the committed `segmentMultiplicity`.
-/

set_option autoImplicit false

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## Restricting a word to one segment -/

section Restrict

variable {I : Type w} {n m : ℕ}

/-- **The sub-word carried by one segment.**  The shuffling group's factor at `t` acts on the
positions `{i // seg i = t}`, and this is the word it sees. -/
def segmentRestrict (seg : Fin n → Fin m) (word : Fin n → I) (t : Fin m) :
    {i // seg i = t} → I := fun i ↦ word i.1

@[simp] theorem segmentRestrict_apply (seg : Fin n → Fin m) (word : Fin n → I) (t : Fin m)
    (i : {i // seg i = t}) : segmentRestrict seg word t i = word i.1 := rfl

end Restrict

section FiberCard

variable {I : Type w} [DecidableEq I] {n m : ℕ}

/-- **The letter fibres of the sub-word on segment `t` are counted by the segmented empirical
type.**  This is the bridge to `segmentMultiplicity` (`SegmentedSplitRestriction.lean:55`), and it
is what turns "the two blocks are available for the same `α`" into the hypothesis of
`WordShuffle.domainPermOfSameFiberCard`. -/
theorem card_fiber_segmentRestrict (seg : Fin n → Fin m) (word : Fin n → I) (t : Fin m) (a : I)
  :
    Fintype.card {j // segmentRestrict seg word t j = a} = segmentMultiplicity seg word t a := by
  have e : {j : {i // seg i = t} // segmentRestrict seg word t j = a} ≃
      {i : Fin n // seg i = t ∧ word i = a} :=
    { toFun := fun j ↦ ⟨j.1.1, j.1.2, j.2⟩
      invFun := fun i ↦ ⟨⟨i.1, i.2.1⟩, i.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  rfl

end FiberCard

/-! ## The segmented shuffle condition, segment by segment -/

section Factorisation

variable {I : Type w} {n m : ℕ}

/-- **A segmented shuffle moves a position inside its own segment, by that segment's factor.**
`segmentPermToPerm` (`SegmentedAvailableWord.lean:102`) is Mathlib's `Equiv.ofFiberEquiv` at
`f = g = seg`, so this is `rfl`. -/
@[simp] theorem segmentPermToPerm_apply (seg : Fin (n + 1) → Fin m) (φ : SegmentPerm seg)
    (i : Fin (n + 1)) : segmentPermToPerm seg φ i = (φ (seg i) ⟨i, rfl⟩).1 := rfl

/-- **The segmented shuffle condition factors over the segments.**  This is the step that makes
`[duan2023faster]`'s count a product: the group is `Sym[n_1] x ... x Sym[n_m]`, and a shuffle
carries `v` to `w` exactly when each factor carries `v`'s sub-word on its segment to `w`'s. -/
theorem comp_segmentPermToPerm_eq_iff (seg : Fin (n + 1) → Fin m) (φ : SegmentPerm seg)
    (v w : Fin (n + 1) → I) :
    v ∘ segmentPermToPerm seg φ = w ↔
      ∀ t : Fin m, segmentRestrict seg v t ∘ φ t = segmentRestrict seg w t := by
  constructor
  · intro hv t
    funext j
    obtain ⟨i, rfl⟩ := j
    exact congrFun hv i
  · intro hs
    funext i
    exact congrFun (hs (seg i)) ⟨i, rfl⟩

end Factorisation

/-! ## The fibre of the segmented shuffling action -/

section Fiber

variable {I : Type w} [DecidableEq I] {n m : ℕ}

/-- The action written out on the underlying position words.  Segmented analogue of the opening
step of `card_availableWordShuffle_fiber` (`RestrictedSplittingShuffle.lean:210`). -/
theorem segmentedAvailableWordShuffle_eq_iff (seg : Fin (n + 1) → Fin m)
  (α : Fin m → I → ℕ)
    (φ : SegmentPerm seg) (a b : SegmentedAvailableWord seg α) :
    segmentedAvailableWordShuffle seg α φ a = b ↔
      positiveWordEquiv I n a.1 ∘ segmentPermToPerm seg φ = positiveWordEquiv I n b.1 := by
  constructor
  · intro hφ
    have hval : positiveWordPositionEquiv I n (segmentPermToPerm seg φ) a.1 = b.1 := by
      rw [← segmentedAvailableWordShuffle_val seg α φ a, hφ]
    rw [← hval, positiveWordEquiv_position_apply]
  · intro hφ
    refine Subtype.ext ?_
    apply (positiveWordEquiv I n).injective
    rw [segmentedAvailableWordShuffle_val, positiveWordEquiv_position_apply]
    exact hφ

/-- **The fibre over a target is the product of the per-segment transporters.**  The shape mirrors
`filter_piCongrRight_eq_piFinset` (`Combinatorics/ProductUniformOnParts.lean:51`); here the product
structure comes from the segmentation rather than from a product of part sets. -/
theorem filter_segmentedAvailableWordShuffle_eq_piFinset (seg : Fin (n + 1) → Fin m)
    (α : Fin m → I → ℕ) (a b : SegmentedAvailableWord seg α) :
    (Finset.univ.filter fun φ : SegmentPerm seg ↦
        segmentedAvailableWordShuffle seg α φ a = b) =
      Fintype.piFinset fun t : Fin m ↦ WordShuffle.domainTransporter
        (segmentRestrict seg (positiveWordEquiv I n a.1) t)
        (segmentRestrict seg (positiveWordEquiv I n b.1) t) := by
  ext φ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, hφ⟩
    exact Fintype.mem_piFinset.2 fun t ↦
      WordShuffle.mem_domainTransporter.2
        ((comp_segmentPermToPerm_eq_iff seg φ _ _).1
          ((segmentedAvailableWordShuffle_eq_iff seg α φ a b).1 hφ) t)
  · intro hφ
    refine ⟨Finset.mem_univ _, (segmentedAvailableWordShuffle_eq_iff seg α φ a b).2 ?_⟩
    exact (comp_segmentPermToPerm_eq_iff seg φ _ _).2 fun t ↦
      WordShuffle.mem_domainTransporter.1 (Fintype.mem_piFinset.1 hφ t)

/-- **The fibre count of the segmented shuffling action does not mention the target.**

This is `[duan2023faster]`'s `∏_t ∏_{k'} (α̃_t(k') n_t)!` (`hole_lemma.tex:116`) with the
factorials left uncomputed: the value is a product over segments of per-segment *stabilizer*
sizes, all taken at the source block. -/
theorem card_segmentedAvailableWordShuffle_fiber (seg : Fin (n + 1) → Fin m)
    (α : Fin m → I → ℕ) (a b : SegmentedAvailableWord seg α) :
    (Finset.univ.filter fun φ : SegmentPerm seg ↦
        segmentedAvailableWordShuffle seg α φ a = b).card =
      ∏ t : Fin m, (WordShuffle.domainTransporter
        (segmentRestrict seg (positiveWordEquiv I n a.1) t)
        (segmentRestrict seg (positiveWordEquiv I n a.1) t)).card := by
  refine (congrArg Finset.card
    (filter_segmentedAvailableWordShuffle_eq_piFinset seg α a b)).trans ?_
  refine (Fintype.card_piFinset _).trans ?_
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  have hcard : ∀ c : I,
      Fintype.card {j // segmentRestrict seg (positiveWordEquiv I n b.1) t j = c} =
        Fintype.card {j // segmentRestrict seg (positiveWordEquiv I n a.1) t j = c} :=
    fun c ↦
      (card_fiber_segmentRestrict seg (positiveWordEquiv I n b.1) t c).trans <|
        (congrFun (b.2 t) c).trans <|
          (congrFun (a.2 t) c).symm.trans
            (card_fiber_segmentRestrict seg (positiveWordEquiv I n a.1) t c).symm
  exact WordShuffle.card_domainTransporter_eq_card_stabilizer _ _
    (WordShuffle.domainPermOfSameFiberCard _ _ hcard)
    (WordShuffle.domainPermOfSameFiberCard_map _ _ hcard)

/-- **`[duan2023faster]`, `hole_lemma.tex` Claim 3, segmented.**

For a fixed available block, the number of segmented shuffles reaching a given available block is
the same for every target.  It holds for every segmentation and every per-segment type, with no
side condition: two blocks available for the same `α` have, segment by segment, the same letter
multiplicities, so they differ by a permutation inside each segment.

This discharges the hypothesis `SegmentedFiberIndependence`
(`SegmentedAvailableWordShuffle.lean:129`) wherever it is assumed. -/
theorem segmentedFiberIndependence (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) :
    SegmentedFiberIndependence seg α := fun a b b' ↦
  (card_segmentedAvailableWordShuffle_fiber seg α a b).trans
    (card_segmentedAvailableWordShuffle_fiber seg α a b').symm

end Fiber

end AlgebraicComplexity
