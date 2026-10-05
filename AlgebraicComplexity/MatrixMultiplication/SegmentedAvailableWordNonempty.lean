/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWord

set_option autoImplicit false

/-!
# Segmented available words exist

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `SegmentedAvailableWord seg α`
(`MatrixMultiplication/SegmentedAvailableWord.lean`) is the subtype of words whose empirical type
on each segment is the prescribed `α t` --- `[duan2023faster]`'s `α̃_t` of `hole_lemma.tex:40`.

Every Hole-Lemma statement that counts available words carries
`0 < Fintype.card (SegmentedAvailableWord seg α)` as a **hypothesis**, at all of its occurrences in
the tree, and nowhere as a conclusion; the union bound `exists_segmented_shuffles_avoiding` and the
whole hole-budget arithmetic are vacuous without it.  This module supplies the converse, which is
the obvious one: the prescribed types are realized as soon as they *are* types, i.e. as soon as
each `α t` has total mass the size of segment `t`.  In `[duan2023faster]` that is true by
construction, since `α̃_t` is the split profile of the `t`-th component.

Nothing new is proved.  `WordType.typeClass_nonempty` (`Combinatorics/WordType.lean`) realizes one
type on one segment, `Finset.equivFin` numbers that segment's positions, and the segments are glued
by reading each position's own segment.  The statement is given in the segmented spelling so that
clients never have to re-index.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe w

section Segmented

variable {I : Type w} [Fintype I] [DecidableEq I] {n m : ℕ}

/-- **A word with prescribed empirical types on every segment.**

The hypothesis is the only thing that can be asked: on segment `t` there are exactly
`(univ.filter fun i ↦ seg i = t).card` positions to distribute, so `α t` must have that mass.
Given it, the word is built segment by segment --- `WordType.typeClass_nonempty` on the segment's
own positions, numbered by `Finset.equivFin` --- and a position simply reads the word of its own
segment. -/
theorem exists_word_segmentMultiplicity (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (hsize : ∀ t, ∑ a, α t a = (Finset.univ.filter fun i ↦ seg i = t).card) :
    ∃ word : Fin (n + 1) → I, ∀ t, segmentMultiplicity seg word t = α t := by
  have hI : Nonempty I := by
    by_contra hcon
    haveI : IsEmpty I := not_nonempty_iff.mp hcon
    have h0 := hsize (seg 0)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h0
    have hmem : (0 : Fin (n + 1)) ∈ Finset.univ.filter fun i ↦ seg i = seg 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hpos : 0 < (Finset.univ.filter fun i ↦ seg i = seg 0).card :=
      Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  haveI : Nonempty I := hI
  have hstep : ∀ t : Fin m, ∃ f : Fin (n + 1) → I,
      ∀ a : I, (Finset.univ.filter fun i ↦ seg i = t ∧ f i = a).card = α t a := by
    intro t
    set S : Finset (Fin (n + 1)) := Finset.univ.filter fun i ↦ seg i = t with hSdef
    have hSmem : ∀ i : Fin (n + 1), i ∈ S ↔ seg i = t := by
      intro i
      rw [hSdef, Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
    have hmem : α t ∈ WordType.types I S.card := WordType.mem_types.mpr (hsize t)
    obtain ⟨w, hw⟩ := WordType.typeClass_nonempty (α t) hmem
    have hmul : WordType.multiplicity w = α t := WordType.mem_typeClass.mp hw
    set g : Fin (n + 1) → I :=
      fun i ↦ if h : i ∈ S then w (S.equivFin ⟨i, h⟩) else Classical.arbitrary I with hgdef
    have hg : ∀ (i : Fin (n + 1)) (h : i ∈ S), g i = w (S.equivFin ⟨i, h⟩) := by
      intro i h
      rw [hgdef]
      exact dif_pos h
    refine ⟨g, fun a ↦ ?_⟩
    have hcard : (Finset.univ.filter fun i ↦ seg i = t ∧ g i = a).card =
        (Finset.univ.filter fun k : Fin S.card ↦ w k = a).card := by
      refine Finset.card_bij'
        (fun i hi ↦ S.equivFin ⟨i, (hSmem i).mpr (Finset.mem_filter.mp hi).2.1⟩)
        (fun k _ ↦ (S.equivFin.symm k).1) ?_ ?_ ?_ ?_
      · intro i hi
        have hiS : i ∈ S := (hSmem i).mpr (Finset.mem_filter.mp hi).2.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [← hg i hiS]
        exact (Finset.mem_filter.mp hi).2.2
      · intro k hk
        have hkS : (S.equivFin.symm k).1 ∈ S := (S.equivFin.symm k).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hSmem _).mp hkS, ?_⟩
        rw [hg _ hkS]
        have hcoe : (⟨(S.equivFin.symm k).1, hkS⟩ : {x // x ∈ S}) = S.equivFin.symm k :=
          Subtype.ext rfl
        rw [hcoe, Equiv.apply_symm_apply]
        exact (Finset.mem_filter.mp hk).2
      · intro i hi
        simp
      · intro k hk
        exact (congrArg (S.equivFin) (Subtype.ext rfl)).trans (S.equivFin.apply_symm_apply k)
    rw [hcard]
    calc (Finset.univ.filter fun k : Fin S.card ↦ w k = a).card
        = Fintype.card {k : Fin S.card // w k = a} := (Fintype.card_subtype _).symm
      _ = WordType.multiplicity w a := (WordType.multiplicity_eq_card_fiber w a).symm
      _ = α t a := by rw [hmul]
  choose f hf using hstep
  refine ⟨fun i ↦ f (seg i) i, fun t ↦ ?_⟩
  funext a
  show (Finset.univ.filter fun i ↦ seg i = t ∧ f (seg i) i = a).card = α t a
  have hfilter : (Finset.univ.filter fun i ↦ seg i = t ∧ f (seg i) i = a) =
      (Finset.univ.filter fun i ↦ seg i = t ∧ f t i = a) := by
    refine Finset.filter_congr ?_
    intro i _
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← h1]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h1]
      exact h2
  rw [hfilter]
  exact hf t a

/-- **The segmented available words are nonempty** when each segment type has the segment's mass. -/
theorem segmentedAvailableWord_nonempty (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (hsize : ∀ t, ∑ a, α t a = (Finset.univ.filter fun i ↦ seg i = t).card) :
    Nonempty (SegmentedAvailableWord seg α) := by
  obtain ⟨word, hword⟩ := exists_word_segmentMultiplicity seg α hsize
  refine ⟨⟨(positiveWordEquiv I n).symm word, ?_⟩⟩
  intro t
  rw [Equiv.apply_symm_apply]
  exact hword t

/-- **`hpos`, as a conclusion.**  The hypothesis carried by every hole-budget statement, discharged
from the one condition that can be asked of the segment types. -/
theorem card_segmentedAvailableWord_pos (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (hsize : ∀ t, ∑ a, α t a = (Finset.univ.filter fun i ↦ seg i = t).card) :
    0 < Fintype.card (SegmentedAvailableWord seg α) :=
  Fintype.card_pos_iff.mpr (segmentedAvailableWord_nonempty seg α hsize)

end Segmented

end AlgebraicComplexity
