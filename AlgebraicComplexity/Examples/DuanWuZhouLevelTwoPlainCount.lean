/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLegMarginal

/-!
# The level-two counts at the plain fifteen-block partition

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` §6.3 hashes the *plain* power of the
coarse Coppersmith--Winograd square, not its six-orientation symmetrization: `sym₆` never touches
the hashed tensor, and the `m ^ 6` copies come from the distribution isomorphism
`sym₆ (⊕_m L) ≅ ⊕_{m ^ 6} sym₆ L`.  So the alphabet is the fifteen coarse addresses
`cwSquareSupport`, and a block word of the positive power is literally a word over them.

This module is the fifteen-letter counterpart of
`Examples/DuanWuZhouLevelTwoLegDigitCount.lean` and
`Examples/DuanWuZhouLevelTwoTargetWordCount.lean`, with the `Fin 6` product and the sixth powers
deleted.  Two things get simpler, not just smaller:

* over fifteen letters, *typicality is a single joint type class* --- `dwz63PlainTypicalWords` is
  `WordType.typeClass` transported through `positiveWordEquiv`.  The `hwords` hypothesis of
  `PartitionHashEncoding.card_legFiber_legalTargets_le_card_typedWordMapFiber` is therefore free,
  and no pigeonhole and no joint-type refinement are needed anywhere;
* the six-fold decoupling collapses: `WordType.card_targetType_mul_card_typedWordMapFiber` gives
  the leg fiber in one step, with no product over orientations.

## The profile on the support

`dwz63AlphaAddress` is committed on all of `CWSquareAddress`; the plain alphabet is the subtype
`cwSquareSupport`.  `dwz63PlainAlpha` is its restriction, and `mappedType_subtype_of_vanishing` ---
a general fact about restricting a profile to any finite set carrying its support --- says that
restriction changes no pushforward.  So `profileMass_dwz63PlainAlpha` and
`mappedType_dwz63PlainLegRead` inherit the committed `profileMass_dwz63AlphaAddress` and
`mappedType_legRead_dwz63AlphaAddress` verbatim, and in particular the three leg marginals are
still `dwz63AlphaMarginal`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## Restricting a profile to a set carrying its support -/

/-- **Restricting a profile to a finite set containing its support changes no pushforward.**
Both sides are the same sum of indicators; the terms dropped are zero. -/
theorem mappedType_subtype_of_vanishing {A B : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] (s : Finset A) (f : A → B) (a : A → ℕ)
    (hvanish : ∀ x, a x ≠ 0 → x ∈ s) (b : B) :
    WordType.mappedType (fun y : s ↦ f y.val) (fun y : s ↦ a y.val) b =
      WordType.mappedType f a b := by
  classical
  rw [WordType.mappedType_eq_sum_ite, WordType.mappedType_eq_sum_ite]
  rw [Finset.sum_coe_sort s fun x ↦ if f x = b then a x else 0]
  refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm.symm
  · intro x _ hx
    have hax : a x = 0 := by
      by_contra hne
      exact hx (hvanish x hne)
    simp [hax]

/-! ## The fifteen-cell profile on the plain alphabet -/

/-- **The section 6.3 distribution on the plain fifteen-letter alphabet.** -/
noncomputable def dwz63PlainAlpha : cwSquareSupport → ℕ :=
  fun s ↦ dwz63AlphaAddress s.val

/-- Reading one leg of a plain block letter. -/
def dwz63PlainLegRead (c : Leg) : cwSquareSupport → Fin 5 :=
  fun s ↦ s.val c

theorem profileMass_dwz63PlainAlpha :
    WordType.profileMass dwz63PlainAlpha = 100000000 := by
  classical
  have hsum : ∑ s : cwSquareSupport, dwz63AlphaAddress s.val =
      ∑ a : CWSquareAddress, dwz63AlphaAddress a := by
    rw [Finset.sum_coe_sort cwSquareSupport dwz63AlphaAddress]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    by_contra hne
    exact hx (mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero hne)
  show ∑ s : cwSquareSupport, dwz63AlphaAddress s.val = 100000000
  rw [hsum]
  exact profileMass_dwz63AlphaAddress

/-- **The three leg marginals of the plain profile are the committed ones.** -/
theorem mappedType_dwz63PlainLegRead (c : Leg) :
    WordType.mappedType (dwz63PlainLegRead c) dwz63PlainAlpha = dwz63AlphaMarginal c := by
  classical
  funext d
  rw [show WordType.mappedType (dwz63PlainLegRead c) dwz63PlainAlpha d =
      WordType.mappedType (fun a : CWSquareAddress ↦ a c) dwz63AlphaAddress d from
    mappedType_subtype_of_vanishing cwSquareSupport (fun a : CWSquareAddress ↦ a c)
      dwz63AlphaAddress (fun _ h ↦ mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero h) d]
  rw [mappedType_legRead_dwz63AlphaAddress]

/-- The repeated form. -/
theorem mappedType_dwz63PlainLegRead_proportionalCounts (c : Leg) (t : ℕ) :
    WordType.mappedType (dwz63PlainLegRead c)
        (WordType.proportionalCounts dwz63PlainAlpha t) =
      WordType.proportionalCounts (dwz63AlphaMarginal c) t := by
  rw [mappedType_proportionalCounts, mappedType_dwz63PlainLegRead]

/-! ## The two counts -/

/-- **`N_α` at the plain partition**: the number of typical block words of length `n + 1`.  Over
fifteen letters this is a single multinomial type class --- no product, no pigeonhole. -/
noncomputable def dwz63PlainJointCount (n t : ℕ) : ℕ :=
  (WordType.typeClass (n + 1) (WordType.proportionalCounts dwz63PlainAlpha t)).card

/-- **`N_c` at the plain partition**: the leg-`c` words of the typical marginal type. -/
noncomputable def dwz63PlainLegCount (c : Leg) (n t : ℕ) : ℕ :=
  (WordType.typeClass (n + 1) (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card

/-- At the forced word length the repeated plain profile is a legal type. -/
theorem proportionalCounts_dwz63PlainAlpha_mem_types {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    WordType.proportionalCounts dwz63PlainAlpha t ∈
      WordType.types (cwSquareSupport) (n + 1) := by
  rw [WordType.mem_types, hn]
  show ∑ s : cwSquareSupport, dwz63PlainAlpha s * t = 100000000 * t
  rw [← Finset.sum_mul,
    show (∑ s : cwSquareSupport, dwz63PlainAlpha s) =
      WordType.profileMass dwz63PlainAlpha from rfl,
    profileMass_dwz63PlainAlpha]

theorem dwz63PlainJointCount_pos {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    0 < dwz63PlainJointCount n t := by
  rw [dwz63PlainJointCount, Finset.card_pos]
  exact WordType.typeClass_nonempty _ (proportionalCounts_dwz63PlainAlpha_mem_types hn)

theorem dwz63PlainLegCount_pos (c : Leg) {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    0 < dwz63PlainLegCount c n t := by
  have hmem : WordType.proportionalCounts (dwz63AlphaMarginal c) t ∈
      WordType.types (Fin 5) (n + 1) := by
    rw [WordType.mem_types, hn]
    show ∑ i, dwz63AlphaMarginal c i * t = 100000000 * t
    rw [← Finset.sum_mul,
      show (∑ i, dwz63AlphaMarginal c i) = WordType.profileMass (dwz63AlphaMarginal c) from rfl,
      profileMass_dwz63AlphaMarginal]
  rw [dwz63PlainLegCount, Finset.card_pos]
  exact WordType.typeClass_nonempty _ hmem

/-! ## The leg fiber at a single joint type, in one step -/

/-- **The exact leg-fiber identity at the plain partition.**

`N_c · #(typed leg fiber) = N_α`, directly from
`WordType.card_targetType_mul_card_typedWordMapFiber` --- the six-fold decoupling of the
`15 ^ 6` route collapses to a single application. -/
theorem dwz63PlainLegCount_mul_card_typedWordMapFiber (c : Leg) (n t : ℕ)
    {x : Fin (n + 1) → Fin 5}
    (hx : WordType.multiplicity x = WordType.proportionalCounts (dwz63AlphaMarginal c) t) :
    dwz63PlainLegCount c n t *
        (WordType.typedWordMapFiber (dwz63PlainLegRead c)
          (WordType.proportionalCounts dwz63PlainAlpha t) x).card =
      dwz63PlainJointCount n t := by
  have hmem : x ∈ WordType.typeClass (n + 1)
      (WordType.mappedType (dwz63PlainLegRead c)
        (WordType.proportionalCounts dwz63PlainAlpha t)) := by
    rw [WordType.mem_typeClass, mappedType_dwz63PlainLegRead_proportionalCounts]
    exact hx
  have h := WordType.card_targetType_mul_card_typedWordMapFiber (dwz63PlainLegRead c)
    (WordType.proportionalCounts dwz63PlainAlpha t) x hmem
  rw [mappedType_dwz63PlainLegRead_proportionalCounts] at h
  exact h

end AlgebraicComplexity.Examples
