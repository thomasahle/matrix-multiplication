/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveChildType

set_option autoImplicit false

/-!
# Exact marginal-family counts for recursive split words

The recursive constituent theorem distinguishes two finite word families on the ordered child
split alphabet.

* The **marked** family has one prescribed joint split type `alpha` (`N_alpha` in the paper).
* The **ambient** family fixes only the three coordinate marginals of `alpha`
  (`N_triple` in the paper).

This file defines those families without mentioning hashing or tensors.  Its main finite identity
is

`N_X * #(ambient words over one fixed X word) = N_triple`.

There is no asymptotic error in this statement.  The proof uses the symmetric-group action on
sample positions: all words of the prescribed `X` type lie in one orbit, and simultaneous
reindexing preserves the other two marginal constraints.  The same result holds for any of the
three legs.

Keeping this count independent of the tensor realization is important.  A tensor client may
inject its actual competitor family into this combinatorial ambient fiber; it need not assume
that every abstract marginal word already has a nonempty fine constituent.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u

namespace ExactRecursiveSplitType

variable {parent : Leg → ℕ} {childTotal samples : ℕ}

/-- The coordinate word visible on one leg of an ordered child-shape word. -/
def coordinateWord (c : Leg)
    (word : Fin samples → RecursiveChildShape parent childTotal) :
    Fin samples → Fin (childTotal + 1) :=
  coordinate c ∘ word

/-- All ordered child-shape words having the three coordinate marginals prescribed by `alpha`.

This is the exact finite family denoted `N_triple` in the recursive constituent proof. -/
noncomputable def marginalWords
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    Finset (Fin samples → RecursiveChildShape parent childTotal) := by
  classical
  exact Finset.univ.filter fun word ↦
    ∀ c, WordType.multiplicity (coordinateWord c word) = alpha.marginalCount c

@[simp] theorem mem_marginalWords
    (alpha : ExactRecursiveSplitType parent childTotal samples)
    (word : Fin samples → RecursiveChildShape parent childTotal) :
    word ∈ alpha.marginalWords ↔
      ∀ c, WordType.multiplicity (coordinateWord c word) = alpha.marginalCount c := by
  classical
  simp [marginalWords]

/-- The marked joint-type family `N_alpha`. -/
noncomputable def markedWords
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    Finset (Fin samples → RecursiveChildShape parent childTotal) :=
  WordType.typeClass samples alpha.count

@[simp] theorem mem_markedWords
    (alpha : ExactRecursiveSplitType parent childTotal samples)
    (word : Fin samples → RecursiveChildShape parent childTotal) :
    word ∈ alpha.markedWords ↔ WordType.multiplicity word = alpha.count := by
  exact WordType.mem_typeClass

/-- Every marked joint-type word has the three prescribed coordinate marginals. -/
theorem markedWords_subset_marginalWords
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    alpha.markedWords ⊆ alpha.marginalWords := by
  classical
  intro word hword
  rw [mem_marginalWords]
  intro c
  rw [coordinateWord, WordType.multiplicity_comp_eq_mappedType,
    WordType.mem_typeClass.mp hword]
  rfl

/-- The marked family has the exact multinomial cardinality of the joint split profile. -/
theorem card_markedWords
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    alpha.markedWords.card = Nat.multinomial Finset.univ alpha.count := by
  exact WordType.card_typeClass_eq_multinomial alpha.count alpha.count_mem_types

/-- Ambient words over one fixed coordinate word. -/
noncomputable def marginalWordFiber
    (alpha : ExactRecursiveSplitType parent childTotal samples) (c : Leg)
    (target : Fin samples → Fin (childTotal + 1)) :
    Finset (Fin samples → RecursiveChildShape parent childTotal) :=
  alpha.marginalWords.filter fun word ↦ coordinateWord c word = target

@[simp] theorem mem_marginalWordFiber
    (alpha : ExactRecursiveSplitType parent childTotal samples) (c : Leg)
    (target : Fin samples → Fin (childTotal + 1))
    (word : Fin samples → RecursiveChildShape parent childTotal) :
    word ∈ alpha.marginalWordFiber c target ↔
      word ∈ alpha.marginalWords ∧ coordinateWord c word = target := by
  classical
  simp [marginalWordFiber]

/-- Simultaneous permutation of sample positions preserves the ambient marginal family. -/
theorem mem_marginalWords_reindex_iff
    (alpha : ExactRecursiveSplitType parent childTotal samples)
    (e : Equiv.Perm (Fin samples))
    (word : Fin samples → RecursiveChildShape parent childTotal) :
    word ∈ alpha.marginalWords ↔ word ∘ e.symm ∈ alpha.marginalWords := by
  classical
  rw [mem_marginalWords, mem_marginalWords]
  constructor <;> intro h c
  · have hreindex := WordType.multiplicity_reindex e (coordinateWord c word)
    simpa only [coordinateWord, Function.comp_assoc] using hreindex.trans (h c)
  · have hreindex := WordType.multiplicity_reindex e.symm
      (coordinateWord c (word ∘ e.symm))
    have hback := hreindex.trans (h c)
    simpa only [coordinateWord, Function.comp_assoc, Equiv.symm_symm,
      Equiv.symm_apply_apply, Function.comp_def] using hback

/-- Coordinate fibers above target words of the same type have equal cardinality. -/
theorem card_marginalWordFiber_eq_of_multiplicity_eq
    (alpha : ExactRecursiveSplitType parent childTotal samples) (c : Leg)
    (left right : Fin samples → Fin (childTotal + 1))
    (hmultiplicity : WordType.multiplicity left = WordType.multiplicity right) :
    (alpha.marginalWordFiber c left).card =
      (alpha.marginalWordFiber c right).card := by
  classical
  let e := WordType.positionPermOfSameMultiplicity left right hmultiplicity
  have he : right ∘ e = left :=
    WordType.positionPermOfSameMultiplicity_map left right hmultiplicity
  have he' : left ∘ e.symm = right := by
    funext i
    have hi := congrFun he (e.symm i)
    simpa [Function.comp_apply] using hi.symm
  apply Finset.card_bij (fun word _ ↦ word ∘ e.symm)
  · intro word hword
    rw [mem_marginalWordFiber] at hword ⊢
    refine ⟨(mem_marginalWords_reindex_iff alpha e word).mp hword.1, ?_⟩
    calc
      coordinateWord c (word ∘ e.symm) = coordinateWord c word ∘ e.symm := by
        rfl
      _ = left ∘ e.symm := congrArg (· ∘ e.symm) hword.2
      _ = right := he'
  · intro leftWord _ rightWord _ heq
    funext i
    have hi := congrFun heq (e i)
    simpa [Function.comp_apply] using hi
  · intro word hword
    refine ⟨word ∘ e, ?_, ?_⟩
    · rw [mem_marginalWordFiber] at hword ⊢
      refine ⟨?_, ?_⟩
      · have hstable :=
          (mem_marginalWords_reindex_iff alpha e.symm word).mp hword.1
        simpa [Function.comp_def] using hstable
      · calc
          coordinateWord c (word ∘ e) = coordinateWord c word ∘ e := by rfl
          _ = right ∘ e := congrArg (· ∘ e) hword.2
          _ = left := he
    · funext i
      simp [Function.comp_apply]

/-- **Exact recursive marginal-fiber double count.**

For any correctly typed target coordinate word, the target type-class cardinality times its
ambient competitor-fiber cardinality is exactly the total marginal-family cardinality.  This is
the division-free finite identity behind `M_0 ≥ 8 N_triple / N_X`. -/
theorem card_coordinateType_mul_card_marginalWordFiber
    (alpha : ExactRecursiveSplitType parent childTotal samples) (c : Leg)
    (target : Fin samples → Fin (childTotal + 1))
    (htarget : target ∈ WordType.typeClass samples (alpha.marginalCount c)) :
    (WordType.typeClass samples (alpha.marginalCount c)).card *
        (alpha.marginalWordFiber c target).card =
      alpha.marginalWords.card := by
  classical
  symm
  calc
    alpha.marginalWords.card =
        ∑ candidate ∈ WordType.typeClass samples (alpha.marginalCount c),
          (alpha.marginalWordFiber c candidate).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun word hword ↦ by
        simp only [Finset.mem_coe, WordType.mem_typeClass]
        exact (mem_marginalWords alpha word).mp hword c)
    _ = ∑ _candidate ∈ WordType.typeClass samples (alpha.marginalCount c),
          (alpha.marginalWordFiber c target).card := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      apply card_marginalWordFiber_eq_of_multiplicity_eq
      exact (WordType.mem_typeClass.mp hcandidate).trans
        (WordType.mem_typeClass.mp htarget).symm
    _ = (WordType.typeClass samples (alpha.marginalCount c)).card *
        (alpha.marginalWordFiber c target).card := by simp

end ExactRecursiveSplitType
end MoreAsymmetryCompatibility
end AlgebraicComplexity
