/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TypedWordMapFiberOverFamily

set_option autoImplicit false

/-!
# Counting an actual family through its realized profiles

This module gives the finite, paper-independent counting step needed when an actual family of
competitors is decoded into typed words.  An injective decoder sends each competitor to its
realized multiplicity profile and to a word above a prescribed finite outer target family.  The
decoder therefore embeds the actual family into the dependent union of precisely the typed fibers
whose profiles it realizes.  Taking cardinalities gives a one-sided sum bound.

The formulation deliberately uses the image of the actual source family.  It neither replaces
that family by every locally legal word nor assumes that every word in a typed fiber is an actual
competitor.  This is the generic counting step behind the staged quotient composition in the
Total-Weight manuscript, `better_bound/paper.tex:1755-1767`.  Paper-specific clients must still
construct the actual decoder and prove that its mapped words lie in the intended outer family.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u v w

/-- An actual finite source family embeds into the dependent union of its realized-profile typed
fibers over a finite outer target family.

Here `decode` need only be injective on `source`, and `hmapped` says only that decoded source
members map into `targets`.  The codomain is intentionally an envelope: words in it need not come
from the source family.

Proof sketch: map a source member `c` to the profile `multiplicity (decode c)` and the decoded word
itself.  The profile lies in the displayed image by construction, while the word has that profile
and maps into `targets` by `hmapped`.  Equality of two outputs gives equality of their decoded
words, and injectivity of `decode` on `source` then recovers the original members. -/
noncomputable def realizedProfileTypedFiberEmbedding
    {C : Type u} {A : Type v} {B : Type w} [Fintype A] {n : ℕ}
    (source : Finset C) (decode : C → Fin n → A) (outer : A → B)
    (targets : Finset (Fin n → B))
    (hdecode : Set.InjOn decode (↑source : Set C))
    (hmapped : ∀ c ∈ source, outer ∘ decode c ∈ targets) :
    {c // c ∈ source} ↪
      Σ profile : {profile // profile ∈ source.image (multiplicity ∘ decode)},
        {word // word ∈ typedWordMapFiberOverFamily outer profile.1 targets} where
  toFun c := by
    classical
    refine ⟨⟨multiplicity (decode c.1), ?_⟩, ⟨decode c.1, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨c.1, c.2, rfl⟩
    · exact mem_typedWordMapFiberOverFamily.mpr ⟨rfl, hmapped c.1 c.2⟩
  inj' left right h := by
    apply Subtype.ext
    apply hdecode left.2 right.2
    exact congrArg (fun value ↦ value.2.1) h

/-- The size of an actual finite source family is at most the sum of the typed-fiber sizes over
exactly the multiplicity profiles realized by that family.

This is one-sided because the typed fibers may contain words that are not decoded actual source
members.  That direction is the safe one for an upper bound on the number of competitors.

Proof sketch: take finite cardinalities in `realizedProfileTypedFiberEmbedding`.  The cardinality of
its dependent-sum codomain is the sum of the cardinalities of its typed fibers. -/
theorem card_le_sum_realizedProfileTypedFibers
    {C : Type u} {A : Type v} {B : Type w} [Fintype A] {n : ℕ}
    (source : Finset C) (decode : C → Fin n → A) (outer : A → B)
    (targets : Finset (Fin n → B))
    (hdecode : Set.InjOn decode (↑source : Set C))
    (hmapped : ∀ c ∈ source, outer ∘ decode c ∈ targets) :
    source.card ≤
      ∑ profile ∈ source.image (multiplicity ∘ decode),
        (typedWordMapFiberOverFamily outer profile targets).card := by
  classical
  calc
    source.card = Fintype.card {c // c ∈ source} := (Fintype.card_coe source).symm
    _ ≤
        Fintype.card
          (Σ profile : {profile // profile ∈ source.image (multiplicity ∘ decode)},
            {word // word ∈ typedWordMapFiberOverFamily outer profile.1 targets}) :=
      Fintype.card_le_of_injective
        (realizedProfileTypedFiberEmbedding source decode outer targets hdecode hmapped)
        (realizedProfileTypedFiberEmbedding source decode outer targets hdecode hmapped).injective
    _ = ∑ profile ∈ source.image (multiplicity ∘ decode),
          (typedWordMapFiberOverFamily outer profile targets).card := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_coe]
      exact (Finset.sum_subtype (source.image (multiplicity ∘ decode))
        (fun _ ↦ Iff.rfl)
        (fun profile ↦ (typedWordMapFiberOverFamily outer profile targets).card)).symm

end AlgebraicComplexity.WordType
