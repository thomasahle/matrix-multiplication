/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.Tensor.IndexedSubfamily
import AlgebraicComplexity.Tensor.IteratedProduct

/-!
# Multinomial type extraction for tensor direct sums

Schönhage's multiple-compression argument tensors a finite direct sum many times, distributes it
into independent word blocks, and retains one multiplicity type.  This file packages that exact
finite algebraic step.  The number of retained blocks is proved to be the corresponding
multinomial coefficient.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {I : Type w} [Fintype I]

/-- Recursive positive words whose function representation has multiplicity vector `a`. -/
noncomputable def positiveTypeClass (I : Type w) [Fintype I]
    (n : ℕ) (a : I → ℕ) : Finset (PositiveWord I n) := by
  classical
  exact Finset.univ.filter fun q ↦
    WordType.multiplicity (positiveWordEquiv I n q) = a

@[simp] theorem mem_positiveTypeClass {n : ℕ} {a : I → ℕ}
    {q : PositiveWord I n} :
    q ∈ positiveTypeClass I n a ↔
      WordType.multiplicity (positiveWordEquiv I n q) = a := by
  classical
  simp [positiveTypeClass]

/-- The recursive word representation carries its length in the type. In applications a length is
often obtained from a mass equation, so the same word arrives at the type-class API through an
equality cast.  Keeping this transport lemma next to `mem_positiveTypeClass` prevents clients
from having to unfold the representation (and, in particular, from accidentally changing the
chosen type while transporting a word).
-/
theorem mem_positiveTypeClass_cast_iff
    {n m : ℕ} (h : n = m) (q : PositiveWord I n) (a : I → ℕ) :
    positiveWordCast h q ∈ positiveTypeClass I m a ↔
      q ∈ positiveTypeClass I n a := by
  subst m
  rfl

/-- Reindexing every recursively represented word along a length equality transports the entire
positive type class to the equal length. -/
theorem positiveTypeClass_cast
    [DecidableEq I] {n m : ℕ} (h : n = m) (a : I → ℕ) :
    (positiveTypeClass I n a).image
        (fun q : PositiveWord I n ↦ positiveWordCast h q) =
      positiveTypeClass I m a := by
  classical
  cases h
  simp

/-- The recursive and function representations of a word type have the same cardinality. -/
theorem card_positiveTypeClass (n : ℕ) (a : I → ℕ) :
    (positiveTypeClass I n a).card = (WordType.typeClass (n + 1) a).card := by
  classical
  apply Finset.card_bijective (positiveWordEquiv I n)
    (positiveWordEquiv I n).bijective
  intro q
  simp

/-- Exact multinomial cardinality of a recursively represented positive word type. -/
theorem card_positiveTypeClass_eq_multinomial (n : ℕ) (a : I → ℕ)
    (ha : a ∈ WordType.types I (n + 1)) :
    (positiveTypeClass I n a).card = Nat.multinomial Finset.univ a := by
  rw [card_positiveTypeClass]
  exact WordType.card_typeClass_eq_multinomial a ha

variable (W : I → LegModuleFamily.{u, v} K)
variable (T : ∀ i, Tensor3 K (W i).Space)

/-- Ambient family of the word tensors belonging to one selected multiplicity type. -/
abbrev PositiveTypeFamily (n : ℕ) (a : I → ℕ) :=
  IndexedSubfamily
    (V := fun q : PositiveWord I n ↦ (positiveWordFamily W n q).Space)
    (positiveTypeClass I n a)

/-- A positive external power of an indexed direct sum restricts to the genuine direct sum of all
word tensors of any chosen multiplicity type. -/
theorem Restricts.iteratedExternal_indexedDirectSum_type (n : ℕ) (a : I → ℕ) :
    Restricts
      (Tensor.iteratedExternal (indexedDirectSumFamily W) (Tensor.indexedDirectSum T) n)
      (Tensor.indexedDirectSum
        (V := PositiveTypeFamily (K := K) W n a)
        (fun q : positiveTypeClass I n a ↦ positiveWordTensor W T n q.1)) := by
  exact (Isomorphic.iteratedExternal_indexedDirectSum W T n).restricts.trans
    (Restricts.indexedDirectSum_subfamily
      (positiveWordTensor W T n) (positiveTypeClass I n a))

end AlgebraicComplexity.Tensor
