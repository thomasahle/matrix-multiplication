/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType

set_option autoImplicit false

/-!
# Typed word-map fibers over a finite target family

For a map from a finite source alphabet into an arbitrary target alphabet, this module considers
source words of one prescribed multiplicity profile whose coordinatewise image belongs to a
finite family of target words.  It proves that this set is exactly the dependent sum of the
individual typed fibers over the target family, and records both the resulting cardinality
identity and its uniform-fiber upper bound.

The result is pure finite combinatorics.  Its motivating application is the staged quotient count
in the Total-Weight manuscript: the actual outer competitor family must be fixed first, and only
then may the conditional lift fibers above its members be counted.  See
`better_bound/paper.tex:1755-1765`, following `eq:relaxed-z-actual-family` and
`prop:total-weight-competitor-count`.  No tensor, entropy, hashing, or paper-specific alphabet is
used here.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u v

/-- Source words of profile `a` whose coordinatewise image under `f` belongs to `targets`.

Unlike a fiber over one target word, this definition permits an arbitrary finite outer family.
It still contains only source words actually lying above that family; it does not enlarge the
family to every locally legal target word. -/
noncomputable def typedWordMapFiberOverFamily
    {A : Type u} {B : Type v} [Fintype A] {n : ℕ}
    (f : A → B) (a : A → ℕ) (targets : Finset (Fin n → B)) :
    Finset (Fin n → A) := by
  classical
  exact (typeClass n a).filter fun word ↦ f ∘ word ∈ targets

/-- Membership means exactly that the source profile is `a` and the mapped word lies in the
specified finite target family. -/
@[simp] theorem mem_typedWordMapFiberOverFamily
    {A : Type u} {B : Type v} [Fintype A] {n : ℕ}
    {f : A → B} {a : A → ℕ} {targets : Finset (Fin n → B)} {word : Fin n → A} :
    word ∈ typedWordMapFiberOverFamily f a targets ↔
      multiplicity word = a ∧ f ∘ word ∈ targets := by
  classical
  simp only [typedWordMapFiberOverFamily, Finset.mem_filter, mem_typeClass]

/-- A typed source word above a finite target family is equivalently its mapped target, together
with the same source word viewed in the typed fiber above that target.

This is an exact decomposition: the target component is forced to be `f ∘ word`, so no choice of
a representative and no injectivity assumption on `f` is involved.

Proof sketch: send `word` to `(f ∘ word, word)`.  Membership in the outer family follows from the
definition, while the inner fiber equation is reflexivity.  Conversely, forget the displayed
target.  The fiber equation proves that its mapped word lies in the family.  The two operations
are inverse because the displayed target is uniquely determined by the source word. -/
noncomputable def typedWordMapFiberOverFamilyEquiv
    {A : Type u} {B : Type v} [Fintype A] {n : ℕ}
    (f : A → B) (a : A → ℕ) (targets : Finset (Fin n → B)) :
    {word // word ∈ typedWordMapFiberOverFamily f a targets} ≃
      Σ target : {target // target ∈ targets},
        {word // word ∈ typedWordMapFiber f a target.1} where
  toFun word := by
    have hword := mem_typedWordMapFiberOverFamily.mp word.2
    refine ⟨⟨f ∘ word.1, hword.2⟩, ⟨word.1, ?_⟩⟩
    rw [mem_typedWordMapFiber]
    exact ⟨hword.1, rfl⟩
  invFun pair := by
    have hword := mem_typedWordMapFiber.mp pair.2.2
    refine ⟨pair.2.1, ?_⟩
    rw [mem_typedWordMapFiberOverFamily]
    refine ⟨hword.1, ?_⟩
    rw [hword.2]
    exact pair.1.2
  left_inv word := by
    apply Subtype.ext
    rfl
  right_inv pair := by
    rcases pair with ⟨⟨target, htarget⟩, ⟨word, hword⟩⟩
    have htarget_eq : f ∘ word = target :=
      (mem_typedWordMapFiber.mp hword).2
    cases htarget_eq
    rfl

/-- The number of typed source words above an arbitrary finite target family is the sum of the
individual typed-fiber cardinalities over that family.

Proof sketch: take cardinalities in `typedWordMapFiberOverFamilyEquiv`, use the cardinality formula
for a dependent sum, and rewrite each finite subtype cardinality as the cardinality of its defining
finite set. -/
theorem card_typedWordMapFiberOverFamily_eq_sum
    {A : Type u} {B : Type v} [Fintype A] {n : ℕ}
    (f : A → B) (a : A → ℕ) (targets : Finset (Fin n → B)) :
    (typedWordMapFiberOverFamily f a targets).card =
      ∑ target ∈ targets, (typedWordMapFiber f a target).card := by
  classical
  rw [← Fintype.card_coe (typedWordMapFiberOverFamily f a targets),
    Fintype.card_congr (typedWordMapFiberOverFamilyEquiv f a targets),
    Fintype.card_sigma]
  simp only [Fintype.card_coe]
  exact (Finset.sum_subtype targets (fun _ ↦ Iff.rfl)
    (fun target ↦ (typedWordMapFiber f a target).card)).symm

/-- If every typed fiber above `targets` has size at most `L`, then the whole staged family has
size at most `targets.card * L`.

Proof sketch: use the exact cardinality sum and bound each summand by `L`; the resulting constant
sum has `targets.card` terms. -/
theorem card_typedWordMapFiberOverFamily_le_mul
    {A : Type u} {B : Type v} [Fintype A] {n : ℕ}
    (f : A → B) (a : A → ℕ) (targets : Finset (Fin n → B)) (L : ℕ)
    (hfiber : ∀ target ∈ targets, (typedWordMapFiber f a target).card ≤ L) :
    (typedWordMapFiberOverFamily f a targets).card ≤ targets.card * L := by
  calc
    (typedWordMapFiberOverFamily f a targets).card =
        ∑ target ∈ targets, (typedWordMapFiber f a target).card :=
      card_typedWordMapFiberOverFamily_eq_sum f a targets
    _ ≤ ∑ _target ∈ targets, L :=
      Finset.sum_le_sum fun target htarget ↦ hfiber target htarget
    _ = targets.card * L := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul]

end AlgebraicComplexity.WordType
