/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType

/-!
# Finite conditional multiplicity classes

This is the dependency-minimal finite core of conditional word types.  Asymptotic growth belongs
in `ConditionalWordType`, which re-exports this module for backward compatibility.
-/

namespace AlgebraicComplexity.WordType

universe u v

variable {U : Type u} {Z : Type v} [Fintype U] [Fintype Z]

/-- Pair a fixed coarse word with a candidate refinement word coordinate by coordinate. -/
def jointWord (source : Fin n → U) (target : Fin n → Z) : Fin n → U × Z :=
  fun i ↦ (source i, target i)

/-- Refinement words whose joint word with `source` has the prescribed multiplicity. -/
noncomputable def conditionalTypeClass
    (source : Fin n → U) (jointType : U × Z → ℕ) : Finset (Fin n → Z) := by
  classical
  exact Finset.univ.filter fun target ↦ multiplicity (jointWord source target) = jointType

@[simp] theorem mem_conditionalTypeClass
    {source : Fin n → U} {jointType : U × Z → ℕ} {target : Fin n → Z} :
    target ∈ conditionalTypeClass source jointType ↔
      multiplicity (jointWord source target) = jointType := by
  classical
  simp [conditionalTypeClass]

/-- The pushforward of a joint type along the first projection is its row-sum marginal. -/
theorem mappedType_fst_apply (jointType : U × Z → ℕ) (u : U) :
    mappedType Prod.fst jointType u = ∑ z, jointType (u, z) := by
  classical
  simp only [mappedType, letterFiber, Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
  · simp
  · intro other _ hother
    simp [hother]
  · simp

/-- Function equality of a coarse marginal is exactly its family of row-sum equations. -/
theorem mappedType_fst_eq_iff (jointType : U × Z → ℕ) (coarseType : U → ℕ) :
    mappedType Prod.fst jointType = coarseType ↔
      ∀ u, (∑ z, jointType (u, z)) = coarseType u := by
  rw [funext_iff]
  constructor
  · intro h u
    rw [← mappedType_fst_apply]
    exact h u
  · intro h u
    rw [mappedType_fst_apply]
    exact h u

/-- A conditional type class is canonically the typed coordinatewise fiber of `Prod.fst`. -/
noncomputable def conditionalTypeClassEquivTypedWordMapFiber
    (source : Fin n → U) (jointType : U × Z → ℕ) :
    {target // target ∈ conditionalTypeClass source jointType} ≃
      {word // word ∈ typedWordMapFiber Prod.fst jointType source} where
  toFun target := ⟨jointWord source target.1, by
    rw [mem_typedWordMapFiber]
    exact ⟨mem_conditionalTypeClass.mp target.2, by
      funext i
      rfl⟩⟩
  invFun word := ⟨fun i ↦ (word.1 i).2, by
    rw [mem_conditionalTypeClass]
    have hword := mem_typedWordMapFiber.mp word.2
    have hjoint : jointWord source (fun i ↦ (word.1 i).2) = word.1 := by
      funext i
      apply Prod.ext
      · have hi := congrFun hword.2 i
        change source i = (word.1 i).1
        simpa [Function.comp_apply] using hi.symm
      · rfl
    rw [hjoint, hword.1]⟩
  left_inv target := by
    apply Subtype.ext
    funext i
    rfl
  right_inv word := by
    apply Subtype.ext
    funext i
    have hword := mem_typedWordMapFiber.mp word.2
    apply Prod.ext
    · have hi := congrFun hword.2 i
      change source i = (word.1 i).1
      simpa [Function.comp_apply] using hi.symm
    · rfl

/-- Conditional refinement words and typed joint-word lifts have the same cardinality. -/
theorem card_conditionalTypeClass_eq_typedWordMapFiber
    (source : Fin n → U) (jointType : U × Z → ℕ) :
    (conditionalTypeClass source jointType).card =
      (typedWordMapFiber Prod.fst jointType source).card := by
  classical
  rw [← Fintype.card_coe (conditionalTypeClass source jointType),
    ← Fintype.card_coe (typedWordMapFiber Prod.fst jointType source)]
  exact Fintype.card_congr (conditionalTypeClassEquivTypedWordMapFiber source jointType)

/-- Exact conditional-type factorization before replacing cardinalities by multinomials. -/
theorem card_sourceType_mul_card_conditionalTypeClass
    (source : Fin n → U) (jointType : U × Z → ℕ)
    (hmap : mappedType Prod.fst jointType = multiplicity source) :
    (typeClass n (mappedType Prod.fst jointType)).card *
        (conditionalTypeClass source jointType).card =
      (typeClass n jointType).card := by
  classical
  rw [card_conditionalTypeClass_eq_typedWordMapFiber]
  apply card_targetType_mul_card_typedWordMapFiber
  rw [mem_typeClass, hmap]

/-- Division-free exact conditional method-of-types formula. -/
theorem multinomial_source_mul_card_conditionalTypeClass
    (source : Fin n → U) (jointType : U × Z → ℕ)
    (hjoint : jointType ∈ types (U × Z) n)
    (hmap : mappedType Prod.fst jointType = multiplicity source) :
    Nat.multinomial Finset.univ (multiplicity source) *
        (conditionalTypeClass source jointType).card =
      Nat.multinomial Finset.univ jointType := by
  classical
  have h := card_sourceType_mul_card_conditionalTypeClass source jointType hmap
  rw [hmap,
    card_typeClass_eq_multinomial _ (multiplicity_mem_types source),
    card_typeClass_eq_multinomial jointType hjoint] at h
  exact h

/-- The same formula with the marginal equality supplied in the opposite orientation. -/
theorem multinomial_source_mul_card_conditionalTypeClass_of_multiplicity_eq
    (source : Fin n → U) (jointType : U × Z → ℕ)
    (hjoint : jointType ∈ types (U × Z) n)
    (hmap : multiplicity source = mappedType Prod.fst jointType) :
    Nat.multinomial Finset.univ (multiplicity source) *
        (conditionalTypeClass source jointType).card =
      Nat.multinomial Finset.univ jointType :=
  multinomial_source_mul_card_conditionalTypeClass source jointType hjoint hmap.symm

/-- Every legal joint type with the prescribed coarse marginal has a refinement. -/
theorem conditionalTypeClass_nonempty
    (source : Fin n → U) (jointType : U × Z → ℕ)
    (hjoint : jointType ∈ types (U × Z) n)
    (hmap : mappedType Prod.fst jointType = multiplicity source) :
    (conditionalTypeClass source jointType).Nonempty := by
  rw [← Finset.card_pos]
  have hfactor :=
    multinomial_source_mul_card_conditionalTypeClass source jointType hjoint hmap
  have hpositive :
      0 < Nat.multinomial Finset.univ (multiplicity source) *
        (conditionalTypeClass source jointType).card := by
    rw [hfactor]
    exact Nat.multinomial_pos Finset.univ jointType
  exact Nat.pos_of_mul_pos_left hpositive

end AlgebraicComplexity.WordType
