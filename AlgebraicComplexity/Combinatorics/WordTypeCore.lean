/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact multiplicity types of finite words

This module contains the finite, denominator-free core of word types: multiplicities, type
classes, the sum law, singleton words, and invariance under position permutations.  Polynomial
cardinality bounds, multinomial identities, entropy, and asymptotic estimates remain in
`Combinatorics.WordType`, which re-exports this core.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι]

/-- Number of occurrences of a letter in a finite word. -/
noncomputable def multiplicity (word : Fin n → ι) (i : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun j ↦ word j = i).card

/-- All multiplicity vectors of words of length `n`. -/
noncomputable def types (ι : Type u) [Fintype ι] (n : ℕ) : Finset (ι → ℕ) := by
  classical
  exact Finset.piAntidiag Finset.univ n

/-- The words of length `n` having a prescribed multiplicity vector. -/
noncomputable def typeClass (n : ℕ) (a : ι → ℕ) : Finset (Fin n → ι) := by
  classical
  exact Finset.univ.filter fun word ↦ multiplicity word = a

@[simp] theorem mem_typeClass {n : ℕ} {a : ι → ℕ} {word : Fin n → ι} :
    word ∈ typeClass n a ↔ multiplicity word = a := by
  classical
  simp [typeClass]

/-- The letter multiplicities of a word add up to its length. -/
theorem sum_multiplicity (word : Fin n → ι) :
    ∑ i, multiplicity word i = n := by
  classical
  simpa [multiplicity] using (Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset ι))
    (f := word) (by simp)).symm

omit [Fintype ι] in
/-- Multiplicity in a one-letter word is the corresponding Kronecker delta. -/
theorem multiplicity_const_fin_one [DecidableEq ι] (a b : ι) :
    multiplicity (fun _ : Fin 1 ↦ a) b = if b = a then 1 else 0 := by
  unfold multiplicity
  by_cases h : b = a
  · subst b
    simp
  · have hab : a ≠ b := fun h' ↦ h h'.symm
    simp [h, hab]

/-- Multiplicity is the cardinality of the corresponding position fiber. -/
theorem multiplicity_eq_card_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (word : Fin n → α) (a : α) :
    multiplicity word a = Fintype.card {i // word i = a} := by
  rw [Fintype.card_subtype]
  unfold multiplicity
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-- Reindexing the positions of a word preserves all letter multiplicities. -/
theorem multiplicity_reindex {α : Type*} [Fintype α]
    (e : Equiv.Perm (Fin n)) (word : Fin n → α) :
    multiplicity (word ∘ e.symm) = multiplicity word := by
  classical
  funext a
  rw [multiplicity_eq_card_fiber, multiplicity_eq_card_fiber]
  exact Fintype.card_congr (e.symm.subtypeEquiv fun i ↦ by
    simp [Function.comp_apply])

@[simp] theorem multiplicity_mem_types (word : Fin n → ι) :
    multiplicity word ∈ types ι n := by
  classical
  simp [types, sum_multiplicity]

@[simp] theorem mem_types {a : ι → ℕ} :
    a ∈ types ι n ↔ ∑ i, a i = n := by
  classical
  simp [types]

end AlgebraicComplexity.WordType
