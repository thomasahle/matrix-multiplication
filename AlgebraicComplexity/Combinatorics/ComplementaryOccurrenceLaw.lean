/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrence
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Symbol laws on labelled complementary occurrences

This file adds exact occurrence/symbol tables to `ComplementaryOccurrence`.  Pooling by a finite
cell map produces a joint cell/symbol profile, and the principal theorem proves that its first
marginal is exactly the occurrence cell profile.  This is the consistency condition needed by
the conditional method of types.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w

/-- An exact symbol-count table for every labelled child occurrence.  Its row mass is the mass
of the occurrence's ordered state.  The two sides may have different count tables. -/
structure ComplementaryOccurrenceLaw
    {State : Type u} [Fintype State] (profile : State → ℕ)
    (Symbol : Type v) [Fintype Symbol] where
  count : ComplementaryOccurrence State → Symbol → ℕ
  rowSum : ∀ occurrence, (∑ symbol, count occurrence symbol) =
    profile occurrence.orderedState

namespace ComplementaryOccurrenceLaw

variable {State : Type u} [Fintype State]
variable {Symbol : Type v} [Fintype Symbol]
variable {Cell : Type w} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

/-- The raw occurrence/symbol joint profile before pooling by compatibility cell. -/
def rawProfile (law : ComplementaryOccurrenceLaw profile Symbol) :
    ComplementaryOccurrence State × Symbol → ℕ :=
  fun entry ↦ law.count entry.1 entry.2

/-- Joint cell/symbol profile obtained by pooling all labelled occurrences. -/
noncomputable def cellJointProfile
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell) : Cell × Symbol → ℕ :=
  fun entry ↦ ∑ occurrence,
    if cellOf (occurrence.childState complement) = entry.1 then
      law.count occurrence entry.2
    else 0

omit [DecidableEq Cell] in
/-- The first marginal of a joint integral table is its row sum.  This lightweight form avoids
importing the full conditional-word-type layer into the occurrence-profile API. -/
theorem mappedType_fst_apply (joint : Cell × Symbol → ℕ) (cell : Cell) :
    WordType.mappedType Prod.fst joint cell = ∑ symbol, joint (cell, symbol) := by
  classical
  simp only [WordType.mappedType, WordType.letterFiber, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_eq_single cell]
  · simp
  · intro other _ hother
    simp [hother]
  · simp

/-- The first marginal of the pooled joint profile is exactly the pushed occurrence cell
profile.

Proof sketch: expand the first marginal as a row sum, interchange the finite symbol and occurrence
sums, use `rowSum` on every labelled occurrence, and recognize the pushed cell profile. -/
theorem mappedType_fst_cellJointProfile
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell) :
    WordType.mappedType Prod.fst (law.cellJointProfile complement cellOf) =
      complementaryOccurrenceCellProfile profile complement cellOf := by
  classical
  funext cell
  rw [mappedType_fst_apply]
  unfold cellJointProfile complementaryOccurrenceCellProfile
  rw [WordType.mappedType_eq_sum_ite, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro occurrence _
  by_cases hcell : cellOf (occurrence.childState complement) = cell
  · simp [hcell, law.rowSum, ComplementaryOccurrence.integralMass]
  · simp [hcell]

end ComplementaryOccurrenceLaw

end AlgebraicComplexity
