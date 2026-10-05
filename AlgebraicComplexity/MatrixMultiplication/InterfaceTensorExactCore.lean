/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordTypeCore
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordCore
import AlgebraicComplexity.Tensor.Basic

/-!
# Exact finite data for recursive interface tensors

This module contains the denominator-free data needed to select a recursive interface term at a
fixed finite sample size.  It deliberately excludes real probability vectors, approximate
consistency, entropy, recursive division, and tensor realization.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor

/-- An exact finite complete-split type: integer counts of chunks at one sample size, supported on
the prescribed digit sum. -/
structure CompleteSplitProfile (depth total samples : ℕ) where
  counts : SplitWord depth → ℕ
  isType : counts ∈ WordType.types (SplitWord depth) samples
  supported : ∀ word, counts word ≠ 0 → splitWordWeight word = total

namespace CompleteSplitProfile

variable {depth total samples : ℕ}

/-- The exact finite class of chunk sequences realizing a complete-split profile. -/
noncomputable def typeClass (β : CompleteSplitProfile depth total samples) :
    Finset (Fin samples → SplitWord depth) :=
  WordType.typeClass samples β.counts

/-- The one-sample exact profile concentrated at one admissible split word. -/
noncomputable def singleton (word : SplitWord depth)
    (hweight : splitWordWeight word = total) :
    CompleteSplitProfile depth total 1 where
  counts other := if other = word then 1 else 0
  isType := by
    classical
    rw [WordType.mem_types]
    simp
  supported := by
    intro other hcount
    by_cases h : other = word
    · simpa [h] using hweight
    · exact False.elim (hcount (by simp [h]))

@[simp] theorem singleton_counts (word : SplitWord depth)
    (hweight : splitWordWeight word = total) (other : SplitWord depth) :
    (singleton word hweight).counts other = if other = word then 1 else 0 :=
  rfl

/-- A chunk sequence is exactly consistent with a profile when its empirical multiplicities are
the stored counts. -/
def IsConsistent (β : CompleteSplitProfile depth total samples)
    (sequence : Fin samples → SplitWord depth) : Prop :=
  WordType.multiplicity sequence = β.counts

/-- Exact complete-split consistency is invariant under an arbitrary permutation of the sample
positions. -/
theorem isConsistent_comp_perm
    (β : CompleteSplitProfile depth total samples)
    (sequence : Fin samples → SplitWord depth)
    (sigma : Equiv.Perm (Fin samples)) :
    β.IsConsistent (sequence ∘ sigma) ↔ β.IsConsistent sequence := by
  unfold IsConsistent
  have hm := WordType.multiplicity_reindex sigma.symm sequence
  simpa using congrArg (fun counts ↦ counts = β.counts) hm

@[simp] theorem isConsistent_iff_mem_typeClass
    (β : CompleteSplitProfile depth total samples)
    (sequence : Fin samples → SplitWord depth) :
    β.IsConsistent sequence ↔ sequence ∈ β.typeClass := by
  simp [IsConsistent, typeClass]

/-- A one-chunk sequence is consistent with a singleton profile exactly when its chunk is the
profile's supported word. -/
theorem singleton_isConsistent_const_iff (word other : SplitWord depth)
    (hweight : splitWordWeight word = total) :
    (singleton word hweight).IsConsistent (fun _ : Fin 1 ↦ other) ↔ other = word := by
  constructor
  · intro hconsistent
    change WordType.multiplicity (fun _ : Fin 1 ↦ other) =
      (singleton word hweight).counts at hconsistent
    have hcoordinate := congrFun hconsistent other
    rw [WordType.multiplicity_const_fin_one, singleton_counts] at hcoordinate
    by_contra hne
    simp [hne] at hcoordinate
  · intro h
    subst other
    change WordType.multiplicity (fun _ : Fin 1 ↦ word) =
      (singleton word hweight).counts
    funext letter
    rw [WordType.multiplicity_const_fin_one, singleton_counts]

end CompleteSplitProfile

/-- Aggregate three-coordinate address of a recursive constituent. -/
structure LevelConstituentIndex (depth : ℕ) where
  count : Leg → ℕ
  total : ∑ c, count c = 2 ^ (depth + 1)

/-- Exact finite metadata of one term in a recursive interface tensor. -/
structure ExactInterfaceTermParameters (depth : ℕ) where
  multiplicity : ℕ
  index : LevelConstituentIndex depth
  split : ∀ c, CompleteSplitProfile depth (index.count c) multiplicity

end AlgebraicComplexity
