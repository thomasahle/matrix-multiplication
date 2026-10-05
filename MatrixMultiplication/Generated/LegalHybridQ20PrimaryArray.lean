/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.SimplifiedVolumeSchemaDefs

set_option autoImplicit false

/-!
# Lightweight exact-array composition for the legal-hybrid q20 primary table

This leaf provides only the list/array lemmas needed to assemble independently checked support and
numerator blocks. It is the reduction boundary for the q20 candidate's top law, described in
`better_bound/paper.tex:148-159`. Generated leaves check at most 200 entries, then use these
structural lemmas to reconstruct the two semantic sparse chunks. It contains no certificate
payload, probability semantics, logarithmic estimate, restriction, or endpoint claim.

The downstream ordered-child laws follow [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`. The q20 data are this project's own candidate;
the elementary array identities here only assemble its finite representation.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore

open MatrixMultiplication.Generated.SimplifiedVolume

/-- Concatenate two exact arrays through their list representations. -/
def concatArrays (left right : Array Nat) : Array Nat :=
  (left.toList ++ right.toList).toArray

/-- Reading a concatenated array as a list recovers list concatenation. -/
@[simp] theorem concatArrays_toList (left right : Array Nat) :
    (concatArrays left right).toList = left.toList ++ right.toList := by
  simp [concatArrays]

/-- The length of a concatenation is the sum of the two lengths. -/
@[simp] theorem concatArrays_size (left right : Array Nat) :
    (concatArrays left right).size = left.size + right.size := by
  simp [concatArrays]

/-- Summing a concatenation adds the sums of the two input arrays. -/
@[simp] theorem concatArrays_sum (left right : Array Nat) :
    (concatArrays left right).toList.sum = left.toList.sum + right.toList.sum := by
  simp [concatArrays]

/-- `All` is preserved by list append. -/
theorem all_append {predicate : Nat → Prop} {left right : List Nat}
    (hleft : All predicate left) (hright : All predicate right) :
    All predicate (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons value values ih => exact ⟨hleft.1, ih hleft.2⟩

/-- Strengthen a checked pointwise predicate. -/
theorem all_mono {first second : Nat → Prop} (himp : ∀ value, first value → second value) :
    ∀ {values : List Nat}, All first values → All second values
  | [], _ => trivial
  | _ :: _, hvalues => ⟨himp _ hvalues.1, all_mono himp hvalues.2⟩

/-- Adjacent strict order composes across a half-open cut.

Proof sketch: induct along the left list. Its internal comparisons are unchanged; the final
comparison across the join follows from the left and right bounds at the common cut.
-/
theorem strictlyIncreasing_append_of_cut {cut : Nat} :
    ∀ (left right : List Nat),
      StrictlyIncreasing left →
      StrictlyIncreasing right →
      All (fun value => value < cut) left →
      All (fun value => cut ≤ value) right →
      StrictlyIncreasing (left ++ right)
  | [], _, _, hright, _, _ => hright
  | [_], [], _, _, _, _ => trivial
  | [_left], _right :: _rights, _, hright, hleftBound, hrightBound =>
      ⟨Nat.lt_of_lt_of_le hleftBound.1 hrightBound.1, hright⟩
  | _first :: second :: rest, right, hleft, hright, hleftBound, hrightBound =>
      ⟨hleft.1,
        strictlyIncreasing_append_of_cut (second :: rest) right hleft.2 hright
          hleftBound.2 hrightBound⟩

/-- Join two sparse mass chunks without changing their entry order. -/
def appendMassChunk (left right : SparseMassChunk) : SparseMassChunk where
  atomIndices := concatArrays left.atomIndices right.atomIndices
  numerators := concatArrays left.numerators right.numerators

/-- Two valid half-open chunks remain valid when joined at their common cut.

Proof sketch: concatenate the matching lengths and positivity witnesses. The common cut orders
the last left address before the first right address, and both intervals lie in the merged one.
-/
theorem appendMassChunk_isValid {left right : SparseMassChunk}
    {ambient lower cut upper : Nat}
    (hlower : lower ≤ cut) (hupper : cut ≤ upper)
    (hleft : left.IsValid ambient lower cut)
    (hright : right.IsValid ambient cut upper) :
    (appendMassChunk left right).IsValid ambient lower upper := by
  rcases hleft with ⟨hleftSize, hleftIncreasing, hleftBounds, hleftPositive⟩
  rcases hright with ⟨hrightSize, hrightIncreasing, hrightBounds, hrightPositive⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [appendMassChunk, concatArrays_size]
    rw [hleftSize, hrightSize]
  · apply strictlyIncreasing_append_of_cut left.atomIndices.toList right.atomIndices.toList
      hleftIncreasing hrightIncreasing
    · exact all_mono (fun _ h => h.2.1) hleftBounds
    · exact all_mono (fun _ h => h.1) hrightBounds
  · apply all_append
    · exact all_mono (fun _ h => ⟨h.1, Nat.lt_of_lt_of_le h.2.1 hupper, h.2.2⟩) hleftBounds
    · exact all_mono (fun _ h => ⟨Nat.le_trans hlower h.1, h.2.1, h.2.2⟩) hrightBounds
  · exact all_append hleftPositive hrightPositive

/-- Joining sparse chunks adds their numbers of stored entries. -/
@[simp] theorem appendMassChunk_valueCount (left right : SparseMassChunk) :
    (appendMassChunk left right).valueCount = left.valueCount + right.valueCount := by
  simp [appendMassChunk, SparseMassChunk.valueCount]

/-- Joining sparse chunks adds their total numerator masses. -/
@[simp] theorem appendMassChunk_total (left right : SparseMassChunk) :
    (appendMassChunk left right).total = left.total + right.total := by
  simp [appendMassChunk, SparseMassChunk.total]

end MatrixMultiplication.Generated.LegalHybridQ20Primary.ArrayCore
