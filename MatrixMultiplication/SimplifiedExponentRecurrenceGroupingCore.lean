/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentRecurrenceInput

/-!
# Executable sufficient-statistic grouping for level-two recurrence inputs

For fixed `(muNumerator, heavyCoordinate)`, a level-two branch contribution is linear in the
occurrence numerator.  This definition-only/exact-arithmetic module groups records by that key and
sums their masses.  It deliberately does not import real entropy: the semantic rate-preservation
theorem is a separate adapter in `SimplifiedExponentRecurrenceGrouping.lean`.

The fold omits zero-occurrence records.  This is not an assumption about the producer: the exact
mass-preservation theorem below proves that those records contribute no occurrence mass, while the
semantic adapter proves that they contribute zero to every branch.
-/

namespace MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

namespace EdgeInput

/-- The sufficient-statistic key for a level-two entropy contribution. -/
def key (input : EdgeInput) : Nat × Nat :=
  (input.muNumerator, input.heavyCoordinate)

/-- Add occurrence masses while retaining the left record's sufficient-statistic key.

Semantic uses of this operation carry the explicit premise that both keys agree. -/
def combine (left right : EdgeInput) : EdgeInput :=
  ⟨left.occurrenceNumerator + right.occurrenceNumerator,
    left.muNumerator, left.heavyCoordinate⟩

end EdgeInput

/-- Insert one record into a grouped list, merging the first record with an equal key. -/
def insertInputByKey (input : EdgeInput) : List EdgeInput → List EdgeInput
  | [] => [input]
  | head :: tail =>
      if input.key = head.key then input.combine head :: tail
      else head :: insertInputByKey input tail

/-- Group records by `(muNumerator, heavyCoordinate)` and sum their occurrence numerators.

Zero-occurrence records are discarded.  The output order is deterministic but semantically
irrelevant; a generated certificate normally checks equality with this canonical fold. -/
def groupInputs : List EdgeInput → List EdgeInput
  | [] => []
  | input :: inputs =>
      if input.occurrenceNumerator = 0 then groupInputs inputs
      else insertInputByKey input (groupInputs inputs)

/-- Total occurrence numerator represented by a list of exact edge records. -/
def occurrenceTotal : List EdgeInput → Nat
  | [] => 0
  | input :: inputs => input.occurrenceNumerator + occurrenceTotal inputs

/-- Insertion adds exactly the inserted record's occurrence mass.

Proof sketch: recurse over the candidate list.  In the equal-key branch `combine` adds the two
numerators; otherwise the head is retained and the induction hypothesis handles the tail. -/
theorem occurrenceTotal_insertInputByKey (input : EdgeInput) (inputs : List EdgeInput) :
    occurrenceTotal (insertInputByKey input inputs) =
      input.occurrenceNumerator + occurrenceTotal inputs := by
  induction inputs with
  | nil => simp [insertInputByKey, occurrenceTotal]
  | cons head tail ih =>
      by_cases hkey : input.key = head.key
      · simp [insertInputByKey, hkey, occurrenceTotal, EdgeInput.combine, Nat.add_assoc]
      · simp [insertInputByKey, hkey, occurrenceTotal, ih, Nat.add_left_comm]

/-- Grouping preserves the exact total occurrence numerator, including zero-mass rows.

Proof sketch: induction discards only a zero numerator; every positive row is inserted and handled
by `occurrenceTotal_insertInputByKey`. -/
theorem occurrenceTotal_groupInputs (inputs : List EdgeInput) :
    occurrenceTotal (groupInputs inputs) = occurrenceTotal inputs := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      by_cases hzero : input.occurrenceNumerator = 0
      · simp [groupInputs, hzero, occurrenceTotal, ih]
      · simp only [groupInputs, hzero, if_false]
        rw [occurrenceTotal_insertInputByKey, ih]
        rfl

/-- Occurrence mass is additive under list concatenation. -/
theorem occurrenceTotal_append (left right : List EdgeInput) :
    occurrenceTotal (left ++ right) = occurrenceTotal left + occurrenceTotal right := by
  induction left with
  | nil => simp [occurrenceTotal]
  | cons input inputs ih =>
      simp [occurrenceTotal, ih, Nat.add_assoc]

/-- Grouping each chunk independently preserves the occurrence mass of the flattened family.

Proof sketch: induct over chunks, using additivity across concatenation and
`occurrenceTotal_groupInputs` on the head chunk. -/
theorem occurrenceTotal_flatten_map_groupInputs (chunks : List (List EdgeInput)) :
    occurrenceTotal ((chunks.map groupInputs).flatten) = occurrenceTotal chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons inputs chunks ih =>
      simp only [List.map_cons, List.flatten_cons, occurrenceTotal_append]
      rw [occurrenceTotal_groupInputs, ih]

end MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
