/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentRecurrence
import MatrixMultiplication.SimplifiedExponentRecurrenceGroupingCore

/-!
# Sufficient statistics for level-two retained-rate recurrences

The exact level-two recurrence assigns each active edge an occurrence numerator, an inner
three-letter parameter `muNumerator`, and one heavy coordinate.  Its contribution to every branch
is linear in the occurrence numerator once the latter two fields are fixed.  Consequently a large
edge list can be replaced by one record per `(muNumerator, heavyCoordinate)` key, whose occurrence
field is the sum over that key.

This file implements that grouping as a small executable fold and proves its semantic soundness.
The result is certificate-independent: generated clients may check a compact grouped list instead
of serializing every edge, while the theorem below transports all three branch rates back to the
original recurrence.
-/

namespace MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

/-- A zero-occurrence input contributes zero to every retained-rate branch. -/
@[simp] theorem inputRate_zero_occurrence (mu heavy : ℕ) (coordinate : Fin 3) :
    inputRate ⟨0, mu, heavy⟩ coordinate = 0 := by
  simp [inputRate, mass]

/-- Combining equal-key inputs adds their contribution to every branch.

Proof sketch: equality of keys identifies the inner parameter and heavy coordinate.  The remaining
identity is linearity of the dyadic occurrence mass in its numerator. -/
theorem inputRate_combine_of_key_eq
    (left right : EdgeInput) (hkey : left.key = right.key) (coordinate : Fin 3) :
    inputRate (left.combine right) coordinate =
      inputRate left coordinate + inputRate right coordinate := by
  rcases left with ⟨leftOccurrence, leftMu, leftHeavy⟩
  rcases right with ⟨rightOccurrence, rightMu, rightHeavy⟩
  have hmu : leftMu = rightMu := congrArg Prod.fst hkey
  have hheavy : leftHeavy = rightHeavy := congrArg Prod.snd hkey
  subst rightMu
  subst rightHeavy
  simp only [EdgeInput.combine, inputRate]
  rw [SimplifiedVolumeReconstruction.LogLinearForm.mass_add]
  rw [add_mul]
  rfl

/-- Inserting by key adds exactly the inserted input's branch contribution.

This theorem does not require the input list itself to be grouped; it is therefore also useful for
assembling independently certified grouped slices. -/
theorem inputBranchRate_insertInputByKey
    (input : EdgeInput) (inputs : List EdgeInput) (coordinate : Fin 3) :
    inputBranchRate (insertInputByKey input inputs) coordinate =
      inputRate input coordinate + inputBranchRate inputs coordinate := by
  induction inputs with
  | nil => simp [insertInputByKey, inputBranchRate]
  | cons head tail ih =>
      by_cases hkey : input.key = head.key
      · simp only [insertInputByKey, hkey, if_true, inputBranchRate,
          List.map_cons, List.sum_cons]
        rw [inputRate_combine_of_key_eq input head hkey]
        ring
      · simp only [insertInputByKey, hkey, if_false, inputBranchRate,
          List.map_cons, List.sum_cons]
        change inputRate head coordinate + inputBranchRate (insertInputByKey input tail) coordinate =
          inputRate input coordinate + (inputRate head coordinate + inputBranchRate tail coordinate)
        rw [ih]
        ring

/-- Grouping preserves every retained-rate branch.

Proof sketch: induct over the input list.  Zero-mass rows disappear by
`inputRate_zero_occurrence`; every other row is inserted with
`inputBranchRate_insertInputByKey`. -/
theorem inputBranchRate_groupInputs (inputs : List EdgeInput) (coordinate : Fin 3) :
    inputBranchRate (groupInputs inputs) coordinate =
      inputBranchRate inputs coordinate := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      by_cases hzero : input.occurrenceNumerator = 0
      · rcases input with ⟨occurrence, mu, heavy⟩
        simp only at hzero
        subst occurrence
        simp only [groupInputs, if_true]
        change inputBranchRate (groupInputs inputs) coordinate =
          inputRate ⟨0, mu, heavy⟩ coordinate + inputBranchRate inputs coordinate
        rw [inputRate_zero_occurrence, zero_add, ih]
      · simp only [groupInputs, hzero, if_false]
        rw [inputBranchRate_insertInputByKey, ih]
        rfl

/-- The grouped input form evaluates to the original ungrouped branch rate. -/
theorem inputBranchForm_groupInputs_eval (inputs : List EdgeInput) (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (inputBranchForm (groupInputs inputs) coordinate) =
      inputBranchRate inputs coordinate := by
  rw [inputBranchForm_eval, inputBranchRate_groupInputs]

/-! ## Independent chunk certificates

A single reduction of all 1,620 semantic edges may still be an inconvenient compiler boundary.
The following lemmas let a generated client check moderate input ranges independently, group each
range immediately, and merge only those much smaller summaries in its public certificate. -/

/-- The branch rate of a concatenated input list is the sum of the two branch rates. -/
theorem inputBranchRate_append (left right : List EdgeInput) (coordinate : Fin 3) :
    inputBranchRate (left ++ right) coordinate =
      inputBranchRate left coordinate + inputBranchRate right coordinate := by
  simp [inputBranchRate]

/-- Grouping every chunk before flattening preserves the branch rate of the flattened family.

Proof sketch: branch rates are additive over list concatenation, and
`inputBranchRate_groupInputs` applies independently to every chunk.  This is deliberately a
semantic equality rather than an equality of grouped-list order, so independently generated
chunks may use the executable canonical order without a global ordering proof. -/
theorem inputBranchRate_flatten_map_groupInputs
    (chunks : List (List EdgeInput)) (coordinate : Fin 3) :
    inputBranchRate ((chunks.map groupInputs).flatten) coordinate =
      inputBranchRate chunks.flatten coordinate := by
  induction chunks with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, inputBranchRate_append]
      rw [inputBranchRate_groupInputs, ih]

/-- Independently checked chunk summaries and one global merge preserve the flattened branch rate.

This is the certificate-facing associativity law.  The checker need not prove that grouping
commutes *definitionally* with concatenation, whose result order depends on last occurrences; it
proves the two displayed finite equalities and obtains the semantic equality needed downstream. -/
theorem inputBranchRate_groupedChunks
    (chunks groupedChunks : List (List EdgeInput)) (grouped : List EdgeInput)
    (hchunks : chunks.map groupInputs = groupedChunks)
    (hgroup : groupInputs groupedChunks.flatten = grouped)
    (coordinate : Fin 3) :
    inputBranchRate chunks.flatten coordinate = inputBranchRate grouped coordinate := by
  calc
    inputBranchRate chunks.flatten coordinate =
        inputBranchRate ((chunks.map groupInputs).flatten) coordinate :=
      (inputBranchRate_flatten_map_groupInputs chunks coordinate).symm
    _ = inputBranchRate groupedChunks.flatten coordinate := by rw [hchunks]
    _ = inputBranchRate (groupInputs groupedChunks.flatten) coordinate :=
      (inputBranchRate_groupInputs groupedChunks.flatten coordinate).symm
    _ = inputBranchRate grouped coordinate := by rw [hgroup]

/-- A checked grouped list is a sufficient statistic for an active recurrence branch.

Generated clients use `hgroup` as their only table-dependent equality.  The subsequent form
normalization sees the much shorter `grouped` list. -/
theorem activeBranchRateWithMassThree_eq_grouped
    (data : SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (grouped : List EdgeInput)
    (hgroup : groupInputs (activeInputsWithMassThree data massThree) = grouped)
    (coordinate : Fin 3) :
    activeBranchRateWithMassThree data massThree coordinate =
      Form.eval levelTwoFormBits (inputBranchForm grouped coordinate) := by
  rw [inputBranchForm_eval]
  unfold activeBranchRateWithMassThree
  rw [← hgroup, inputBranchRate_groupInputs]

/-- An arbitrary independently checked chunk family may replace the active input enumeration.

`hinputs` records only how the chosen ranges concatenate to the recurrence's active input list.
The remaining two premises are small grouping checks.  This form supports 10--15-row proof slices
without changing the public recurrence or its fixed historical 90-row chunking. -/
theorem activeBranchRateWithMassThree_eq_groupedChunkFamily
    (data : SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (chunks groupedChunks : List (List EdgeInput))
    (grouped : List EdgeInput)
    (hinputs : activeInputsWithMassThree data massThree = chunks.flatten)
    (hchunks : chunks.map groupInputs = groupedChunks)
    (hgroup : groupInputs groupedChunks.flatten = grouped)
    (coordinate : Fin 3) :
    activeBranchRateWithMassThree data massThree coordinate =
      Form.eval levelTwoFormBits (inputBranchForm grouped coordinate) := by
  rw [inputBranchForm_eval]
  unfold activeBranchRateWithMassThree
  rw [hinputs]
  exact inputBranchRate_groupedChunks chunks groupedChunks grouped hchunks hgroup coordinate

/-- Independently grouped edge ranges may be merged into one compact sufficient statistic.

`hchunks` is the only reduction-heavy, primary-table-dependent premise: each range can prove its
entry of this list equality in its own compilation unit.  `hgroup` then checks the small global
merge.  The conclusion is identical to `activeBranchRateWithMassThree_eq_grouped`, but it avoids
ever serializing the full ungrouped input list in one downstream module. -/
theorem activeBranchRateWithMassThree_eq_groupedChunks
    (data : SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (groupedChunks : List (List EdgeInput))
    (grouped : List EdgeInput)
    (hchunks :
      (activeInputChunksWithMassThree data massThree).map groupInputs = groupedChunks)
    (hgroup : groupInputs groupedChunks.flatten = grouped)
    (coordinate : Fin 3) :
    activeBranchRateWithMassThree data massThree coordinate =
      Form.eval levelTwoFormBits (inputBranchForm grouped coordinate) := by
  exact activeBranchRateWithMassThree_eq_groupedChunkFamily data massThree
    (activeInputChunksWithMassThree data massThree) groupedChunks grouped
    rfl hchunks hgroup coordinate

end

end MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
