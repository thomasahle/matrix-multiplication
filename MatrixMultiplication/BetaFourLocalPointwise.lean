/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourLocalChecker

/-!
# Pointwise evaluation of a parent-local beta-four scatter

The dense evaluator updates a persistent 1,107-cell array once for every nonzero source product.
That is a useful executable specification, but reducing the whole closed array can retain several
gigabytes of intermediate state.  This module projects the same fold to one requested output
position.  The projection theorem is generic: generated clients may check bounded position shards
without ever constructing the dense array, then recover the original scatter semantics.

Unlike the inverse-code gather API, this pointwise evaluator scans exactly the source symbols used
by the scatter.  Its soundness therefore needs no padding or support assumption and remains valid
for arbitrary local rows.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.BetaFourLocalGeometry

/-- Read one padded array position, returning zero out of range. -/
def betaFourRowNumeratorAt (row : Array ℕ) (position : ℕ) : ℕ :=
  row[position]?.getD 0

private theorem size_localAddNumeratorAt (row : Array ℕ) (target value : ℕ) :
    (addNumeratorAt row target value).size = row.size := by
  unfold addNumeratorAt
  split <;> simp

/-- Reading one updated position is the old value plus the contribution targeted there. -/
private theorem betaFourRowNumeratorAt_addNumeratorAt (row : Array ℕ)
    (target value position : ℕ) (hposition : position < row.size) :
    betaFourRowNumeratorAt (addNumeratorAt row target value) position =
      betaFourRowNumeratorAt row position + if target = position then value else 0 := by
  unfold addNumeratorAt betaFourRowNumeratorAt
  by_cases htarget : target < row.size
  · simp only [htarget, ↓reduceIte, Array.getElem?_modify]
    by_cases heq : target = position
    · subst target
      simp [hposition]
    · simp [heq]
  · have hne : target ≠ position := by
      intro heq
      subst target
      exact htarget hposition
    simp [htarget, hne]

private theorem size_foldl_eq {α : Type*} (step : Array ℕ → α → Array ℕ)
    (hstep : ∀ row value, (step row value).size = row.size)
    (values : List α) (initial : Array ℕ) :
    (values.foldl step initial).size = initial.size := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      calc
        ((value :: values).foldl step initial).size =
            (values.foldl step (step initial value)).size := rfl
        _ = (step initial value).size := ih (step initial value)
        _ = initial.size := hstep initial value

private theorem foldl_projection {α : Type*}
    (rowStep : Array ℕ → α → Array ℕ) (natStep : ℕ → α → ℕ)
    (position : ℕ)
    (hsize : ∀ row value, (rowStep row value).size = row.size)
    (hread : ∀ row value, position < row.size →
      betaFourRowNumeratorAt (rowStep row value) position =
        natStep (betaFourRowNumeratorAt row position) value)
    (values : List α) (initial : Array ℕ) (hposition : position < initial.size) :
    betaFourRowNumeratorAt (values.foldl rowStep initial) position =
      values.foldl natStep (betaFourRowNumeratorAt initial position) := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      have hnext : position < (rowStep initial value).size := by
        rw [hsize initial value]
        exact hposition
      calc
        betaFourRowNumeratorAt ((value :: values).foldl rowStep initial) position =
            betaFourRowNumeratorAt
              (values.foldl rowStep (rowStep initial value)) position := rfl
        _ = values.foldl natStep
              (betaFourRowNumeratorAt (rowStep initial value) position) :=
            ih (rowStep initial value) hnext
        _ = values.foldl natStep
              (natStep (betaFourRowNumeratorAt initial position) value) := by
            rw [hread initial value hposition]
        _ = (value :: values).foldl natStep
              (betaFourRowNumeratorAt initial position) := rfl

namespace BetaFourLocalSlotData

/-- Scalar update contributed at one requested parent position by one child-symbol pair. -/
def addContributionAt (data : BetaFourLocalSlotData) (parent coordinate position : ℕ)
    (accumulator leftSymbol rightSymbol : ℕ) : ℕ :=
  let leftNumerator := data.leftNumerators[leftSymbol]?.getD 0
  if leftNumerator = 0 then accumulator
  else
    let rightNumerator := data.rightNumerators[rightSymbol]?.getD 0
    if rightNumerator = 0 then accumulator
    else
      let target := concatenatedParentSlotForPair parent coordinate (pairAt parent data.slot)
        leftSymbol rightSymbol
      if target = position then
        accumulator + data.splitNumerator * leftNumerator * rightNumerator
      else accumulator

/-- Project the sparse nested child-symbol fold to one requested parent position. -/
def addToNumeratorAt (data : BetaFourLocalSlotData) (parent coordinate position : ℕ)
    (accumulator : ℕ) : ℕ :=
  if data.splitNumerator = 0 then accumulator
  else
    (nonzeroSymbols data.leftNumerators).foldl (fun accumulator leftSymbol ↦
      (nonzeroSymbols data.rightNumerators).foldl (fun accumulator rightSymbol ↦
        data.addContributionAt parent coordinate position accumulator leftSymbol rightSymbol)
        accumulator) accumulator

/-- Contribution of one local top slot to one requested parent position. -/
def numeratorAt (data : BetaFourLocalSlotData) (parent coordinate position : ℕ) : ℕ :=
  data.addToNumeratorAt parent coordinate position 0

private theorem size_addContribution (data : BetaFourLocalSlotData)
    (parent coordinate leftSymbol rightSymbol : ℕ) (row : Array ℕ) :
    (data.addContribution parent coordinate leftSymbol rightSymbol row).size = row.size := by
  by_cases hleft : data.leftNumerators[leftSymbol]?.getD 0 = 0
  · simp [addContribution, hleft]
  · by_cases hright : data.rightNumerators[rightSymbol]?.getD 0 = 0
    · simp [addContribution, hleft, hright]
    · simpa [addContribution, hleft, hright] using size_localAddNumeratorAt row
        (concatenatedParentSlotForPair parent coordinate (pairAt parent data.slot)
          leftSymbol rightSymbol)
        (data.splitNumerator * data.leftNumerators[leftSymbol]?.getD 0 *
          data.rightNumerators[rightSymbol]?.getD 0)

private theorem size_addToRowSparse (data : BetaFourLocalSlotData)
    (parent coordinate : ℕ) (row : Array ℕ) :
    (data.addToRowSparse parent coordinate row).size = row.size := by
  unfold addToRowSparse
  split
  · rfl
  · apply size_foldl_eq
    intro outer leftSymbol
    apply size_foldl_eq
    intro inner rightSymbol
    exact data.size_addContribution parent coordinate leftSymbol rightSymbol inner

private theorem betaFourRowNumeratorAt_addContribution (data : BetaFourLocalSlotData)
    (parent coordinate position leftSymbol rightSymbol : ℕ) (row : Array ℕ)
    (hposition : position < row.size) :
    betaFourRowNumeratorAt
        (data.addContribution parent coordinate leftSymbol rightSymbol row) position =
      data.addContributionAt parent coordinate position
        (betaFourRowNumeratorAt row position) leftSymbol rightSymbol := by
  by_cases hleft : data.leftNumerators[leftSymbol]?.getD 0 = 0
  · simp [addContribution, addContributionAt, hleft]
  · by_cases hright : data.rightNumerators[rightSymbol]?.getD 0 = 0
    · simp [addContribution, addContributionAt, hleft, hright]
    · simp only [addContribution, addContributionAt, hleft, hright, ↓reduceIte]
      rw [betaFourRowNumeratorAt_addNumeratorAt _ _ _ _ hposition]
      by_cases htarget :
          concatenatedParentSlotForPair parent coordinate (pairAt parent data.slot)
              leftSymbol rightSymbol = position <;>
        simp [htarget]

/-- Projecting a sparse slot update to one position is the scalar slot update. -/
theorem betaFourRowNumeratorAt_addToRowSparse (data : BetaFourLocalSlotData)
    (parent coordinate position : ℕ) (row : Array ℕ)
    (hposition : position < row.size) :
    betaFourRowNumeratorAt (data.addToRowSparse parent coordinate row) position =
      data.addToNumeratorAt parent coordinate position
        (betaFourRowNumeratorAt row position) := by
  unfold addToRowSparse addToNumeratorAt
  split
  · rfl
  · apply foldl_projection
    · intro outer leftSymbol
      apply size_foldl_eq
      intro inner rightSymbol
      exact data.size_addContribution parent coordinate leftSymbol rightSymbol inner
    · intro outer leftSymbol houter
      apply foldl_projection
      · intro inner rightSymbol
        exact data.size_addContribution parent coordinate leftSymbol rightSymbol inner
      · intro inner rightSymbol hinner
        exact data.betaFourRowNumeratorAt_addContribution
          parent coordinate position leftSymbol rightSymbol inner hinner
      · exact houter
    · exact hposition

end BetaFourLocalSlotData

namespace BetaFourLocalData

/-- Fold every local top-slot contribution into one requested parent position. -/
def addToNumeratorAt (data : BetaFourLocalData) (parent coordinate position : ℕ)
    (accumulator : ℕ) : ℕ :=
  data.slots.foldl (fun accumulator slotData ↦
    slotData.addToNumeratorAt parent coordinate position accumulator) accumulator

/-- Exact numerator at one parent position, evaluated without constructing the parent array. -/
def numeratorAt (data : BetaFourLocalData) (parent coordinate position : ℕ) : ℕ :=
  data.addToNumeratorAt parent coordinate position 0

/-- Evaluate requested parent positions independently and in the supplied order. -/
def scatterOn (data : BetaFourLocalData) (parent coordinate : ℕ)
    (positions : List ℕ) : List ℕ :=
  positions.map (data.numeratorAt parent coordinate)

/-- Array-valued implementation underlying the public sparse-row list. -/
def scatterSparseArray (data : BetaFourLocalData) (parent coordinate : ℕ) : Array ℕ :=
  data.slots.foldl (fun row slotData ↦ slotData.addToRowSparse parent coordinate row)
    (Array.replicate parentSupportWidth 0)

private theorem size_scatterSparseArray (data : BetaFourLocalData) (parent coordinate : ℕ) :
    (data.scatterSparseArray parent coordinate).size = parentSupportWidth := by
  unfold scatterSparseArray
  have hfold (slots : List BetaFourLocalSlotData) (row : Array ℕ) :
      (slots.foldl
        (fun row slotData ↦ slotData.addToRowSparse parent coordinate row) row).size =
        row.size := by
    induction slots generalizing row with
    | nil => rfl
    | cons slotData slots ih =>
        calc
          ((slotData :: slots).foldl
              (fun row slotData ↦ slotData.addToRowSparse parent coordinate row) row).size =
            (slots.foldl
              (fun row slotData ↦ slotData.addToRowSparse parent coordinate row)
              (slotData.addToRowSparse parent coordinate row)).size := rfl
          _ = (slotData.addToRowSparse parent coordinate row).size := ih _
          _ = row.size := slotData.size_addToRowSparse parent coordinate row
  calc
    (data.slots.foldl
        (fun row slotData ↦ slotData.addToRowSparse parent coordinate row)
        (Array.replicate parentSupportWidth 0)).size =
      (Array.replicate parentSupportWidth 0).size := hfold _ _
    _ = parentSupportWidth := by simp

/-- Pointwise evaluation agrees with reading the sparse array evaluator.

Proof sketch: `foldl_projection` commutes the fixed-position read through the outer slot fold.
The corresponding slot theorem commutes it through both child-symbol folds and one guarded array
update.  The replicated initial row reads as zero at every in-range position. -/
theorem betaFourRowNumeratorAt_scatterSparseArray (data : BetaFourLocalData)
    (parent coordinate position : ℕ) (hposition : position < parentSupportWidth) :
    betaFourRowNumeratorAt (data.scatterSparseArray parent coordinate) position =
      data.numeratorAt parent coordinate position := by
  unfold scatterSparseArray numeratorAt addToNumeratorAt
  calc
    betaFourRowNumeratorAt
        (data.slots.foldl
          (fun row slotData ↦ slotData.addToRowSparse parent coordinate row)
          (Array.replicate parentSupportWidth 0)) position =
      data.slots.foldl
        (fun accumulator slotData ↦
          slotData.addToNumeratorAt parent coordinate position accumulator)
        (betaFourRowNumeratorAt (Array.replicate parentSupportWidth 0) position) :=
      foldl_projection
        (fun row slotData ↦ slotData.addToRowSparse parent coordinate row)
        (fun accumulator slotData ↦
          slotData.addToNumeratorAt parent coordinate position accumulator)
        position
        (fun row slotData ↦ slotData.size_addToRowSparse parent coordinate row)
        (fun row slotData hrow ↦
          slotData.betaFourRowNumeratorAt_addToRowSparse
            parent coordinate position row hrow)
        data.slots (Array.replicate parentSupportWidth 0) (by simpa using hposition)
    _ = data.slots.foldl
          (fun accumulator slotData ↦
            slotData.addToNumeratorAt parent coordinate position accumulator) 0 := by
      simp [betaFourRowNumeratorAt, hposition]

/-- The public sparse row is the list view of the private array evaluator. -/
theorem scatterSparse_eq_scatterSparseArray_toList (data : BetaFourLocalData)
    (parent coordinate : ℕ) :
    data.scatterSparse parent coordinate =
      (data.scatterSparseArray parent coordinate).toList := by
  rfl

/-- A full range of independent pointwise checks is exactly the sparse parent row.

Proof sketch: both lists have length `parentSupportWidth`.  At an in-range index, the mapped range
contains that same index and `betaFourRowNumeratorAt_scatterSparseArray` identifies its value with
the array read.  Both optional reads are `none` outside the common length. -/
theorem scatterOn_range_eq_scatterSparse (data : BetaFourLocalData)
    (parent coordinate : ℕ) :
    data.scatterOn parent coordinate (List.range parentSupportWidth) =
      data.scatterSparse parent coordinate := by
  rw [scatterSparse_eq_scatterSparseArray_toList]
  apply List.ext_getElem?
  intro position
  by_cases hposition : position < parentSupportWidth
  · simp only [scatterOn]
    rw [List.getElem?_map, List.getElem?_range hposition]
    simp only [Option.map_some, Array.getElem?_toList]
    rw [show (data.scatterSparseArray parent coordinate)[position]? =
        some (betaFourRowNumeratorAt (data.scatterSparseArray parent coordinate) position) by
      simp [betaFourRowNumeratorAt, size_scatterSparseArray, hposition]]
    rw [betaFourRowNumeratorAt_scatterSparseArray data parent coordinate position hposition]
  · have hsize : (data.scatterSparseArray parent coordinate).size = parentSupportWidth :=
      data.size_scatterSparseArray parent coordinate
    simp [scatterOn, hposition, hsize]

/-- Pointwise evaluation of the full padded range recovers the dense semantic scatter. -/
theorem scatterOn_range_eq_scatter (data : BetaFourLocalData) (parent coordinate : ℕ) :
    data.scatterOn parent coordinate (List.range parentSupportWidth) =
      data.scatter parent coordinate := by
  rw [scatterOn_range_eq_scatterSparse, scatterSparse_eq_scatter]

/-- Pointwise scattering respects concatenation of independently checked position shards. -/
theorem scatterOn_append (data : BetaFourLocalData) (parent coordinate : ℕ)
    (left right : List ℕ) :
    data.scatterOn parent coordinate (left ++ right) =
      data.scatterOn parent coordinate left ++ data.scatterOn parent coordinate right := by
  simp [scatterOn]

end BetaFourLocalData

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
