/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourLocalGeometry
import MatrixMultiplication.DyadicNumeratorList

/-!
# Lightweight checker for parent-local beta-four data

One certificate record stores an ordered top slot, its split numerator, and the two beta-three
coordinate rows used by the parent convolution.  This module evaluates such records by either a
dense or zero-sparse scatter and proves that the two computations agree.  It contains no global
cache, generated data, entropy semantics, or real analysis.

`BetaFourLocalCertificate.lean` is the separate semantic adapter.  It projects the established
global caches into this representation and proves that local evaluation recovers the original
level-four recurrence.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.BetaFourLocalGeometry

/-- Exact data consumed from one parent-local ordered top slot. -/
structure BetaFourLocalSlotData where
  slot : ℕ
  splitNumerator : ℕ
  leftNumerators : Array ℕ
  rightNumerators : Array ℕ
  deriving DecidableEq, Repr

namespace BetaFourLocalSlotData

/-- Contribution of this local slot record to one requested parent-support symbol. -/
def gatherNumerator (data : BetaFourLocalSlotData)
    (parent coordinate symbol : ℕ) : ℕ :=
  let pair := pairAt parent data.slot
  let parentTotal := shapeCoordinate (parentShapeAt parent) coordinate
  let parentCode := ternarySupportCodeAt parentWordLength parentTotal symbol
  let leftCode := parentCode / 3 ^ childWordLength
  let rightCode := parentCode % 3 ^ childWordLength
  let leftSupport := ternarySupportCodes childWordLength
    (shapeCoordinate pair.1 coordinate)
  let rightSupport := ternarySupportCodes childWordLength
    (shapeCoordinate pair.2 coordinate)
  let leftSymbol := leftSupport.idxOf leftCode
  let rightSymbol := rightSupport.idxOf rightCode
  data.splitNumerator * (data.leftNumerators[leftSymbol]?.getD 0) *
    (data.rightNumerators[rightSymbol]?.getD 0)

/-- Every padded entry outside the two true child supports is zero. -/
def IsSupportZero (data : BetaFourLocalSlotData) (parent coordinate : ℕ) : Prop :=
  let pair := pairAt parent data.slot
  (∀ symbol,
      (ternarySupportCodes childWordLength
        (shapeCoordinate pair.1 coordinate)).length ≤ symbol →
      data.leftNumerators[symbol]?.getD 0 = 0) ∧
    (∀ symbol,
      (ternarySupportCodes childWordLength
        (shapeCoordinate pair.2 coordinate)).length ≤ symbol →
      data.rightNumerators[symbol]?.getD 0 = 0)

/-- Scatter one pair of child symbols from this local record into a padded parent row. -/
def addContribution (data : BetaFourLocalSlotData) (parent coordinate : ℕ)
    (leftSymbol rightSymbol : ℕ) (row : Array ℕ) : Array ℕ :=
  let leftNumerator := data.leftNumerators[leftSymbol]?.getD 0
  if leftNumerator = 0 then row
  else
    let rightNumerator := data.rightNumerators[rightSymbol]?.getD 0
    if rightNumerator = 0 then row
    else
      addNumeratorAt row
        (concatenatedParentSlotForPair parent coordinate (pairAt parent data.slot)
          leftSymbol rightSymbol)
        (data.splitNumerator * leftNumerator * rightNumerator)

/-- Dense local scatter for one top-slot record. -/
def addToRow (data : BetaFourLocalSlotData) (parent coordinate : ℕ)
    (row : Array ℕ) : Array ℕ :=
  if data.splitNumerator = 0 then row
  else
    (List.range childSupportWidth).foldl (fun row leftSymbol ↦
      (List.range childSupportWidth).foldl (fun row rightSymbol ↦
        data.addContribution parent coordinate leftSymbol rightSymbol row) row) row

/-- Nonzero symbols of one locally serialized child row. -/
def nonzeroSymbols (row : Array ℕ) : List ℕ :=
  (List.range childSupportWidth).filter fun symbol ↦
    decide (row[symbol]?.getD 0 ≠ 0)

/-- Zero-sparse local scatter for one top-slot record. -/
def addToRowSparse (data : BetaFourLocalSlotData) (parent coordinate : ℕ)
    (row : Array ℕ) : Array ℕ :=
  if data.splitNumerator = 0 then row
  else
    (nonzeroSymbols data.leftNumerators).foldl (fun row leftSymbol ↦
      (nonzeroSymbols data.rightNumerators).foldl (fun row rightSymbol ↦
        data.addContribution parent coordinate leftSymbol rightSymbol row) row) row

private theorem foldl_filter_eq_of_false_step {α β : Type*}
    (keep : β → Bool) (step : α → β → α)
    (hstep : ∀ accumulator value, keep value = false →
      step accumulator value = accumulator)
    (values : List β) (initial : α) :
    (values.filter keep).foldl step initial = values.foldl step initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      cases hkeep : keep value with
      | false =>
          simp only [List.filter_cons, hkeep, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
          rw [hstep initial value hkeep]
          exact ih initial
      | true =>
          simp only [List.filter_cons, hkeep, ↓reduceIte, List.foldl_cons]
          exact ih (step initial value)

private theorem foldl_eq_self_of_step {α β : Type*}
    (step : α → β → α) (hstep : ∀ accumulator value, step accumulator value = accumulator)
    (values : List β) (initial : α) : values.foldl step initial = initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      rw [List.foldl_cons, hstep initial value]
      exact ih initial

/-- Filtering zero child entries leaves a local slot scatter unchanged.

Proof sketch: the inner fold may discard a right symbol because the second zero guard makes its
step the identity.  If a left symbol is discarded, the first zero guard makes the entire inner
fold the identity. -/
theorem addToRowSparse_eq_addToRow (data : BetaFourLocalSlotData)
    (parent coordinate : ℕ) (row : Array ℕ) :
    data.addToRowSparse parent coordinate row = data.addToRow parent coordinate row := by
  unfold addToRowSparse addToRow
  by_cases hsplit : data.splitNumerator = 0
  · simp [hsplit]
  · simp only [hsplit, ↓reduceIte]
    have hright (leftSymbol : ℕ) (initial : Array ℕ) :
        (nonzeroSymbols data.rightNumerators).foldl
            (fun row rightSymbol ↦
              data.addContribution parent coordinate leftSymbol rightSymbol row) initial =
          (List.range childSupportWidth).foldl
            (fun row rightSymbol ↦
              data.addContribution parent coordinate leftSymbol rightSymbol row) initial := by
      apply foldl_filter_eq_of_false_step
      intro accumulator rightSymbol hkeep
      have hzero : data.rightNumerators[rightSymbol]?.getD 0 = 0 := by
        simpa [Bool.decide_eq_false] using hkeep
      simp [addContribution, hzero]
    simp_rw [hright]
    apply foldl_filter_eq_of_false_step
    intro accumulator leftSymbol hkeep
    have hzero : data.leftNumerators[leftSymbol]?.getD 0 = 0 := by
      simpa [Bool.decide_eq_false] using hkeep
    apply foldl_eq_self_of_step
    intro inner rightSymbol
    simp [addContribution, hzero]

end BetaFourLocalSlotData

/-- Complete lightweight input for one parent, region, and physical coordinate. -/
structure BetaFourLocalData where
  slots : List BetaFourLocalSlotData
  deriving DecidableEq, Repr

namespace BetaFourLocalData

/-- Pointwise numerator gathered solely from the parent-local records. -/
def gatherNumerator (data : BetaFourLocalData) (parent coordinate symbol : ℕ) : ℕ :=
  if symbol <
      (ternarySupportCodes parentWordLength
        (shapeCoordinate (parentShapeAt parent) coordinate)).length then
    (data.slots.map fun slotData ↦
      slotData.gatherNumerator parent coordinate symbol).sum
  else 0

/-- Gather a bounded list of parent-support symbols from local records. -/
def gatherOn (data : BetaFourLocalData) (parent coordinate : ℕ)
    (symbols : List ℕ) : List ℕ :=
  symbols.map (data.gatherNumerator parent coordinate)

/-- Every local slot record has zero padding outside its true coordinate support. -/
def IsSupportZero (data : BetaFourLocalData) (parent coordinate : ℕ) : Prop :=
  ∀ slotData ∈ data.slots, slotData.IsSupportZero parent coordinate

/-- Dense parent row obtained by scattering only the local slot records. -/
def scatter (data : BetaFourLocalData) (parent coordinate : ℕ) : List ℕ :=
  (data.slots.foldl (fun row slotData ↦ slotData.addToRow parent coordinate row)
    (Array.replicate parentSupportWidth 0)).toList

/-- Zero-sparse parent scatter obtained from the same local records. -/
def scatterSparse (data : BetaFourLocalData) (parent coordinate : ℕ) : List ℕ :=
  (data.slots.foldl (fun row slotData ↦ slotData.addToRowSparse parent coordinate row)
    (Array.replicate parentSupportWidth 0)).toList

/-- The sparse and dense local scatter evaluators are exactly equal.

Proof sketch: replace the sparse step pointwise by `addToRowSparse_eq_addToRow`; the initial row
and slot order are identical. -/
theorem scatterSparse_eq_scatter (data : BetaFourLocalData) (parent coordinate : ℕ) :
    data.scatterSparse parent coordinate = data.scatter parent coordinate := by
  unfold scatterSparse scatter
  have hstep :
      (fun row (slotData : BetaFourLocalSlotData) ↦
        slotData.addToRowSparse parent coordinate row) =
        (fun row (slotData : BetaFourLocalSlotData) ↦
          slotData.addToRow parent coordinate row) := by
    funext row slotData
    exact slotData.addToRowSparse_eq_addToRow parent coordinate row
  rw [hstep]

/-- Local gathering respects concatenation of independently checked symbol shards. -/
theorem gatherOn_append (data : BetaFourLocalData) (parent coordinate : ℕ)
    (left right : List ℕ) :
    data.gatherOn parent coordinate (left ++ right) =
      data.gatherOn parent coordinate left ++ data.gatherOn parent coordinate right := by
  simp [gatherOn]

end BetaFourLocalData

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
