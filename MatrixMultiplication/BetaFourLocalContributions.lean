/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourLocalPointwise

/-!
# Routed contribution lists for parent-local beta-four checks

`BetaFourLocalPointwise` projects the exact source scatter to one output position.  Re-evaluating
that projection independently at every position, however, also repeats the comparatively expensive
ternary-support routing calculation.  This module factors the computation into two phases:

1. route every nonzero child-symbol pair once, producing a compact list of optional contributions;
2. sum that already-routed list at any requested collection of output positions.

The optional entries deliberately preserve the source fold's two zero guards.  This makes the
semantic comparison unconditional: it does not assume valid padding, unique routes, or a support
invariant.  Generated clients may therefore prove one exact routing certificate and then check
their arithmetic in small position shards.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.BetaFourLocalGeometry

/-- One source contribution after its parent-support destination has been computed. -/
structure BetaFourRoutedContribution where
  target : ℕ
  numerator : ℕ
  deriving DecidableEq, Repr

namespace BetaFourRoutedContribution

/-- Apply an optional routed contribution at one requested output position. -/
def addOptionalAt (position accumulator : ℕ) : Option BetaFourRoutedContribution → ℕ
  | none => accumulator
  | some contribution =>
      if contribution.target = position then accumulator + contribution.numerator
      else accumulator

/-- Sum a routed contribution list at one output position. -/
def numeratorAt (contributions : List (Option BetaFourRoutedContribution))
    (position : ℕ) : ℕ :=
  contributions.foldl (addOptionalAt position) 0

/-- Evaluate an already-routed contribution list at the requested output positions. -/
def scatterOn (contributions : List (Option BetaFourRoutedContribution))
    (positions : List ℕ) : List ℕ :=
  positions.map (numeratorAt contributions)

/-- Routed pointwise scattering respects concatenation of position shards. -/
theorem scatterOn_append (contributions : List (Option BetaFourRoutedContribution))
    (left right : List ℕ) :
    scatterOn contributions (left ++ right) =
      scatterOn contributions left ++ scatterOn contributions right := by
  simp [scatterOn]

/-- Apply one optional routed contribution to a dense accumulator row. -/
def addOptionalToRow (row : Array ℕ) : Option BetaFourRoutedContribution → Array ℕ
  | none => row
  | some contribution =>
      addNumeratorAt row contribution.target contribution.numerator

/-- Evaluate every routed contribution with one linear dense-array fold. -/
def scatterArray (contributions : List (Option BetaFourRoutedContribution)) : Array ℕ :=
  contributions.foldl addOptionalToRow (Array.replicate parentSupportWidth 0)

private theorem size_addOptionalToRow (row : Array ℕ)
    (contribution : Option BetaFourRoutedContribution) :
    (addOptionalToRow row contribution).size = row.size := by
  cases contribution with
  | none => rfl
  | some contribution =>
      by_cases htarget : contribution.target < row.size
      · simp [addOptionalToRow, addNumeratorAt, htarget]
      · simp [addOptionalToRow, addNumeratorAt, htarget]

private theorem size_scatterArray (contributions : List (Option BetaFourRoutedContribution)) :
    (scatterArray contributions).size = parentSupportWidth := by
  unfold scatterArray
  have hfold (values : List (Option BetaFourRoutedContribution)) (row : Array ℕ) :
      (values.foldl addOptionalToRow row).size = row.size := by
    induction values generalizing row with
    | nil => rfl
    | cons value values ih =>
        calc
          ((value :: values).foldl addOptionalToRow row).size =
              (values.foldl addOptionalToRow (addOptionalToRow row value)).size := rfl
          _ = (addOptionalToRow row value).size := ih _
          _ = row.size := size_addOptionalToRow row value
  calc
    (contributions.foldl addOptionalToRow
        (Array.replicate parentSupportWidth 0)).size =
      (Array.replicate parentSupportWidth 0).size := hfold _ _
    _ = parentSupportWidth := by simp

private theorem betaFourRowNumeratorAt_addOptionalToRow (row : Array ℕ)
    (contribution : Option BetaFourRoutedContribution) (position : ℕ)
    (hposition : position < row.size) :
    betaFourRowNumeratorAt (addOptionalToRow row contribution) position =
      addOptionalAt position (betaFourRowNumeratorAt row position) contribution := by
  cases contribution with
  | none => rfl
  | some contribution =>
      rcases contribution with ⟨target, numerator⟩
      unfold addOptionalToRow addOptionalAt addNumeratorAt betaFourRowNumeratorAt
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

private theorem betaFourRowNumeratorAt_foldl_addOptionalToRow
    (values : List (Option BetaFourRoutedContribution)) (row : Array ℕ)
    (position : ℕ) (hposition : position < row.size) :
    betaFourRowNumeratorAt (values.foldl addOptionalToRow row) position =
      values.foldl (addOptionalAt position) (betaFourRowNumeratorAt row position) := by
  induction values generalizing row with
  | nil => rfl
  | cons value values ih =>
      have hnext : position < (addOptionalToRow row value).size := by
        rw [size_addOptionalToRow row value]
        exact hposition
      calc
        betaFourRowNumeratorAt
            ((value :: values).foldl addOptionalToRow row) position =
          betaFourRowNumeratorAt
            (values.foldl addOptionalToRow (addOptionalToRow row value)) position := rfl
        _ = values.foldl (addOptionalAt position)
              (betaFourRowNumeratorAt (addOptionalToRow row value) position) :=
            ih (addOptionalToRow row value) hnext
        _ = values.foldl (addOptionalAt position)
              (addOptionalAt position (betaFourRowNumeratorAt row position) value) := by
            rw [betaFourRowNumeratorAt_addOptionalToRow row value position hposition]
        _ = (value :: values).foldl (addOptionalAt position)
              (betaFourRowNumeratorAt row position) := rfl

/-- Reading the one-pass routed array agrees with the scalar routed evaluator. -/
theorem betaFourRowNumeratorAt_scatterArray
    (contributions : List (Option BetaFourRoutedContribution))
    (position : ℕ) (hposition : position < parentSupportWidth) :
    betaFourRowNumeratorAt (scatterArray contributions) position =
      numeratorAt contributions position := by
  unfold scatterArray numeratorAt
  rw [betaFourRowNumeratorAt_foldl_addOptionalToRow _ _ position (by simpa using hposition)]
  simp [betaFourRowNumeratorAt, hposition]

/-- The one-pass routed array is exactly the full pointwise routed row.

Proof sketch: both sides have the common parent-support length.  At every in-range index, the array
projection theorem identifies the dense read with the scalar fold used by `scatterOn`; both
optional reads are absent beyond that length.
-/
theorem scatterArray_toList_eq_scatterOn_range
    (contributions : List (Option BetaFourRoutedContribution)) :
    (scatterArray contributions).toList =
      scatterOn contributions (List.range parentSupportWidth) := by
  apply List.ext_getElem?
  intro position
  by_cases hposition : position < parentSupportWidth
  · simp only [scatterOn]
    rw [List.getElem?_map, List.getElem?_range hposition]
    simp only [Option.map_some, Array.getElem?_toList]
    rw [show (scatterArray contributions)[position]? =
        some (betaFourRowNumeratorAt (scatterArray contributions) position) by
      simp [betaFourRowNumeratorAt, size_scatterArray, hposition]]
    rw [betaFourRowNumeratorAt_scatterArray contributions position hposition]
  · have hsize : (scatterArray contributions).size = parentSupportWidth :=
      size_scatterArray contributions
    simp [scatterOn, hposition, hsize]

end BetaFourRoutedContribution

namespace BetaFourLocalSlotData

/-- Parent support materialized once for a local slot's routing fold. -/
def routedParentSupport (parent coordinate : ℕ) : List ℕ :=
  ternarySupportCodes parentWordLength
    (shapeCoordinate (parentShapeAt parent) coordinate)

/-- Left child support materialized once for a local slot's routing fold. -/
def routedLeftSupport (data : BetaFourLocalSlotData) (parent coordinate : ℕ) : List ℕ :=
  ternarySupportCodes childWordLength
    (shapeCoordinate (pairAt parent data.slot).1 coordinate)

/-- Right child support materialized once for a local slot's routing fold. -/
def routedRightSupport (data : BetaFourLocalSlotData) (parent coordinate : ℕ) : List ℕ :=
  ternarySupportCodes childWordLength
    (shapeCoordinate (pairAt parent data.slot).2 coordinate)

/-- Route one guarded pair using support-code lists already computed by the surrounding fold. -/
def routedContributionFromSupports (data : BetaFourLocalSlotData)
    (parentSupport leftSupport rightSupport : List ℕ)
    (leftSymbol rightSymbol : ℕ) : Option BetaFourRoutedContribution :=
  let leftNumerator := data.leftNumerators[leftSymbol]?.getD 0
  if leftNumerator = 0 then none
  else
    let rightNumerator := data.rightNumerators[rightSymbol]?.getD 0
    if rightNumerator = 0 then none
    else
      some {
        target := concatenatedParentSlotFromSupports parentSupport leftSupport rightSupport
          leftSymbol rightSymbol
        numerator := data.splitNumerator * leftNumerator * rightNumerator
      }

/-- The routed contribution after the two nonzero guards have been discharged.

Generated certificates use this constructor to describe a fixed-left row without repeating the
already-stored split and child numerators in every output record.  The companion theorem below is
the semantic boundary: callers must prove that both guarded numerators are nonzero.
-/
def routedContributionUncheckedFromSupports (data : BetaFourLocalSlotData)
    (parentSupport leftSupport rightSupport : List ℕ)
    (leftSymbol rightSymbol : ℕ) : BetaFourRoutedContribution :=
  {
    target := concatenatedParentSlotFromSupports parentSupport leftSupport rightSupport
      leftSymbol rightSymbol
    numerator := data.splitNumerator *
      data.leftNumerators[leftSymbol]?.getD 0 *
      data.rightNumerators[rightSymbol]?.getD 0
  }

/-- Once both source numerators are nonzero, guarded and unchecked routing agree. -/
theorem routedContributionFromSupports_eq_some_unchecked
    (data : BetaFourLocalSlotData) (parentSupport leftSupport rightSupport : List ℕ)
    (leftSymbol rightSymbol : ℕ)
    (hleft : data.leftNumerators[leftSymbol]?.getD 0 ≠ 0)
    (hright : data.rightNumerators[rightSymbol]?.getD 0 ≠ 0) :
    data.routedContributionFromSupports parentSupport leftSupport rightSupport
        leftSymbol rightSymbol =
      some (data.routedContributionUncheckedFromSupports
        parentSupport leftSupport rightSupport leftSymbol rightSymbol) := by
  simp [routedContributionFromSupports, routedContributionUncheckedFromSupports, hleft, hright]

/-- Route one guarded child-symbol pair without applying it to an output row.

The result is optional so that the representation retains the exact two zero guards from
`addContributionAt`.  Entries reached through `nonzeroSymbols` are normally all `some`, but the
proof does not rely on that fact.
-/
def routedContribution (data : BetaFourLocalSlotData) (parent coordinate : ℕ)
    (leftSymbol rightSymbol : ℕ) : Option BetaFourRoutedContribution :=
  data.routedContributionFromSupports
    (routedParentSupport parent coordinate)
    (data.routedLeftSupport parent coordinate)
    (data.routedRightSupport parent coordinate)
    leftSymbol rightSymbol

/-- Route one fixed-left row using support-code lists supplied by a checked certificate. -/
def routedContributionsForLeftFromSupports (data : BetaFourLocalSlotData)
    (parentSupport leftSupport rightSupport : List ℕ) (leftSymbol : ℕ) :
    List (Option BetaFourRoutedContribution) :=
  (nonzeroSymbols data.rightNumerators).map fun rightSymbol ↦
    data.routedContributionFromSupports parentSupport leftSupport rightSupport
      leftSymbol rightSymbol

/-- A compact fixed-left route after removing guards known to succeed.

Unlike a literal routed row, this representation stores each split and child numerator only once,
in `data`.  Its evaluation is still bounded by the at-most-nineteen nonzero right symbols.
-/
def routedContributionsForLeftUncheckedFromSupports (data : BetaFourLocalSlotData)
    (parentSupport leftSupport rightSupport : List ℕ) (leftSymbol : ℕ) :
    List (Option BetaFourRoutedContribution) :=
  (nonzeroSymbols data.rightNumerators).map fun rightSymbol ↦
    some (data.routedContributionUncheckedFromSupports
      parentSupport leftSupport rightSupport leftSymbol rightSymbol)

/-- Membership in `nonzeroSymbols` certifies that the corresponding array entry is nonzero. -/
theorem getD_ne_zero_of_mem_nonzeroSymbols (row : Array ℕ) (symbol : ℕ)
    (hmem : symbol ∈ nonzeroSymbols row) : row[symbol]?.getD 0 ≠ 0 := by
  simpa [nonzeroSymbols] using (List.mem_filter.mp hmem).2

/-- A fixed-left guarded route equals its compact unchecked representation.

Proof sketch: map congruence reduces the statement to one right symbol.  Membership in the sparse
right support discharges its guard, while `hleft` discharges the common left guard.
-/
theorem routedContributionsForLeftFromSupports_eq_unchecked
    (data : BetaFourLocalSlotData) (parentSupport leftSupport rightSupport : List ℕ)
    (leftSymbol : ℕ) (hleft : data.leftNumerators[leftSymbol]?.getD 0 ≠ 0) :
    data.routedContributionsForLeftFromSupports
        parentSupport leftSupport rightSupport leftSymbol =
      data.routedContributionsForLeftUncheckedFromSupports
        parentSupport leftSupport rightSupport leftSymbol := by
  unfold routedContributionsForLeftFromSupports
    routedContributionsForLeftUncheckedFromSupports
  apply List.map_congr_left
  intro rightSymbol hmem
  exact data.routedContributionFromSupports_eq_some_unchecked
    parentSupport leftSupport rightSupport leftSymbol rightSymbol hleft
      (getD_ne_zero_of_mem_nonzeroSymbols data.rightNumerators rightSymbol hmem)

/-- Route the right-symbol row belonging to one fixed nonzero left symbol.

This is the bounded checking unit used by generated certificates.  A beta-three row has at most
nineteen symbols, so a theorem about this list never asks the kernel to normalize more than
nineteen routed contributions at once.
-/
def routedContributionsForLeft (data : BetaFourLocalSlotData) (parent coordinate : ℕ)
    (leftSymbol : ℕ) : List (Option BetaFourRoutedContribution) :=
  let parentSupport := routedParentSupport parent coordinate
  let leftSupport := data.routedLeftSupport parent coordinate
  let rightSupport := data.routedRightSupport parent coordinate
  data.routedContributionsForLeftFromSupports parentSupport leftSupport rightSupport leftSymbol

/-- Route every sparse child-symbol pair belonging to one top-slot record. -/
def routedContributions (data : BetaFourLocalSlotData) (parent coordinate : ℕ) :
    List (Option BetaFourRoutedContribution) :=
  let parentSupport := routedParentSupport parent coordinate
  let leftSupport := data.routedLeftSupport parent coordinate
  let rightSupport := data.routedRightSupport parent coordinate
  if data.splitNumerator = 0 then []
  else
    (nonzeroSymbols data.leftNumerators).flatMap fun leftSymbol ↦
      (nonzeroSymbols data.rightNumerators).map fun rightSymbol ↦
        data.routedContributionFromSupports parentSupport leftSupport rightSupport
          leftSymbol rightSymbol

/-- A nonzero slot route is the concatenation of its bounded fixed-left rows.

Proof sketch: unfold both definitions.  The three support lists on the left are shared outside the
`flatMap`; after zeta reduction they are definitionally the same lists used by each fixed-left row.
-/
theorem routedContributions_eq_flatMap_forLeft_of_ne (data : BetaFourLocalSlotData)
    (parent coordinate : ℕ) (hsplit : data.splitNumerator ≠ 0) :
    data.routedContributions parent coordinate =
      (nonzeroSymbols data.leftNumerators).flatMap
        (data.routedContributionsForLeft parent coordinate) := by
  unfold routedContributions
  simp only [hsplit, ↓reduceIte]
  apply List.flatMap_congr
  intro leftSymbol hleft
  rfl

/-- Replace the three computed supports by extensionally equal checked support tables.

This is the semantic composition rule for compact generated certificates: support enumeration is
checked once, while every fixed-left routing row is checked independently against those inert
tables.
-/
theorem routedContributions_eq_flatMap_forLeftFromSupports_of_ne
    (data : BetaFourLocalSlotData) (parent coordinate : ℕ)
    (parentSupport leftSupport rightSupport : List ℕ)
    (hparent : routedParentSupport parent coordinate = parentSupport)
    (hleft : data.routedLeftSupport parent coordinate = leftSupport)
    (hright : data.routedRightSupport parent coordinate = rightSupport)
    (hsplit : data.splitNumerator ≠ 0) :
    data.routedContributions parent coordinate =
      (nonzeroSymbols data.leftNumerators).flatMap
        (data.routedContributionsForLeftFromSupports
          parentSupport leftSupport rightSupport) := by
  unfold routedContributions
  rw [hparent, hleft, hright]
  simp only [hsplit, ↓reduceIte]
  rfl

/-- A zero-weight slot contributes no routed entries. -/
theorem routedContributions_eq_nil_of_split_eq_zero (data : BetaFourLocalSlotData)
    (parent coordinate : ℕ) (hsplit : data.splitNumerator = 0) :
    data.routedContributions parent coordinate = [] := by
  simp [routedContributions, hsplit]

private theorem addOptionalAt_routedContributionFromSupports (data : BetaFourLocalSlotData)
    (parent coordinate position accumulator leftSymbol rightSymbol : ℕ) :
    BetaFourRoutedContribution.addOptionalAt position accumulator
        (data.routedContributionFromSupports
          (routedParentSupport parent coordinate)
          (data.routedLeftSupport parent coordinate)
          (data.routedRightSupport parent coordinate)
          leftSymbol rightSymbol) =
      data.addContributionAt parent coordinate position accumulator leftSymbol rightSymbol := by
  by_cases hleft : data.leftNumerators[leftSymbol]?.getD 0 = 0
  · simp [routedContributionFromSupports, BetaFourRoutedContribution.addOptionalAt,
      addContributionAt, hleft]
  · by_cases hright : data.rightNumerators[rightSymbol]?.getD 0 = 0
    · simp [routedContributionFromSupports, BetaFourRoutedContribution.addOptionalAt,
        addContributionAt, hleft, hright]
    · simp [routedContributionFromSupports, BetaFourRoutedContribution.addOptionalAt,
        addContributionAt, concatenatedParentSlotForPair, routedParentSupport,
        routedLeftSupport, routedRightSupport, hleft, hright]
      rfl

private theorem foldl_mapped_routedContributions (data : BetaFourLocalSlotData)
    (parent coordinate position leftSymbol : ℕ) (rightSymbols : List ℕ)
    (initial : ℕ) :
    ((rightSymbols.map fun rightSymbol ↦
        data.routedContributionFromSupports
          (routedParentSupport parent coordinate)
          (data.routedLeftSupport parent coordinate)
          (data.routedRightSupport parent coordinate)
          leftSymbol rightSymbol).foldl
          (BetaFourRoutedContribution.addOptionalAt position) initial) =
      rightSymbols.foldl (fun accumulator rightSymbol ↦
        data.addContributionAt parent coordinate position accumulator
          leftSymbol rightSymbol) initial := by
  induction rightSymbols generalizing initial with
  | nil => rfl
  | cons rightSymbol rightSymbols ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [data.addOptionalAt_routedContributionFromSupports
        parent coordinate position initial
        leftSymbol rightSymbol]
      exact ih _

private theorem foldl_flatMapped_routedContributions (data : BetaFourLocalSlotData)
    (parent coordinate position : ℕ) (leftSymbols rightSymbols : List ℕ)
    (initial : ℕ) :
    ((leftSymbols.flatMap fun leftSymbol ↦
        rightSymbols.map fun rightSymbol ↦
          data.routedContributionFromSupports
            (routedParentSupport parent coordinate)
            (data.routedLeftSupport parent coordinate)
            (data.routedRightSupport parent coordinate)
            leftSymbol rightSymbol).foldl
            (BetaFourRoutedContribution.addOptionalAt position) initial) =
      leftSymbols.foldl (fun accumulator leftSymbol ↦
        rightSymbols.foldl (fun accumulator rightSymbol ↦
          data.addContributionAt parent coordinate position accumulator
            leftSymbol rightSymbol) accumulator) initial := by
  induction leftSymbols generalizing initial with
  | nil => rfl
  | cons leftSymbol leftSymbols ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      rw [data.foldl_mapped_routedContributions parent coordinate position leftSymbol
        rightSymbols initial]
      exact ih _

/-- Folding the routed list at one position is exactly the original sparse scalar slot fold.

Proof sketch: expand the outer `flatMap` into the left-symbol fold and each inner `map` into the
right-symbol fold.  Applying `routedContribution` has the same zero guards, target, and numerator
as `addContributionAt`, so every scalar step agrees.
-/
theorem foldl_routedContributions_eq_addToNumeratorAt (data : BetaFourLocalSlotData)
    (parent coordinate position accumulator : ℕ) :
    (data.routedContributions parent coordinate).foldl
        (BetaFourRoutedContribution.addOptionalAt position) accumulator =
      data.addToNumeratorAt parent coordinate position accumulator := by
  unfold routedContributions addToNumeratorAt
  by_cases hsplit : data.splitNumerator = 0
  · simp [hsplit]
  · simp only [hsplit, ↓reduceIte]
    exact data.foldl_flatMapped_routedContributions parent coordinate position
      (nonzeroSymbols data.leftNumerators) (nonzeroSymbols data.rightNumerators) accumulator

end BetaFourLocalSlotData

namespace BetaFourLocalData

/-- Route all sparse source contributions of a parent-local certificate exactly once. -/
def routedContributions (data : BetaFourLocalData) (parent coordinate : ℕ) :
    List (Option BetaFourRoutedContribution) :=
  data.slots.flatMap fun slotData ↦ slotData.routedContributions parent coordinate

private theorem foldl_flatMapped_slotContributions (parent coordinate position : ℕ)
    (slots : List BetaFourLocalSlotData) (initial : ℕ) :
    ((slots.flatMap fun slotData ↦ slotData.routedContributions parent coordinate).foldl
        (BetaFourRoutedContribution.addOptionalAt position) initial) =
      slots.foldl (fun accumulator slotData ↦
        slotData.addToNumeratorAt parent coordinate position accumulator) initial := by
  induction slots generalizing initial with
  | nil => rfl
  | cons slotData slots ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      rw [slotData.foldl_routedContributions_eq_addToNumeratorAt
        parent coordinate position initial]
      exact ih _

/-- The routed contribution list computes the same scalar numerator as the source slot fold. -/
theorem routedNumeratorAt_eq (data : BetaFourLocalData)
    (parent coordinate position : ℕ) :
    BetaFourRoutedContribution.numeratorAt
        (data.routedContributions parent coordinate) position =
      data.numeratorAt parent coordinate position := by
  unfold BetaFourRoutedContribution.numeratorAt routedContributions numeratorAt addToNumeratorAt
  exact foldl_flatMapped_slotContributions parent coordinate position data.slots 0

/-- Evaluating routed contributions agrees with the source pointwise evaluator on any positions.

Proof sketch: map `routedNumeratorAt_eq` over the requested position list.  This theorem is the
certificate boundary used by generated clients: routing may be checked once, independently of
the number and partitioning of later arithmetic shards.
-/
theorem routedScatterOn_eq_scatterOn (data : BetaFourLocalData)
    (parent coordinate : ℕ) (positions : List ℕ) :
    BetaFourRoutedContribution.scatterOn (data.routedContributions parent coordinate) positions =
      data.scatterOn parent coordinate positions := by
  unfold BetaFourRoutedContribution.scatterOn scatterOn
  apply List.map_congr_left
  intro position hposition
  exact data.routedNumeratorAt_eq parent coordinate position

/-- A full routed pointwise evaluation recovers the dense semantic scatter. -/
theorem routedScatterOn_range_eq_scatter (data : BetaFourLocalData)
    (parent coordinate : ℕ) :
    BetaFourRoutedContribution.scatterOn (data.routedContributions parent coordinate)
        (List.range parentSupportWidth) =
      data.scatter parent coordinate := by
  rw [data.routedScatterOn_eq_scatterOn parent coordinate]
  exact data.scatterOn_range_eq_scatter parent coordinate

end BetaFourLocalData

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
