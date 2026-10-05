/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourLocalPointwise
import MatrixMultiplication.TernarySplitWordEncoding

/-!
# Gather agreement for beta-four local slots

This module proves that the inverse-code gather for one parent-local beta-four slot agrees with
its pointwise sparse scatter contribution.  It depends only on the lightweight local evaluator and
ternary support-code interface; global recurrence caches and recursive tensor semantics remain in
the downstream semantic-agreement module.

The declarations intentionally live in `MatrixMultiplication.BetaFourSemanticAgreement`: this
file is the lightweight first half of that API, while `BetaFourSemanticAgreement.lean` adds the
global-cache and recursive-tensor bridge.
-/

namespace MatrixMultiplication.BetaFourSemanticAgreement

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

namespace BetaFourLocalSlotData

private theorem foldl_eq_self_of_mem_identity {α : Type*}
    (values : List α) (step : ℕ → α → ℕ)
    (hstep : ∀ accumulator value, value ∈ values → step accumulator value = accumulator)
    (initial : ℕ) : values.foldl step initial = initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      rw [List.foldl_cons, hstep initial value (by simp)]
      apply ih
      intro accumulator other hother
      exact hstep accumulator other (by simp [hother])

private theorem foldl_add_once {α : Type*} [DecidableEq α]
    (values : List α) (step : ℕ → α → ℕ) (target : α) (amount initial : ℕ)
    (hnodup : values.Nodup) (htarget : target ∈ values)
    (hother : ∀ accumulator value, value ∈ values →
      value ≠ target → step accumulator value = accumulator)
    (hat : ∀ accumulator, step accumulator target = accumulator + amount) :
    values.foldl step initial = initial + amount := by
  induction values generalizing initial with
  | nil => simp at htarget
  | cons value values ih =>
      have hnodupTail := hnodup.tail
      by_cases hvalue : value = target
      · subst value
        rw [List.foldl_cons, hat]
        apply foldl_eq_self_of_mem_identity
        intro accumulator other hotherMem
        exact hother accumulator other (by simp [hotherMem]) fun heq ↦
          hnodup.notMem (heq ▸ hotherMem)
      · rw [List.foldl_cons, hother initial value (by simp) hvalue]
        have htargetTail : target ∈ values := by
          simp only [List.mem_cons] at htarget
          rcases htarget with hhead | htail
          · exact (hvalue hhead.symm).elim
          · exact htail
        apply ih initial hnodupTail htargetTail
        · intro accumulator other hotherMem hotherNe
          exact hother accumulator other (by simp [hotherMem]) hotherNe

private theorem nonzeroSymbols_nodup (row : Array ℕ) :
    (BetaFourLocalSlotData.nonzeroSymbols row).Nodup :=
  List.nodup_range.filter _

private theorem getD_ne_zero_of_mem_nonzeroSymbols (row : Array ℕ) (symbol : ℕ)
    (hmem : symbol ∈ BetaFourLocalSlotData.nonzeroSymbols row) :
    row[symbol]?.getD 0 ≠ 0 := by
  simpa [BetaFourLocalSlotData.nonzeroSymbols] using (List.mem_filter.mp hmem).2

/-- Child-support position selected by the left half of one parent-support symbol. -/
def selectedLeftSymbol (data : BetaFourLocalSlotData)
    (parent coordinate symbol : ℕ) : ℕ :=
  let pair := MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot
  let parentTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
    (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate
  let parentCode := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
    MatrixMultiplication.BetaFourLocalGeometry.parentWordLength parentTotal symbol
  (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength
    (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate pair.1 coordinate)).idxOf
      (parentCode / 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength)

/-- Child-support position selected by the right half of one parent-support symbol. -/
def selectedRightSymbol (data : BetaFourLocalSlotData)
    (parent coordinate symbol : ℕ) : ℕ :=
  let pair := MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot
  let parentTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
    (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate
  let parentCode := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
    MatrixMultiplication.BetaFourLocalGeometry.parentWordLength parentTotal symbol
  (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength
    (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate pair.2 coordinate)).idxOf
      (parentCode % 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength)

/-- The inverse-code gather reads exactly the two selected child positions. -/
theorem gatherNumerator_eq_selected (data : BetaFourLocalSlotData)
    (parent coordinate symbol : ℕ) :
    data.gatherNumerator parent coordinate symbol =
      data.splitNumerator *
        data.leftNumerators[selectedLeftSymbol data parent coordinate symbol]?.getD 0 *
          data.rightNumerators[selectedRightSymbol data parent coordinate symbol]?.getD 0 := by
  rfl

/-- A nonzero padded child entry lies inside its true support. -/
private theorem symbol_lt_leftSupport_of_ne (data : BetaFourLocalSlotData)
    (parent coordinate symbol : ℕ) (hpadding : data.IsSupportZero parent coordinate)
    (hne : data.leftNumerators[symbol]?.getD 0 ≠ 0) :
    symbol < (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
      MatrixMultiplication.BetaFourLocalGeometry.childWordLength
      (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
        (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate)).length :=
  lt_of_not_ge fun hge ↦ hne (hpadding.1 symbol hge)

/-- A nonzero padded right-child entry lies inside its true support. -/
private theorem symbol_lt_rightSupport_of_ne (data : BetaFourLocalSlotData)
    (parent coordinate symbol : ℕ) (hpadding : data.IsSupportZero parent coordinate)
    (hne : data.rightNumerators[symbol]?.getD 0 ≠ 0) :
    symbol < (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
      MatrixMultiplication.BetaFourLocalGeometry.childWordLength
      (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
        (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate)).length :=
  lt_of_not_ge fun hge ↦ hne (hpadding.2 symbol hge)

/-- For nonzero child entries, routing to a genuine parent symbol determines both source symbols.

Proof sketch: zero padding puts both source indices inside their child support lists.  Their two
codes therefore concatenate to a member of the parent support.  Equality of parent support
indices gives equality of codes; quotient and remainder by `3^4` recover the two uniquely selected
child codes. -/
theorem symbols_eq_selected_of_route_eq (data : BetaFourLocalSlotData)
    (parent coordinate position leftSymbol rightSymbol : ℕ)
    (hpadding : data.IsSupportZero parent coordinate)
    (hcoordinateSum :
      MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate +
        MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate)
    (hposition : position <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.parentWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate)).length)
    (hleft : data.leftNumerators[leftSymbol]?.getD 0 ≠ 0)
    (hright : data.rightNumerators[rightSymbol]?.getD 0 ≠ 0)
    (hroute : MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
      parent coordinate (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot)
        leftSymbol rightSymbol = position) :
    leftSymbol = selectedLeftSymbol data parent coordinate position ∧
      rightSymbol = selectedRightSymbol data parent coordinate position := by
  let pair := MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot
  let leftTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate pair.1 coordinate
  let rightTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate pair.2 coordinate
  let parentTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
    (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate
  let leftSupport := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength leftTotal
  let rightSupport := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength rightTotal
  let parentSupport := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.parentWordLength parentTotal
  let leftCode := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength leftTotal leftSymbol
  let rightCode := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength rightTotal rightSymbol
  let parentCode := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
    MatrixMultiplication.BetaFourLocalGeometry.parentWordLength parentTotal position
  change leftTotal + rightTotal = parentTotal at hcoordinateSum
  change parentSupport.idxOf
    (leftCode * 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength + rightCode) =
      position at hroute
  have hleftPosition : leftSymbol < leftSupport.length :=
    symbol_lt_leftSupport_of_ne data parent coordinate leftSymbol hpadding hleft
  have hrightPosition : rightSymbol < rightSupport.length :=
    symbol_lt_rightSupport_of_ne data parent coordinate rightSymbol hpadding hright
  have hleftCode : leftCode ∈ leftSupport :=
    TernarySplitWordEncoding.ternarySupportCodeAt_mem hleftPosition
  have hrightCode : rightCode ∈ rightSupport :=
    TernarySplitWordEncoding.ternarySupportCodeAt_mem hrightPosition
  have hconcat :
      leftCode * 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength + rightCode ∈
        parentSupport := by
    have := TernarySplitWordEncoding.concat_mem_parent_support hleftCode hrightCode
    simpa only [parentSupport, hcoordinateSum] using this
  have hparentIndex : parentSupport.idxOf parentCode = position :=
    TernarySplitWordEncoding.ternarySupport_idxOf_codeAt hposition
  have hindex :
      parentSupport.idxOf
          (leftCode * 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength + rightCode) =
        parentSupport.idxOf parentCode := by
    exact hroute.trans hparentIndex.symm
  have hcode :
      leftCode * 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength + rightCode =
        parentCode :=
    TernarySplitWordEncoding.support_idxOf_inj hconcat hindex
  have hrightCodeBound :
      rightCode < 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength := by
    simpa [rightSupport, MatrixMultiplication.BetaFourLocalGeometry.childWordLength] using
      (List.mem_range.mp (List.mem_filter.mp hrightCode).1)
  have hleftHalf :
      leftCode = parentCode / 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength := by
    have := congrArg
      (fun value ↦ value / 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength) hcode
    simpa [TernarySplitWordEncoding.concat_div_depthTwo leftCode rightCode hrightCodeBound] using this
  have hrightHalf :
      rightCode = parentCode % 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength := by
    have := congrArg
      (fun value ↦ value % 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength) hcode
    simpa [TernarySplitWordEncoding.concat_mod_depthTwo leftCode rightCode hrightCodeBound] using this
  constructor
  · calc
      leftSymbol = leftSupport.idxOf leftCode :=
        (TernarySplitWordEncoding.ternarySupport_idxOf_codeAt hleftPosition).symm
      _ = leftSupport.idxOf
          (parentCode / 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength) := by
        rw [← hleftHalf]
      _ = selectedLeftSymbol data parent coordinate position := by
        rfl
  · calc
      rightSymbol = rightSupport.idxOf rightCode :=
        (TernarySplitWordEncoding.ternarySupport_idxOf_codeAt hrightPosition).symm
      _ = rightSupport.idxOf
          (parentCode % 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength) := by
        rw [← hrightHalf]
      _ = selectedRightSymbol data parent coordinate position := by
        rfl

/-- If both inverse-selected child entries are nonzero, they route back to the requested parent
position.

Proof sketch: zero padding puts the selected indices inside the true child supports.  Reading
those support entries yields the quotient and remainder of the requested parent code; Euclidean
division recomposes that code, and `idxOf` then recovers the original parent position. -/
theorem selected_route_eq (data : BetaFourLocalSlotData)
    (parent coordinate position : ℕ)
    (hpadding : data.IsSupportZero parent coordinate)
    (hposition : position <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.parentWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate)).length)
    (hleft :
      data.leftNumerators[selectedLeftSymbol data parent coordinate position]?.getD 0 ≠ 0)
    (hright :
      data.rightNumerators[selectedRightSymbol data parent coordinate position]?.getD 0 ≠ 0) :
    MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
      parent coordinate (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot)
        (selectedLeftSymbol data parent coordinate position)
        (selectedRightSymbol data parent coordinate position) = position := by
  let pair := MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot
  let parentTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
    (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate
  let parentSupport := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.parentWordLength parentTotal
  let parentCode := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
    MatrixMultiplication.BetaFourLocalGeometry.parentWordLength parentTotal position
  let leftTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate pair.1 coordinate
  let rightTotal := MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate pair.2 coordinate
  let leftSupport := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength leftTotal
  let rightSupport := MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
    MatrixMultiplication.BetaFourLocalGeometry.childWordLength rightTotal
  let leftSymbol := selectedLeftSymbol data parent coordinate position
  let rightSymbol := selectedRightSymbol data parent coordinate position
  have hleftPosition : leftSymbol < leftSupport.length :=
    symbol_lt_leftSupport_of_ne data parent coordinate leftSymbol hpadding hleft
  have hrightPosition : rightSymbol < rightSupport.length :=
    symbol_lt_rightSupport_of_ne data parent coordinate rightSymbol hpadding hright
  have hleftCode :
      MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
          MatrixMultiplication.BetaFourLocalGeometry.childWordLength leftTotal leftSymbol =
        parentCode / 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength := by
    apply TernarySplitWordEncoding.ternarySupportCodeAt_idxOf
    exact List.idxOf_lt_length_iff.mp hleftPosition
  have hrightCode :
      MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
          MatrixMultiplication.BetaFourLocalGeometry.childWordLength rightTotal rightSymbol =
        parentCode % 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength := by
    apply TernarySplitWordEncoding.ternarySupportCodeAt_idxOf
    exact List.idxOf_lt_length_iff.mp hrightPosition
  have hrecompose :
      parentCode / 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength *
          3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength +
        parentCode % 3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength = parentCode :=
    Nat.div_add_mod' parentCode _
  change parentSupport.idxOf
    (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
          MatrixMultiplication.BetaFourLocalGeometry.childWordLength leftTotal leftSymbol *
        3 ^ MatrixMultiplication.BetaFourLocalGeometry.childWordLength +
      MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodeAt
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength rightTotal rightSymbol) = position
  rw [hleftCode, hrightCode, hrecompose]
  exact TernarySplitWordEncoding.ternarySupport_idxOf_codeAt hposition

/-- One local slot's pointwise scatter is its inverse-code gather contribution.

The two width hypotheses state that the genuine child supports fit the common nineteen-cell
evaluator padding.  They are structural consequences of a valid total-eight child pair.

Proof sketch: if the split or either selected numerator is zero, routing uniqueness makes every
source fold step the identity.  Otherwise the selected symbols occur exactly once in the two
noduplicated sparse symbol lists; routing uniqueness makes every other step the identity, and the
selected pair contributes the gathered product once. -/
theorem addToNumeratorAt_eq_add_gatherNumerator (data : BetaFourLocalSlotData)
    (parent coordinate position accumulator : ℕ)
    (hpadding : data.IsSupportZero parent coordinate)
    (hcoordinateSum :
      MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate +
        MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate)
    (hleftWidth :
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate)).length ≤
        MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth)
    (hrightWidth :
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate)).length ≤
        MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth)
    (hposition : position <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.parentWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.parentShapeAt parent) coordinate)).length) :
    data.addToNumeratorAt parent coordinate position accumulator =
      accumulator + data.gatherNumerator parent coordinate position := by
  let leftSelected := selectedLeftSymbol data parent coordinate position
  let rightSelected := selectedRightSymbol data parent coordinate position
  let leftValue := data.leftNumerators[leftSelected]?.getD 0
  let rightValue := data.rightNumerators[rightSelected]?.getD 0
  by_cases hsplit : data.splitNumerator = 0
  · simp [BetaFourLocalSlotData.addToNumeratorAt,
      gatherNumerator_eq_selected, hsplit]
  by_cases hleftSelected : leftValue = 0
  · have hfold : data.addToNumeratorAt parent coordinate position accumulator = accumulator := by
      unfold BetaFourLocalSlotData.addToNumeratorAt
      simp only [hsplit, ↓reduceIte]
      apply foldl_eq_self_of_mem_identity
      intro outer leftSymbol hleftMem
      apply foldl_eq_self_of_mem_identity
      intro inner rightSymbol hrightMem
      have hleftNe := getD_ne_zero_of_mem_nonzeroSymbols
        data.leftNumerators leftSymbol hleftMem
      have hrightNe := getD_ne_zero_of_mem_nonzeroSymbols
        data.rightNumerators rightSymbol hrightMem
      have hroute :
          MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
              parent coordinate
              (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot)
              leftSymbol rightSymbol ≠ position := by
        intro heq
        have hselected := symbols_eq_selected_of_route_eq data parent coordinate position
          leftSymbol rightSymbol hpadding hcoordinateSum hposition hleftNe hrightNe heq
        apply hleftNe
        simpa [leftValue, leftSelected, hselected.1] using hleftSelected
      simp [BetaFourLocalSlotData.addContributionAt, hleftNe, hrightNe, hroute]
    have hleftZero :
        data.leftNumerators[selectedLeftSymbol data parent coordinate position]?.getD 0 = 0 := by
      simpa [leftValue, leftSelected] using hleftSelected
    rw [hfold]
    rw [gatherNumerator_eq_selected]
    simp [hleftZero]
  by_cases hrightSelected : rightValue = 0
  · have hfold : data.addToNumeratorAt parent coordinate position accumulator = accumulator := by
      unfold BetaFourLocalSlotData.addToNumeratorAt
      simp only [hsplit, ↓reduceIte]
      apply foldl_eq_self_of_mem_identity
      intro outer leftSymbol hleftMem
      apply foldl_eq_self_of_mem_identity
      intro inner rightSymbol hrightMem
      have hleftNe := getD_ne_zero_of_mem_nonzeroSymbols
        data.leftNumerators leftSymbol hleftMem
      have hrightNe := getD_ne_zero_of_mem_nonzeroSymbols
        data.rightNumerators rightSymbol hrightMem
      have hroute :
          MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
              parent coordinate
              (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot)
              leftSymbol rightSymbol ≠ position := by
        intro heq
        have hselected := symbols_eq_selected_of_route_eq data parent coordinate position
          leftSymbol rightSymbol hpadding hcoordinateSum hposition hleftNe hrightNe heq
        apply hrightNe
        simpa [rightValue, rightSelected, hselected.2] using hrightSelected
      simp [BetaFourLocalSlotData.addContributionAt, hleftNe, hrightNe, hroute]
    have hrightZero :
        data.rightNumerators[selectedRightSymbol data parent coordinate position]?.getD 0 = 0 := by
      simpa [rightValue, rightSelected] using hrightSelected
    rw [hfold]
    rw [gatherNumerator_eq_selected]
    simp [hrightZero]
  have hleftSupport : leftSelected <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate)).length :=
    symbol_lt_leftSupport_of_ne data parent coordinate leftSelected hpadding hleftSelected
  have hrightSupport : rightSelected <
      (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
        MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
          (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate)).length :=
    symbol_lt_rightSupport_of_ne data parent coordinate rightSelected hpadding hrightSelected
  have hleftMem : leftSelected ∈ BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators := by
    simp only [BetaFourLocalSlotData.nonzeroSymbols, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨lt_of_lt_of_le hleftSupport hleftWidth, hleftSelected⟩
  have hrightMem : rightSelected ∈ BetaFourLocalSlotData.nonzeroSymbols data.rightNumerators := by
    simp only [BetaFourLocalSlotData.nonzeroSymbols, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨lt_of_lt_of_le hrightSupport hrightWidth, hrightSelected⟩
  have hselectedRoute := selected_route_eq data parent coordinate position hpadding hposition
    hleftSelected hrightSelected
  unfold BetaFourLocalSlotData.addToNumeratorAt
  simp only [hsplit, ↓reduceIte]
  rw [foldl_add_once
    (BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators)
    (fun outer leftSymbol ↦
      (BetaFourLocalSlotData.nonzeroSymbols data.rightNumerators).foldl
        (fun inner rightSymbol ↦
          data.addContributionAt parent coordinate position inner leftSymbol rightSymbol) outer)
    leftSelected (data.splitNumerator * leftValue * rightValue) accumulator
    (nonzeroSymbols_nodup data.leftNumerators) hleftMem]
  · simp [gatherNumerator_eq_selected, leftValue, rightValue,
      leftSelected, rightSelected]
  · intro outer leftSymbol hleftMem' hleftOther
    apply foldl_eq_self_of_mem_identity
    intro inner rightSymbol hrightMem'
    have hleftNe := getD_ne_zero_of_mem_nonzeroSymbols
      data.leftNumerators leftSymbol hleftMem'
    have hrightNe := getD_ne_zero_of_mem_nonzeroSymbols
      data.rightNumerators rightSymbol hrightMem'
    have hroute :
        MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
            parent coordinate
            (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot)
            leftSymbol rightSymbol ≠ position := by
      intro heq
      have hselected := symbols_eq_selected_of_route_eq data parent coordinate position
        leftSymbol rightSymbol hpadding hcoordinateSum hposition hleftNe hrightNe heq
      exact hleftOther hselected.1
    simp [BetaFourLocalSlotData.addContributionAt, hleftNe, hrightNe, hroute]
  · intro outer
    rw [foldl_add_once
      (BetaFourLocalSlotData.nonzeroSymbols data.rightNumerators)
      (fun inner rightSymbol ↦
        data.addContributionAt parent coordinate position inner leftSelected rightSymbol)
      rightSelected (data.splitNumerator * leftValue * rightValue) outer
      (nonzeroSymbols_nodup data.rightNumerators) hrightMem]
    · intro inner rightSymbol hrightMem' hrightOther
      have hrightNe := getD_ne_zero_of_mem_nonzeroSymbols
        data.rightNumerators rightSymbol hrightMem'
      have hroute :
          MatrixMultiplication.BetaFourLocalGeometry.concatenatedParentSlotForPair
              parent coordinate
              (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot)
              leftSelected rightSymbol ≠ position := by
        intro heq
        have hselected := symbols_eq_selected_of_route_eq data parent coordinate position
          leftSelected rightSymbol hpadding hcoordinateSum hposition hleftSelected hrightNe heq
        exact hrightOther hselected.2
      simp [BetaFourLocalSlotData.addContributionAt, hrightNe, hroute]
    · intro inner
      simp [BetaFourLocalSlotData.addContributionAt, hleftSelected, hrightSelected,
        hselectedRoute, leftValue, rightValue, leftSelected, rightSelected]

end BetaFourLocalSlotData

end MatrixMultiplication.BetaFourSemanticAgreement
