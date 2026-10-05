/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence

/-!
# Exact complete-split recurrence for the total-weight quotient

The unconditional certificate hashes each length-two CW complete-split word only by its total
digit weight.  Inside a fixed child shape that total is already known, so the quotient alphabet
has one genuine slot.  This module gives the exact natural-number pushforward used by the
certificate evaluator and ties it to `cwSplitWordTotalDigit`, the tensor-level quotient map.

The three-slot padding is retained solely so the existing product recurrences keep a uniform
array shape.  Padded fine slots have zero mass by `betaTwoNumerator`'s support guard.
-/

namespace MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Slot action induced by `cwSplitWordTotalDigit`.  A genuine source word is sent to the unique
slot zero in its fixed-total quotient fiber.  The out-of-range value three is used only for a
padded source symbol whose fine numerator is already zero. -/
def totalWeightSupportSlot (total symbol : ℕ) : ℕ :=
  let source := splitPairOfTernaryCode
    (ternarySupportCodeAt levelTwoWordLength total symbol)
  if (cwSplitWordTotalDigit 1 source).val = total then 0 else levelTwoSupportWidth

/-- On every genuine length-two support symbol, the tensor quotient records exactly the fixed
shape total. -/
theorem cwSplitWordTotalDigit_source_val
    (total symbol : ℕ)
    (htotal : total ≤ 2 * levelTwoWordLength)
    (hsymbol : symbol < (ternarySupportCodes levelTwoWordLength total).length) :
    (cwSplitWordTotalDigit 1
      (splitPairOfTernaryCode
        (ternarySupportCodeAt levelTwoWordLength total symbol))).val = total := by
  norm_num [levelTwoWordLength] at htotal
  interval_cases total <;>
    simp only [levelTwoWordLength, ternarySupportCodes_levelTwo_zero,
      ternarySupportCodes_levelTwo_one, ternarySupportCodes_levelTwo_two,
      ternarySupportCodes_levelTwo_three, ternarySupportCodes_levelTwo_four,
      List.length_cons, List.length_nil] at hsymbol ⊢ <;>
    interval_cases symbol <;>
    decide

/-- Statement-to-program bridge: the executable quotient slot is zero on all structural
support.  This theorem prevents the numeric specification and `cwSplitWordTotalDigit` from
drifting apart. -/
theorem totalWeightSupportSlot_eq_zero
    (total symbol : ℕ)
    (htotal : total ≤ 2 * levelTwoWordLength)
    (hsymbol : symbol < (ternarySupportCodes levelTwoWordLength total).length) :
    totalWeightSupportSlot total symbol = 0 := by
  simp only [totalWeightSupportSlot]
  rw [if_pos (cwSplitWordTotalDigit_source_val total symbol htotal hsymbol)]

theorem totalWeightSupportSlots_totalOne :
    (List.range 2).map (totalWeightSupportSlot 1) = [0, 0] := by decide

theorem totalWeightSupportSlots_totalTwo :
    (List.range 3).map (totalWeightSupportSlot 2) = [0, 0, 0] := by decide

theorem totalWeightSupportSlots_totalThree :
    (List.range 2).map (totalWeightSupportSlot 3) = [0, 0] := by decide

/-- Exact pushforward of a fine depth-two law through the total-weight quotient. -/
def totalWeightBetaTwoNumerator (data : PrimaryTables)
    (node region slot coordinate targetSymbol : ℕ) : ℕ :=
  ((List.range levelTwoSupportWidth).map fun sourceSymbol ↦
    if totalWeightSupportSlot
        (shapeCoordinate (splitShapeAt node slot) coordinate) sourceSymbol = targetSymbol then
      betaTwoNumerator data node region slot coordinate sourceSymbol
    else 0).sum

/-- One contribution to a positive depth-four parent law after total-weight quotienting both
length-two children. -/
def betaThreeContribution (data : PrimaryTables)
    (node region coordinate parentSymbol slot leftSymbol rightSymbol : ℕ) : ℕ :=
  if splitSlotIsValid node slot then
    let leftShape := splitShapeAt node slot
    let rightSlot := complementSlotAt node slot
    let rightShape := splitShapeAt node rightSlot
    let leftCode := ternarySupportCodeAt levelTwoWordLength
      (shapeCoordinate leftShape coordinate) leftSymbol
    let rightCode := ternarySupportCodeAt levelTwoWordLength
      (shapeCoordinate rightShape coordinate) rightSymbol
    let parentCode := ternarySupportCodeAt levelThreeWordLength
      (shapeCoordinate (nodeShapeAt node) coordinate) parentSymbol
    if leftCode * 3 ^ levelTwoWordLength + rightCode = parentCode then
      dyadicNumeratorAt data.pos3Alpha (node * 6 + region) slot *
        totalWeightBetaTwoNumerator data node region slot coordinate leftSymbol *
        totalWeightBetaTwoNumerator data node region rightSlot coordinate rightSymbol
    else 0
  else 0

/-- Exact positive level-three parent numerator at denominator `2^36`. -/
def betaThreeRegionNumerator (data : PrimaryTables)
    (node region coordinate parentSymbol : ℕ) : ℕ :=
  ((List.range 10).flatMap fun slot ↦
      (List.range levelTwoSupportWidth).flatMap fun leftSymbol ↦
        (List.range levelTwoSupportWidth).map fun rightSymbol ↦
          betaThreeContribution data node region coordinate parentSymbol
            slot leftSymbol rightSymbol).sum

/-- Serialized total-quotient depth-four parent row, padded to width nineteen. -/
def betaThreeRegionRow (data : PrimaryTables) (node region coordinate : ℕ) : List ℕ :=
  (List.range levelThreeSupportWidth).map
    (betaThreeRegionNumerator data node region coordinate)

end MatrixMultiplication.TotalQuotientCompleteSplitRecurrence
