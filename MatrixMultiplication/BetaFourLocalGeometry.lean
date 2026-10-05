/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry

/-!
# Lightweight geometry for parent-local beta-four checks

This definition-only module contains exactly the finite geometry needed to check one level-four
parent convolution: ternary support words, ordered child-pair slots, and the parent scatter index.
It deliberately does not import the global recurrence, entropy, generated tables, or real
analysis.  The semantic adapter in `BetaFourLocalCertificate.lean` proves that these executable
definitions agree with the established global recurrence.

The definitions mirror the corresponding historical recurrence definitions but use their own
namespace.  Keeping this boundary independent lets hundreds of generated arithmetic shards load a
small environment; only the adapter modules pay for the global semantic import closure.
-/

namespace MatrixMultiplication.BetaFourLocalGeometry

open AlgebraicComplexity.LevelFourReconstruction

/-- Number of incoming regional copies in the repeated-orientation construction. -/
def regionCount : ℕ := 6

/-- Length of each beta-three ternary word. -/
def childWordLength : ℕ := 4

/-- Common padded width of a beta-three coordinate row. -/
def childSupportWidth : ℕ := 19

/-- Length of a beta-four parent ternary word. -/
def parentWordLength : ℕ := 8

/-- Common padded width of a beta-four parent coordinate row. -/
def parentSupportWidth : ℕ := 1107

/-- Maximum number of ordered child-pair slots belonging to one parent. -/
def pairSlotCount : ℕ := levelFourPairSlotCount

/-- Read one coordinate of a constituent shape. -/
def shapeCoordinate (shape : Shape) (coordinate : ℕ) : ℕ :=
  if coordinate = 0 then shape.x else if coordinate = 1 then shape.y else shape.z

/-- Big-endian base-three digit of a fixed-length word code. -/
def ternaryDigit (length code position : ℕ) : ℕ :=
  code / 3 ^ (length - 1 - position) % 3

/-- Sum of the ternary digits in a fixed-length word code. -/
def ternaryCodeWeight (length code : ℕ) : ℕ :=
  ((List.range length).map fun position ↦ ternaryDigit length code position).sum

/-- Increasing base-three codes of fixed length and prescribed digit sum. -/
def ternarySupportCodes (length total : ℕ) : List ℕ :=
  (List.range (3 ^ length)).filter fun code ↦ ternaryCodeWeight length code = total

/-- Ternary word code at one padded support slot; an invalid slot reads as zero. -/
def ternarySupportCodeAt (length total symbol : ℕ) : ℕ :=
  (ternarySupportCodes length total)[symbol]?.getD 0

/-- Certificate index of a total-eight constituent shape. -/
def shapeEightIndex (shape : Shape) : ℕ :=
  (shapes 8).idxOf shape

/-- Positive total-sixteen parent occupying a proof-free certificate index. -/
def parentShapeAt (parent : ℕ) : Shape :=
  positiveLevelFourShapes[parent]?.getD default

/-- Certificate-order valid local pair slots for a positive parent. -/
def validSlots (parent : ℕ) : List ℕ :=
  (List.range pairSlotCount).filter fun slot ↦
    decide (slot < (levelFourPairsForParent (parentShapeAt parent)).length)

/-- Ordered child pair at one proof-free parent-local slot. -/
def pairAt (parent slot : ℕ) : Shape × Shape :=
  (levelFourPairsForParent (parentShapeAt parent))[slot]?.getD default

/-- Add a numerator at a padded row position when that position is in range. -/
def addNumeratorAt (row : Array ℕ) (slot numerator : ℕ) : Array ℕ :=
  if slot < row.size then row.modify slot (· + numerator) else row

/-- Parent slot obtained from already-materialized parent and child support-code lists.

This is the efficient inner operation used by route-once certificate checkers.  Keeping the three
support lists explicit lets a caller compute them once outside a child-symbol fold.
-/
def concatenatedParentSlotFromSupports (parentSupport leftSupport rightSupport : List ℕ)
    (leftSymbol rightSymbol : ℕ) : ℕ :=
  let leftCode := leftSupport[leftSymbol]?.getD 0
  let rightCode := rightSupport[rightSymbol]?.getD 0
  parentSupport.idxOf (leftCode * 3 ^ childWordLength + rightCode)

/-- Parent support slot formed by concatenating two child support words. -/
def concatenatedParentSlotForPair (parent coordinate : ℕ) (pair : Shape × Shape)
    (leftSymbol rightSymbol : ℕ) : ℕ :=
  concatenatedParentSlotFromSupports
    (ternarySupportCodes parentWordLength
      (shapeCoordinate (parentShapeAt parent) coordinate))
    (ternarySupportCodes childWordLength (shapeCoordinate pair.1 coordinate))
    (ternarySupportCodes childWordLength (shapeCoordinate pair.2 coordinate))
    leftSymbol rightSymbol

end MatrixMultiplication.BetaFourLocalGeometry
