/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentRecursiveConstituent
import MatrixMultiplication.SimplifiedVolumeReconstruction
import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient
import Mathlib.Tactic.IntervalCases

/-!
# Exact complete-split recurrence for the simplified exponent certificate

This module reconstructs the depth-two and positive depth-four complete-split numerator rows used
by the recursive constituent rates.  It intentionally follows the mathematical word recurrence,
not the archived evaluator's precomputed scatter arrays:

* positive total-four children use the exact `CW_5` light/heavy law;
* nonpositive children use the supplied zero-law row, its ternary complement, and a point mass on
  the first zero coordinate;
* a positive total-eight parent is the split-weighted independent concatenation of its two
  total-four child laws.

All definitions return natural-number numerators.  The depth-two denominator is `2^12`; the
depth-four parent numerator therefore has denominator `2^(12+12+12) = 2^36`.  Generated clients
can cache and kernel-check bounded ranges of these functions before constructing entropy rows.

The fine law is quotient-neutral.  Its pushforward and the parent recurrence take the quotient's
slot map explicitly; the historical sorted-pair functions below are compatibility specializations.
This distinction matters because certificate tables for different quotients have the same Lean
type, so the type alone cannot prevent a mismatched recurrence.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedVolumeReconstruction

def localBits : ℕ := 12
def localDenominator : ℕ := 2 ^ localBits
def levelTwoWordLength : ℕ := 2
def levelThreeWordLength : ℕ := 4
def levelTwoSupportWidth : ℕ := 3
def levelThreeSupportWidth : ℕ := 19

/-- Read one coordinate of a constituent shape. -/
def shapeCoordinate (shape : Shape) (coordinate : ℕ) : ℕ :=
  if coordinate = 0 then shape.x else if coordinate = 1 then shape.y else shape.z

/-- Ternary word code at one padded support slot.  Invalid slots read as zero. -/
def ternarySupportCodeAt (length total symbol : ℕ) : ℕ :=
  (ternarySupportCodes length total)[symbol]?.getD 0

/-- Digitwise ternary complement of a fixed-length big-endian word code. -/
def ternaryComplementCode (length code : ℕ) : ℕ :=
  3 ^ length - 1 - code

/-- Slot of the complemented word in the support row of complementary total. -/
def ternaryComplementSlot (length total symbol : ℕ) : ℕ :=
  (ternarySupportCodes length (2 * length - total)).idxOf
    (ternaryComplementCode length (ternarySupportCodeAt length total symbol))

/-! The next five small theorems expose the actual level-two support geometry.  Keeping these
facts kernel-computed avoids trusting the archived evaluator's cached complement table. -/

theorem ternarySupportCodes_levelTwo_zero :
    ternarySupportCodes 2 0 = [0] := by decide

theorem ternarySupportCodes_levelTwo_one :
    ternarySupportCodes 2 1 = [1, 3] := by decide

theorem ternarySupportCodes_levelTwo_two :
    ternarySupportCodes 2 2 = [2, 4, 6] := by decide

theorem ternarySupportCodes_levelTwo_three :
    ternarySupportCodes 2 3 = [5, 7] := by decide

theorem ternarySupportCodes_levelTwo_four :
    ternarySupportCodes 2 4 = [8] := by decide

/-- On every genuine length-two support symbol, `ternaryComplementSlot` lands on the slot whose
code is the digitwise ternary complement.  This is the executable correctness condition that a
cached complement table must satisfy; unlike the archived Python table, it is independent of
construction order. -/
theorem ternaryComplementSlot_levelTwo_code
    (total symbol : ℕ)
    (htotal : total ≤ 2 * levelTwoWordLength)
    (hsymbol : symbol < (ternarySupportCodes levelTwoWordLength total).length) :
    ternarySupportCodeAt levelTwoWordLength (2 * levelTwoWordLength - total)
        (ternaryComplementSlot levelTwoWordLength total symbol) =
      ternaryComplementCode levelTwoWordLength
        (ternarySupportCodeAt levelTwoWordLength total symbol) := by
  norm_num [levelTwoWordLength] at htotal
  interval_cases total <;>
    simp only [levelTwoWordLength, ternarySupportCodes_levelTwo_zero,
      ternarySupportCodes_levelTwo_one, ternarySupportCodes_levelTwo_two,
      ternarySupportCodes_levelTwo_three, ternarySupportCodes_levelTwo_four,
      List.length_cons, List.length_nil] at hsymbol ⊢ <;>
    interval_cases symbol <;>
    decide

/-- First zero coordinate of a nonpositive shape, matching the published evaluator. -/
def zeroCoordinate (shape : Shape) : ℕ :=
  if shape.x = 0 then 0 else if shape.y = 0 then 1 else 2

/-- First positive coordinate of a nonpositive shape.  The supplied zero-law row lives here. -/
def primaryZeroLawCoordinate (shape : Shape) : ℕ :=
  if 0 < shape.x then 0 else if 0 < shape.y then 1 else 2

/-- The remaining coordinate receives the digitwise-complemented zero-law row. -/
def complementZeroLawCoordinate (shape : Shape) : ℕ :=
  (List.range 3).find? (fun coordinate ↦
      decide (coordinate ≠ zeroCoordinate shape ∧
        coordinate ≠ primaryZeroLawCoordinate shape))
    |>.getD 0

/-- Flat edge index for one `(positive node, region, padded split slot)` triple. -/
def edgeIndex (node region slot : ℕ) : ℕ :=
  node * 60 + region * 10 + slot

/-- Numerator of the supplied nonpositive depth-two zero-law row. -/
def edgeZeroLawNumerator (data : PrimaryTables) (node region slot symbol : ℕ) : ℕ :=
  dyadicNumeratorAt data.edgeZero2 (edgeIndex node region slot) symbol

/-- Exact depth-two complete-split numerator at denominator `2^12`.

The positive case is the typed `112` law: the heavy coordinate has probabilities
`(mu, 1-2mu, mu)` and both light coordinates are uniform on their two legal words. -/
def betaTwoNumerator (data : PrimaryTables)
    (node region slot coordinate symbol : ℕ) : ℕ :=
  if splitSlotIsValid node slot then
    let shape := splitShapeAt node slot
    if shape.IsPositive then
      if coordinate = (if shape.x = 2 then 0 else if shape.y = 2 then 1 else 2) then
        if symbol = 0 then scalarNumeratorAt data.mu (edgeIndex node region slot)
        else if symbol = 1 then
          localDenominator - 2 * scalarNumeratorAt data.mu (edgeIndex node region slot)
        else if symbol = 2 then scalarNumeratorAt data.mu (edgeIndex node region slot)
        else 0
      else if symbol < 2 then localDenominator / 2 else 0
    else
      if coordinate = zeroCoordinate shape then
        if symbol = 0 then localDenominator else 0
      else if coordinate = primaryZeroLawCoordinate shape then
        edgeZeroLawNumerator data node region slot symbol
      else if coordinate = complementZeroLawCoordinate shape then
        if symbol <
            (ternarySupportCodes levelTwoWordLength
              (shapeCoordinate shape coordinate)).length then
          edgeZeroLawNumerator data node region slot
            (ternaryComplementSlot levelTwoWordLength
              (shapeCoordinate shape coordinate) symbol)
        else 0
      else 0
  else 0

/-- Padded positions are not complete-split symbols.  In particular, the default code returned by
`ternarySupportCodeAt` outside the support must never be complemented back into a genuine atom.
This lemma is the generic safety property enforced by the explicit support guard above. -/
theorem betaTwoNumerator_complement_padding
    (data : PrimaryTables) (node region slot coordinate symbol : ℕ)
    (hslot : splitSlotIsValid node slot = true)
    (hnonpositive : ¬(splitShapeAt node slot).IsPositive)
    (hzero : coordinate ≠ zeroCoordinate (splitShapeAt node slot))
    (hprimary : coordinate ≠ primaryZeroLawCoordinate (splitShapeAt node slot))
    (hcomplement : coordinate = complementZeroLawCoordinate (splitShapeAt node slot))
    (hpadding :
      (ternarySupportCodes levelTwoWordLength
        (shapeCoordinate (splitShapeAt node slot) coordinate)).length ≤ symbol) :
    betaTwoNumerator data node region slot coordinate symbol = 0 := by
  subst coordinate
  simp [betaTwoNumerator, hslot, hnonpositive, hzero, hprimary,
    Nat.not_lt.mpr hpadding]

/-- Regression for the padded coordinate of the concrete `(0,0,4)` child at level three node
one, split slot zero.  Its physical coordinate one has total zero, hence only symbol zero is
legal; padded symbol one contributes no mass for every certificate table and region. -/
theorem betaTwoNumerator_nodeOne_shape004_padding
    (data : PrimaryTables) (region : ℕ) :
    betaTwoNumerator data 1 region 0 1 1 = 0 := by
  rfl

/-! ## The fixed sorted-pair quotient

The current certificate uses one globally consistent coarsening of every length-two
complete-split alphabet.  In the evaluator's increasing ternary-code order it is exactly

* total one: `[0, 0]`;
* total two: `[0, 1, 0]`; and
* total three: `[0, 0]`.

Totals zero and four are singletons.  The map is deliberately not injective. -/

/-- Decode a two-digit big-endian ternary code as the corresponding split word. -/
def splitPairOfTernaryCode (code : ℕ) : AlgebraicComplexity.SplitWord 1 :=
  AlgebraicComplexity.Examples.cwSplitPair
    ⟨code / 3 % 3, Nat.mod_lt _ (by decide)⟩
    ⟨code % 3, Nat.mod_lt _ (by decide)⟩

/-- Encode a two-digit split word in the evaluator's big-endian ternary convention. -/
def ternaryCodeOfSplitPair (word : AlgebraicComplexity.SplitWord 1) : ℕ :=
  (word 0 : ℕ) * 3 + (word 1 : ℕ)

/-- Target slot induced by sorting the actual split word and looking it up again in the
fixed-total support enumeration.  Thus the numerical recurrence uses the tensor quotient map
itself, rather than a second independently stated slot table. -/
def sortedPairSupportSlot (total symbol : ℕ) : ℕ :=
  (ternarySupportCodes levelTwoWordLength total).idxOf
    (ternaryCodeOfSplitPair
      (AlgebraicComplexity.Examples.cwSortedPairSplitWord
        (splitPairOfTernaryCode
          (ternarySupportCodeAt levelTwoWordLength total symbol))))

/-- Public statement-to-program bridge: `sortedPairSupportSlot` is exactly the slot action
induced by `cwSortedPairSplitWord` under the evaluator's support enumeration. -/
theorem sortedPairSupportSlot_eq_induced (total symbol : ℕ) :
    sortedPairSupportSlot total symbol =
      (ternarySupportCodes levelTwoWordLength total).idxOf
        (ternaryCodeOfSplitPair
          (AlgebraicComplexity.Examples.cwSortedPairSplitWord
            (splitPairOfTernaryCode
              (ternarySupportCodeAt levelTwoWordLength total symbol)))) :=
  rfl

theorem sortedPairSupportSlots_totalOne :
    (List.range 2).map (sortedPairSupportSlot 1) = [0, 0] := by decide

theorem sortedPairSupportSlots_totalTwo :
    (List.range 3).map (sortedPairSupportSlot 2) = [0, 1, 0] := by decide

theorem sortedPairSupportSlots_totalThree :
    (List.range 2).map (sortedPairSupportSlot 3) = [0, 0] := by decide

/-- On every genuine total/slot pair, looking up the induced target slot returns exactly the
ternary code of the sorted source word.  In particular `idxOf` never falls through to the padded
default on the certificate's structural support. -/
theorem ternarySupportCodeAt_sortedPairSupportSlot
    (total symbol : ℕ)
    (htotal : total ≤ 2 * levelTwoWordLength)
    (hsymbol : symbol < (ternarySupportCodes levelTwoWordLength total).length) :
    ternarySupportCodeAt levelTwoWordLength total
        (sortedPairSupportSlot total symbol) =
      ternaryCodeOfSplitPair
        (AlgebraicComplexity.Examples.cwSortedPairSplitWord
          (splitPairOfTernaryCode
            (ternarySupportCodeAt levelTwoWordLength total symbol))) := by
  norm_num [levelTwoWordLength] at htotal
  interval_cases total <;>
    simp only [levelTwoWordLength, ternarySupportCodes_levelTwo_zero,
      ternarySupportCodes_levelTwo_one, ternarySupportCodes_levelTwo_two,
      ternarySupportCodes_levelTwo_three, ternarySupportCodes_levelTwo_four,
      List.length_cons, List.length_nil] at hsymbol ⊢ <;>
    interval_cases symbol <;>
    decide

/-- Exact pushforward of the fine depth-two law through an arbitrary quotient slot map.

The slot map is the only quotient-specific input to the recurrence.  Keeping it explicit prevents
a certificate produced for one quotient from being interpreted silently with another quotient's
rows.  The output remains padded to width three, so later product recurrences need no shape
change.

Proof sketch: enumerate the three padded source symbols, retain exactly those sent to the requested
target slot, and add their fine-law numerators. -/
def quotientBetaTwoNumerator (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node region slot coordinate targetSymbol : ℕ) : ℕ :=
  ((List.range levelTwoSupportWidth).map fun sourceSymbol ↦
    if supportSlot
        (shapeCoordinate (splitShapeAt node slot) coordinate) sourceSymbol = targetSymbol then
      betaTwoNumerator data node region slot coordinate sourceSymbol
    else 0).sum

/-- Exact pushforward through the fixed sorted-pair quotient used by the original certificate. -/
def sortedPairBetaTwoNumerator (data : PrimaryTables)
    (node region slot coordinate targetSymbol : ℕ) : ℕ :=
  quotientBetaTwoNumerator sortedPairSupportSlot data
    node region slot coordinate targetSymbol

/-- Ordered split numerator `alpha(u) + alpha(parent-u)`. -/
def orderedSplitNumerator (data : PrimaryTables) (node region slot : ℕ) : ℕ :=
  dyadicNumeratorAt data.pos3Alpha (node * 6 + region) slot +
    dyadicNumeratorAt data.pos3Alpha (node * 6 + region) (complementSlotAt node slot)

/-- Contribution of one split and one pair of quotient child slots to a fixed parent word. -/
def quotientBetaThreeContribution (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
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
        quotientBetaTwoNumerator supportSlot data
          node region slot coordinate leftSymbol *
        quotientBetaTwoNumerator supportSlot data
          node region rightSlot coordinate rightSymbol
    else 0
  else 0

/-- Exact positive level-three parent numerator for an arbitrary quotient slot map. -/
def quotientBetaThreeRegionNumerator (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node region coordinate parentSymbol : ℕ) : ℕ :=
  ((List.range 10).flatMap fun slot ↦
      (List.range levelTwoSupportWidth).flatMap fun leftSymbol ↦
        (List.range levelTwoSupportWidth).map fun rightSymbol ↦
          quotientBetaThreeContribution supportSlot data node region coordinate parentSymbol
            slot leftSymbol rightSymbol).sum

/-- Serialized parent row for an arbitrary quotient, padded to the evaluator's width nineteen. -/
def quotientBetaThreeRegionRow (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node region coordinate : ℕ) : List ℕ :=
  (List.range levelThreeSupportWidth).map
    (quotientBetaThreeRegionNumerator supportSlot data node region coordinate)

/-- Sorted-pair specialization of one split's contribution to a fixed parent word. -/
def betaThreeContribution (data : PrimaryTables)
    (node region coordinate parentSymbol slot leftSymbol rightSymbol : ℕ) : ℕ :=
  quotientBetaThreeContribution sortedPairSupportSlot data node region coordinate parentSymbol
    slot leftSymbol rightSymbol

/-- Exact sorted-pair positive level-three parent row at denominator `2^36`. -/
def betaThreeRegionNumerator (data : PrimaryTables)
    (node region coordinate parentSymbol : ℕ) : ℕ :=
  quotientBetaThreeRegionNumerator sortedPairSupportSlot data node region coordinate parentSymbol

/-- Serialized sorted-pair depth-four parent row, padded to width nineteen. -/
def betaThreeRegionRow (data : PrimaryTables) (node region coordinate : ℕ) : List ℕ :=
  quotientBetaThreeRegionRow sortedPairSupportSlot data node region coordinate

end MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
