/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
import MatrixMultiplication.TernarySplitWordEncoding

set_option autoImplicit false

/-!
# Support geometry for level-four boundary complementation

The finite level-four compatibility interface asks for three slotwise boundary identities.  A
direct certificate checker can test those identities for every `(region, parent, slot, word)`, but
that repeats the same zero-law fact hundreds of times.  This file develops the reusable support
geometry and nonpositive beta-three recurrence laws used by the final boundary assembly in
`SimplifiedRecursiveLevelFourBoundary`.

For a nonpositive depth-three child, the recurrence stores one live coordinate row and defines the
other live row by digitwise ternary complementation.  The remaining coordinate is a point mass.
The point-mass case is forced by normalization when the child shape is one of `(8,0,0)`,
`(0,8,0)`, or `(0,0,8)`.  Thus an exact recurrence cache and the already-required active-child
normalization imply the complete slotwise boundary law.

The proof deliberately treats the ordered split and its reversed occurrence separately.  The
evaluator's `orderedTopSplitNumerator` is their sum, so a zero forward mass does not by itself make
the symmetrized occurrence inactive.

Complete-split distributions follow [alman2025more],
`papers/sources/2404.16349/prelim.tex:249-278`; their recursive decomposition and nonpositive
boundary convention appear in `papers/sources/2404.16349/constituent.tex:13-47`.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedRecursiveLevelFourBoundary

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Proof-level coordinate order for the repeated `XZY` certificate orientation. -/
def repeatedXzyCoordinateOrder : CoordinateOrder := ⟨0, 2, 1⟩

/-- The proof-level order and semantic tensor orientation assign the same physical coordinate to
each logical leg. -/
theorem repeatedXzyCoordinateOrder_agrees :
    CoordinateOrder.AgreesWithOrientation repeatedXzyCoordinateOrder xzy := by
  intro c
  cases c <;> rfl

@[simp] theorem fixedParentCoarseIndex_repeatedXzy_x (parent slot : ℕ) :
    (fixedParentCoarseIndex repeatedXzyCoordinateOrder parent slot).x =
      (pairAt parent slot).1.x :=
  rfl

@[simp] theorem fixedParentCoarseIndex_repeatedXzy_y (parent slot : ℕ) :
    (fixedParentCoarseIndex repeatedXzyCoordinateOrder parent slot).y =
      (pairAt parent slot).1.z :=
  rfl

@[simp] theorem fixedParentCoarseIndex_repeatedXzy_z (parent slot : ℕ) :
    (fixedParentCoarseIndex repeatedXzyCoordinateOrder parent slot).z =
      (pairAt parent slot).1.y :=
  rfl

@[simp] theorem fixedParentSlotCount_repeatedXzy_X
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent slot : ℕ) (word : SplitWord 2) :
    fixedParentSlotCount top betaThree repeatedXzyCoordinateOrder
        root region parent slot .X word =
      orderedTopSplitNumerator top root region parent slot *
        betaThreeWordNumerator betaThree
          (shapeEightIndex (pairAt parent slot).1 * regionCount + region)
          0 (pairAt parent slot).1.x word * childRowRescale :=
  rfl

@[simp] theorem fixedParentSlotCount_repeatedXzy_Y
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent slot : ℕ) (word : SplitWord 2) :
    fixedParentSlotCount top betaThree repeatedXzyCoordinateOrder
        root region parent slot .Y word =
      orderedTopSplitNumerator top root region parent slot *
        betaThreeWordNumerator betaThree
          (shapeEightIndex (pairAt parent slot).1 * regionCount + region)
          2 (pairAt parent slot).1.z word * childRowRescale :=
  rfl

@[simp] theorem fixedParentSlotCount_repeatedXzy_Z
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region parent slot : ℕ) (word : SplitWord 2) :
    fixedParentSlotCount top betaThree repeatedXzyCoordinateOrder
        root region parent slot .Z word =
      orderedTopSplitNumerator top root region parent slot *
        betaThreeWordNumerator betaThree
          (shapeEightIndex (pairAt parent slot).1 * regionCount + region)
          1 (pairAt parent slot).1.y word * childRowRescale :=
  rfl

/-! ## Length-four ternary support geometry -/

/-- The explicit evaluator code of a depth-two split word belongs to the support row named by the
word's digit sum. -/
theorem splitWordDepthTwoCode_mem_support (word : SplitWord 2) :
    splitWordDepthTwoCode word ∈
      ternarySupportCodes levelThreeWordLength (splitWordWeight word) := by
  change MatrixMultiplication.TernarySplitWordEncoding.splitWordDepthTwoCode word ∈
    MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
      MatrixMultiplication.BetaFourLocalGeometry.childWordLength (splitWordWeight word)
  exact MatrixMultiplication.TernarySplitWordEncoding.splitWordDepthTwoCode_mem_support word

/-- Every length-four fixed-total support row fits the evaluator's nineteen-symbol padding. -/
theorem ternarySupportCodes_depthTwoWord_length_le (word : SplitWord 2) :
    (ternarySupportCodes levelThreeWordLength (splitWordWeight word)).length ≤
      childSupportWidth := by
  change
    (MatrixMultiplication.BetaFourLocalGeometry.ternarySupportCodes
      MatrixMultiplication.BetaFourLocalGeometry.childWordLength
        (splitWordWeight word)).length ≤
      MatrixMultiplication.BetaFourLocalGeometry.childSupportWidth
  exact
    MatrixMultiplication.TernarySplitWordEncoding.ternarySupportCodes_depthTwoWord_length_le word

/-- Digitwise complementation of a depth-two split word agrees with the evaluator's complement of
its big-endian base-three code. -/
theorem splitWordDepthTwoCode_complement (word : SplitWord 2) :
    splitWordDepthTwoCode (complementSplitWord word) =
      ternaryComplementCode levelThreeWordLength (splitWordDepthTwoCode word) := by
  simpa [
      MatrixMultiplication.SimplifiedExponentLevelFourValidity.splitWordDepthTwoCode,
      MatrixMultiplication.TernarySplitWordEncoding.splitWordDepthTwoCode,
      ternaryComplementCode,
      levelThreeWordLength,
      MatrixMultiplication.BetaFourLocalGeometry.childWordLength] using
    MatrixMultiplication.TernarySplitWordEncoding.splitWordDepthTwoCode_complement word

/-- Complementing a genuine length-four support symbol lands at the support slot occupied by the
complemented split word.  This is the semantic version of the evaluator's positional lookup. -/
theorem ternaryComplementSlot_depthTwoWord (word : SplitWord 2) :
    ternaryComplementSlot levelThreeWordLength (splitWordWeight word)
        ((ternarySupportCodes levelThreeWordLength (splitWordWeight word)).idxOf
          (splitWordDepthTwoCode word)) =
      (ternarySupportCodes levelThreeWordLength
          (splitWordWeight (complementSplitWord word))).idxOf
        (splitWordDepthTwoCode (complementSplitWord word)) := by
  have hmem := splitWordDepthTwoCode_mem_support word
  have htotal :=
    AlgebraicComplexity.Examples.splitWordWeight_add_complementSplitWord word
  have htotal' :
      2 * levelThreeWordLength - splitWordWeight word =
        splitWordWeight (complementSplitWord word) := by
    simp only [coarseTotal, levelThreeWordLength] at htotal ⊢
    omega
  have hcodeAt :
      ternarySupportCodeAt levelThreeWordLength (splitWordWeight word)
          ((ternarySupportCodes levelThreeWordLength (splitWordWeight word)).idxOf
            (splitWordDepthTwoCode word)) = splitWordDepthTwoCode word := by
    unfold ternarySupportCodeAt
    rw [List.getElem?_idxOf hmem]
    rfl
  unfold ternaryComplementSlot
  rw [htotal', hcodeAt]
  exact congrArg (fun code ↦
      (ternarySupportCodes levelThreeWordLength
        (splitWordWeight (complementSplitWord word))).idxOf code)
    (splitWordDepthTwoCode_complement word).symm

/-! ## Exact nonpositive beta-three recurrence rows -/

/-- Flattening fixed-width consecutive blocks gives the ordinary consecutive enumeration. -/
private theorem flatMap_range_map_blocks
    {A : Type*} (blockCount blockWidth : ℕ) (f : ℕ → A) :
    (List.range blockCount).flatMap (fun block ↦
        (List.range blockWidth).map (fun offset ↦ f (block * blockWidth + offset))) =
      (List.range (blockCount * blockWidth)).map f := by
  induction blockCount with
  | zero => simp
  | succ blockCount ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih,
        Nat.succ_mul, List.range_add, List.map_append]
      simp only [List.map_map, Function.comp_def, Nat.add_comm]

/-- The two-level shape/region serialization is the direct consecutive row serialization. -/
theorem reconstructedBetaThreeRowsFor_eq_direct
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables) :
    reconstructedBetaThreeRowsFor supportSlot data =
      ((List.range (45 * regionCount)).map
        (betaThreeGlobalRowFor supportSlot data)).toArray := by
  unfold reconstructedBetaThreeRowsFor reconstructedBetaThreeShapeRowsFor
  exact congrArg List.toArray
    (flatMap_range_map_blocks 45 regionCount (betaThreeGlobalRowFor supportSlot data))

/-- A serialized beta-three cache agrees with the nonpositive branch of the exact recurrence.

Only rows whose shape is nonpositive are constrained.  Positive rows are produced by the
recursive mixture and play no role in a boundary-complement argument. -/
def FollowsNonpositiveBetaThreeRecurrence
    (data : PrimaryTables) (betaThree : BetaThreeRows) : Prop :=
  ∀ (shape : Shape), shape ∈ shapes 8 → ¬shape.IsPositive →
    ∀ (region : Fin regionCount) (coordinate : ℕ), coordinate < 3 →
      ∀ (total : ℕ) (word : SplitWord 2),
      betaThreeWordNumerator betaThree
          (shapeEightIndex shape * regionCount + region.val) coordinate total word =
        if splitWordWeight word = total then
          zeroBetaThreeBaseNumerator data
              (shapeEightIndex shape * regionCount + region.val) coordinate
              ((ternarySupportCodes levelThreeWordLength total).idxOf
                (splitWordDepthTwoCode word)) * betaThreeZeroRescale
        else 0

/-- The evaluator's first zero-coordinate selector always names a physical tensor leg. -/
theorem zeroCoordinate_lt_three (shape : Shape) : zeroCoordinate shape < 3 := by
  unfold zeroCoordinate
  split
  · omega
  · split <;> omega

/-- The evaluator's primary live-coordinate selector always names a physical tensor leg. -/
theorem primaryZeroLawCoordinate_lt_three (shape : Shape) :
    primaryZeroLawCoordinate shape < 3 := by
  unfold primaryZeroLawCoordinate
  split
  · omega
  · split <;> omega

/-- The remaining live-coordinate selector is drawn from `List.range 3`; its default is also a
physical tensor leg. -/
theorem complementZeroLawCoordinate_lt_three (shape : Shape) :
    complementZeroLawCoordinate shape < 3 := by
  unfold complementZeroLawCoordinate
  generalize hfind : (List.range 3).find? (fun coordinate ↦
      decide (coordinate ≠ zeroCoordinate shape ∧
        coordinate ≠ primaryZeroLawCoordinate shape)) = found
  cases found with
  | none => simp
  | some coordinate =>
      have hmem : coordinate ∈ List.range 3 := List.mem_of_find?_eq_some hfind
      simpa using hmem

/-- Looking up the shape attached to a valid total-eight shape index recovers that shape. -/
theorem zeroThreeShapeAt_shapeEightIndex (shape : Shape) (hshape : shape ∈ shapes 8)
    (region : Fin regionCount) :
    zeroThreeShapeAt (shapeEightIndex shape * regionCount + region.val) = shape := by
  unfold zeroThreeShapeAt shapeEightIndex
  change (shapes 8)[((shapes 8).idxOf shape * 6 + region.val) / 6]?.getD default = shape
  have hregion : region.val < 6 := by
    simpa [MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.regionCount] using
      region.isLt
  have hdiv : ((shapes 8).idxOf shape * 6 + region.val) / 6 =
      (shapes 8).idxOf shape := by
    omega
  rw [hdiv, List.getElem?_idxOf hshape]
  rfl

/-- Reading a valid coordinate and padded symbol from a reconstructed nonpositive row returns the
literal zero-law recurrence numerator.  This is the small cache-correctness lemma needed by the
structural boundary proof; it evaluates no certificate constants. -/
theorem betaThreeNumeratorFrom_reconstructedBetaThreeRowsFor_of_nonpositive
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (row coordinate symbol : ℕ)
    (hrow : row < 45 * regionCount)
    (hnonpositive : ¬(zeroThreeShapeAt row).IsPositive)
    (hcoordinate : coordinate < 3)
    (hsymbol : symbol < childSupportWidth) :
    betaThreeNumeratorFrom (reconstructedBetaThreeRowsFor supportSlot data)
        row coordinate symbol =
      zeroBetaThreeBaseNumerator data row coordinate symbol * betaThreeZeroRescale := by
  rw [reconstructedBetaThreeRowsFor_eq_direct]
  unfold betaThreeNumeratorFrom
  simp only [List.getElem?_toArray]
  rw [List.getElem?_map, List.getElem?_range hrow]
  simp only [Option.map_some, Option.getD_some]
  unfold betaThreeGlobalRowFor
  rw [if_neg hnonpositive]
  simp only [List.getElem?_toArray]
  rw [List.getElem?_map, List.getElem?_range hcoordinate]
  simp only [Option.map_some, Option.getD_some]
  simp only [List.getElem?_toArray]
  rw [List.getElem?_map, List.getElem?_range hsymbol]
  rfl

/-- The literal reconstructed cache satisfies the abstract nonpositive recurrence interface. -/
theorem reconstructedBetaThreeRowsFor_followsNonpositiveBetaThreeRecurrence
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables) :
    FollowsNonpositiveBetaThreeRecurrence data
      (reconstructedBetaThreeRowsFor supportSlot data) := by
  intro shape hshape hnonpositive region coordinate hcoordinate total word
  by_cases hweight : splitWordWeight word = total
  · rw [if_pos hweight]
    unfold betaThreeWordNumerator
    rw [if_pos hweight]
    apply betaThreeNumeratorFrom_reconstructedBetaThreeRowsFor_of_nonpositive
    · have hindex : shapeEightIndex shape < 45 := by
        unfold shapeEightIndex
        have hlt := List.idxOf_lt_length_of_mem hshape
        rw [MatrixMultiplication.LevelFourRemainingReconstruction.shapes_eight_length] at hlt
        exact hlt
      exact by
        have hregion := region.isLt
        simp only [
          MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.regionCount] at hregion ⊢
        omega
    · rw [zeroThreeShapeAt_shapeEightIndex shape hshape region]
      exact hnonpositive
    · exact hcoordinate
    · have hmem : splitWordDepthTwoCode word ∈
          ternarySupportCodes levelThreeWordLength total := by
        simpa [hweight] using splitWordDepthTwoCode_mem_support word
      have hlength :
          (ternarySupportCodes levelThreeWordLength total).length ≤ childSupportWidth := by
        simpa [hweight] using ternarySupportCodes_depthTwoWord_length_le word
      exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem hmem) hlength
  · simp [betaThreeWordNumerator, hweight]

/-- On a nonpositive reconstructed row, guarded word lookup reduces to the literal zero-law
numerator. -/
theorem betaThreeWordNumerator_eq_zeroRecurrence
    (data : PrimaryTables) (betaThree : BetaThreeRows)
    (hrows : FollowsNonpositiveBetaThreeRecurrence data betaThree)
    (shape : Shape) (hshape : shape ∈ shapes 8) (hnonpositive : ¬shape.IsPositive)
    (region : Fin regionCount) (coordinate total : ℕ) (word : SplitWord 2)
    (hcoordinate : coordinate < 3) :
    betaThreeWordNumerator betaThree
        (shapeEightIndex shape * regionCount + region.val) coordinate total word =
      if splitWordWeight word = total then
        zeroBetaThreeBaseNumerator data
            (shapeEightIndex shape * regionCount + region.val) coordinate
            ((ternarySupportCodes levelThreeWordLength total).idxOf
              (splitWordDepthTwoCode word)) * betaThreeZeroRescale
      else 0 := by
  exact hrows shape hshape hnonpositive region coordinate hcoordinate total word

/-- The live row selected as the primary zero law is read without a support permutation. -/
theorem zeroBetaThreeBaseNumerator_primary
    (data : PrimaryTables) (row coordinate symbol : ℕ) (shape : Shape)
    (hshape : zeroThreeShapeAt row = shape)
    (hcoordinate : coordinate = primaryZeroLawCoordinate shape)
    (hne : primaryZeroLawCoordinate shape ≠ zeroCoordinate shape) :
    zeroBetaThreeBaseNumerator data row coordinate symbol =
      dyadicNumeratorAt data.zero3 row symbol := by
  subst coordinate
  simp [zeroBetaThreeBaseNumerator, hshape, hne]

/-- The other live coordinate of a nonpositive row is the digitwise-complement pushforward of the
primary row. -/
theorem zeroBetaThreeBaseNumerator_complement
    (data : PrimaryTables) (row coordinate symbol : ℕ) (shape : Shape)
    (hshape : zeroThreeShapeAt row = shape)
    (hcoordinate : coordinate = complementZeroLawCoordinate shape)
    (hneZero : complementZeroLawCoordinate shape ≠ zeroCoordinate shape)
    (hnePrimary : complementZeroLawCoordinate shape ≠ primaryZeroLawCoordinate shape) :
    zeroBetaThreeBaseNumerator data row coordinate symbol =
      if symbol <
          (ternarySupportCodes levelThreeWordLength
            (shapeCoordinate shape coordinate)).length then
        dyadicNumeratorAt data.zero3 row
          (ternaryComplementSlot levelThreeWordLength
            (shapeCoordinate shape coordinate) symbol)
      else 0 := by
  subst coordinate
  simp [zeroBetaThreeBaseNumerator, hshape, hneZero, hnePrimary]

/-- The two live coordinates of a nonpositive recurrence row carry complementary complete-split
laws.  This statement includes no certificate values: it follows solely from the recurrence's
definition of the complement row and the exact support-slot transport above. -/
theorem betaThreeWordNumerator_complement_eq_primary
    (data : PrimaryTables) (betaThree : BetaThreeRows)
    (hrows : FollowsNonpositiveBetaThreeRecurrence data betaThree)
    (shape : Shape) (hshape : shape ∈ shapes 8) (hnonpositive : ¬shape.IsPositive)
    (region : Fin regionCount) (word : SplitWord 2)
    (hnePrimary : primaryZeroLawCoordinate shape ≠ zeroCoordinate shape)
    (hneComplementZero : complementZeroLawCoordinate shape ≠ zeroCoordinate shape)
    (hneComplementPrimary :
      complementZeroLawCoordinate shape ≠ primaryZeroLawCoordinate shape)
    (htotals :
      shapeCoordinate shape (primaryZeroLawCoordinate shape) +
          shapeCoordinate shape (complementZeroLawCoordinate shape) = coarseTotal 2) :
    betaThreeWordNumerator betaThree
        (shapeEightIndex shape * regionCount + region.val)
        (complementZeroLawCoordinate shape)
        (shapeCoordinate shape (complementZeroLawCoordinate shape)) word =
      betaThreeWordNumerator betaThree
        (shapeEightIndex shape * regionCount + region.val)
        (primaryZeroLawCoordinate shape)
        (shapeCoordinate shape (primaryZeroLawCoordinate shape))
        (complementSplitWord word) := by
  let row := shapeEightIndex shape * regionCount + region.val
  let complementTotal := shapeCoordinate shape (complementZeroLawCoordinate shape)
  let primaryTotal := shapeCoordinate shape (primaryZeroLawCoordinate shape)
  have hshapeAt : zeroThreeShapeAt row = shape :=
    zeroThreeShapeAt_shapeEightIndex shape hshape region
  rw [betaThreeWordNumerator_eq_zeroRecurrence data betaThree hrows shape hshape
      hnonpositive region (complementZeroLawCoordinate shape) complementTotal word
      (complementZeroLawCoordinate_lt_three shape),
    betaThreeWordNumerator_eq_zeroRecurrence data betaThree hrows shape hshape
      hnonpositive region (primaryZeroLawCoordinate shape) primaryTotal
      (complementSplitWord word) (primaryZeroLawCoordinate_lt_three shape)]
  by_cases hweight : splitWordWeight word = complementTotal
  · have hcomplementWeight :
        splitWordWeight (complementSplitWord word) = primaryTotal := by
      have hsum :=
        AlgebraicComplexity.Examples.splitWordWeight_add_complementSplitWord word
      dsimp [primaryTotal, complementTotal] at hweight ⊢
      omega
    rw [if_pos hweight, if_pos hcomplementWeight]
    rw [zeroBetaThreeBaseNumerator_complement data row
        (complementZeroLawCoordinate shape)
        ((ternarySupportCodes levelThreeWordLength complementTotal).idxOf
          (splitWordDepthTwoCode word)) shape hshapeAt rfl hneComplementZero
          hneComplementPrimary,
      zeroBetaThreeBaseNumerator_primary data row
        (primaryZeroLawCoordinate shape)
        ((ternarySupportCodes levelThreeWordLength primaryTotal).idxOf
          (splitWordDepthTwoCode (complementSplitWord word))) shape hshapeAt rfl
          hnePrimary]
    have hmem : splitWordDepthTwoCode word ∈
        ternarySupportCodes levelThreeWordLength complementTotal := by
      simpa [hweight] using splitWordDepthTwoCode_mem_support word
    have hslot :
        (ternarySupportCodes levelThreeWordLength complementTotal).idxOf
            (splitWordDepthTwoCode word) <
          (ternarySupportCodes levelThreeWordLength complementTotal).length :=
      List.idxOf_lt_length_of_mem hmem
    rw [if_pos hslot]
    have htransport := ternaryComplementSlot_depthTwoWord word
    rw [hweight, hcomplementWeight] at htransport
    rw [htransport]
  · have hcomplementWeight :
        splitWordWeight (complementSplitWord word) ≠ primaryTotal := by
      intro hcontra
      have hsum :=
        AlgebraicComplexity.Examples.splitWordWeight_add_complementSplitWord word
      dsimp [primaryTotal, complementTotal] at hcontra hweight ⊢
      omega
    rw [if_neg hweight, if_neg hcomplementWeight]


end MatrixMultiplication.SimplifiedRecursiveLevelFourBoundary
