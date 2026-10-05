/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveCompleteSplitOccurrenceLaw
import MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
import MatrixMultiplication.SimplifiedExponentLevelFourValidity

/-!
# Labelled level-four child occurrences in the simplified certificate

The top split row is an ordered law: one valid slot names a left child, while the stored second
shape is its labelled right child.  The complete-split rows below therefore retain the two sides
as separate occurrences.  This is important at self-complementary slots, where the two
occurrences have the same coarse child shape but must still contribute twice.

This module is the semantic source of the compatibility target tables.  It uses the raw
`topSplitNumerator`, not the already-symmetrized evaluator count.  A downstream finite theorem
may reindex right occurrences and recover the evaluator formula

`(topSplitNumerator u + topSplitNumerator (s-u)) * betaThree(u)`.

No compatibility zero-out, competitor bound, tensor restriction, or numerical inequality is
assumed here.
-/

namespace MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveParentTerms
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- A proof-free evaluator coordinate order describes the same logical-to-physical orientation as
`sigma`. -/
def CoordinateOrder.AgreesWithOrientation
    (order : CoordinateOrder) (sigma : Orientation) : Prop :=
  ∀ c, coordinateForLeg order c = coordinateOfLeg (sigma c)

/-- The proof-free valid-slot list contains no duplicate local indices. -/
theorem validSlots_nodup (parent : ℕ) : (validSlots parent).Nodup := by
  exact List.nodup_range.filter _

/-- The proof-free list membership subtype is equivalent to the intrinsic valid-slot type. -/
def validSlotsEquiv (parent : Fin positiveLevelFourShapeCount) :
    {slot : ℕ // slot ∈ (validSlots parent.val).toFinset} ≃
      LevelFourValidSlot parent where
  toFun slot := by
    have hmem : slot.1 ∈ validSlots parent.val := List.mem_toFinset.mp slot.2
    have hbounds : slot.1 < pairSlotCount ∧
        slot.1 < (levelFourPairsForParent (positiveLevelFourShape parent)).length := by
      simpa [validSlots, parentShapeAt_eq_positiveLevelFourShape] using hmem
    exact ⟨⟨slot.1, hbounds.1⟩, hbounds.2⟩
  invFun slot :=
    ⟨slot.1.val, List.mem_toFinset.mpr (by
      simp only [validSlots, List.mem_filter, List.mem_range, decide_eq_true_eq]
      rw [parentShapeAt_eq_positiveLevelFourShape]
      exact ⟨slot.1.isLt, slot.2⟩)⟩
  left_inv slot := by
    apply Subtype.ext
    rfl
  right_inv slot := by
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- Summing a proof-free function over `validSlots` is the same as summing over the intrinsic
valid-slot `Fintype`. -/
theorem sum_validSlots_eq_sum_validSlot
    (parent : Fin positiveLevelFourShapeCount) (f : ℕ → ℕ) :
    ((validSlots parent.val).map f).sum =
      ∑ slot : LevelFourValidSlot parent, f slot.1.val := by
  let slots : Finset ℕ := (validSlots parent.val).toFinset
  calc
    ((validSlots parent.val).map f).sum = ∑ slot ∈ slots, f slot := by
      rw [show slots = (validSlots parent.val).toFinset by rfl,
        ← List.toFinset_eq (validSlots_nodup parent.val)]
      rfl
    _ = ∑ slot : slots, f slot.1 := by
      rw [Finset.sum_coe_sort]
    _ = ∑ slot : LevelFourValidSlot parent, f slot.1.val := by
      exact Fintype.sum_equiv (validSlotsEquiv parent)
        (fun slot : slots ↦ f slot.1)
        (fun slot : LevelFourValidSlot parent ↦ f slot.1.val)
        (fun _ ↦ rfl)

/-- Concrete characterization of positive `Y` cells for the one-part constituent interface. -/
theorem yCompatibilityCell_eq_pooled_iff
    (q : CoarseIndex PUnit) (part : PUnit) (y : ℕ) :
    yCompatibilityCell q = .pooled part y ↔ q.z ≠ 0 ∧ q.y = y := by
  cases part
  by_cases hz : q.z = 0 <;> simp [yCompatibilityCell, hz]

/-- Concrete characterization of positive `Z` cells for the one-part constituent interface. -/
theorem zCompatibilityCell_eq_pooled_iff
    (q : CoarseIndex PUnit) (part : PUnit) (z : ℕ) :
    zCompatibilityCell q = .pooled part z ↔
      q.x ≠ 0 ∧ q.y ≠ 0 ∧ q.z = z := by
  cases part
  by_cases hx : q.x = 0
  · simp [zCompatibilityCell, hx]
  · by_cases hy : q.y = 0 <;> simp [zCompatibilityCell, hx, hy]

/-- Two compatibility target packages are equal when their five data tables agree pointwise.
The three boundary fields are propositions and therefore agree by proof irrelevance. -/
theorem compatibilityTargets_extensionality
    {Part : Type*} {depth : ℕ}
    {left right : CompatibilityTargets Part depth}
    (hx : left.xExact = right.xExact)
    (hy : left.yExact = right.yExact)
    (hz : left.zExact = right.zExact)
    (hyp : left.yPooled = right.yPooled)
    (hzp : left.zPooled = right.zPooled) :
    left = right := by
  cases left with
  | mk lx ly lz lyp lzp _ _ _ =>
    cases right with
    | mk rx ry rz ryp rzp _ _ _ =>
      dsimp at hx hy hz hyp hzp
      subst rx
      subst ry
      subst rz
      subst ryp
      subst rzp
      rfl

/-- Intrinsic child shape carried by one labelled occurrence of a raw ordered level-four slot. -/
def levelFourOccurrenceChildShape
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent)) :
    RecursiveChildShape ((positiveLevelFourShape parent).orientedLeg sigma) 8 :=
  match occurrence.2 with
  | .left => levelFourChildShape parent sigma occurrence.1
  | .right =>
      RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma occurrence.1)

@[simp] theorem levelFourOccurrenceChildShape_left
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) :
    levelFourOccurrenceChildShape parent sigma (slot, .left) =
      levelFourChildShape parent sigma slot :=
  rfl

@[simp] theorem levelFourOccurrenceChildShape_right
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) :
    levelFourOccurrenceChildShape parent sigma (slot, .right) =
      RecursiveChildShape.complement (levelFourParentIndex_total_twice parent sigma)
        (levelFourChildShape parent sigma slot) :=
  rfl

/-- Logical coarse index of an intrinsic recursive child shape. -/
def recursiveChildShapeCoarseIndex
    {parentCount : Leg → ℕ} {childTotal : ℕ}
    (child : RecursiveChildShape parentCount childTotal) : CoarseIndex PUnit where
  part := PUnit.unit
  x := child.get .X
  y := child.get .Y
  z := child.get .Z

@[simp] theorem recursiveChildShapeCoarseIndex_get
    {parentCount : Leg → ℕ} {childTotal : ℕ}
    (child : RecursiveChildShape parentCount childTotal) (c : Leg) :
    (recursiveChildShapeCoarseIndex child).get c = child.get c := by
  cases c <;> rfl

/-- Logical coarse index observed at one labelled raw-slot occurrence. -/
def levelFourOccurrenceCoarseIndex
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent)) :
    CoarseIndex PUnit :=
  recursiveChildShapeCoarseIndex
    (levelFourOccurrenceChildShape parent sigma occurrence)

/-- Every labelled level-four occurrence is a tight depth-two child constituent. -/
theorem levelFourOccurrenceCoarseIndex_total
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent)) :
    (levelFourOccurrenceCoarseIndex parent sigma occurrence).x +
        (levelFourOccurrenceCoarseIndex parent sigma occurrence).y +
        (levelFourOccurrenceCoarseIndex parent sigma occurrence).z = coarseTotal 2 := by
  simpa [levelFourOccurrenceCoarseIndex, recursiveChildShapeCoarseIndex,
    coarseTotal] using (levelFourOccurrenceChildShape parent sigma occurrence).total_eq

/-- Coarse index attached to the ordered left child at one valid slot. -/
def levelFourSlotCoarseIndex
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) : CoarseIndex PUnit :=
  recursiveChildShapeCoarseIndex (levelFourChildShape parent sigma slot)

/-- The explicit left/right occurrence map agrees with child-state transport by the canonical
slot-complement permutation. -/
theorem levelFourOccurrenceChildShape_eq_childState
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent)) :
    levelFourOccurrenceChildShape parent sigma occurrence =
      levelFourChildShape parent sigma
        (occurrence.childState (levelFourComplementSlotPerm parent)) := by
  obtain ⟨slot, side⟩ := occurrence
  cases side with
  | left => rfl
  | right =>
      exact (levelFourChildShape_complement parent sigma slot).symm

/-- Coarse occurrence lookup is equivalently the slot coarse map after canonical child-state
transport. -/
theorem levelFourOccurrenceCoarseIndex_eq_childState
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent)) :
    levelFourOccurrenceCoarseIndex parent sigma occurrence =
      levelFourSlotCoarseIndex parent sigma
        (occurrence.childState (levelFourComplementSlotPerm parent)) := by
  rw [levelFourOccurrenceCoarseIndex, levelFourSlotCoarseIndex,
    levelFourOccurrenceChildShape_eq_childState]

/-- Under the explicit order/orientation agreement, the proof-free evaluator coarse index is the
intrinsic logical child-shape index. -/
theorem fixedParentCoarseIndex_eq_levelFourSlotCoarseIndex
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    fixedParentCoarseIndex order parent.val slot.1.val =
      levelFourSlotCoarseIndex parent sigma slot := by
  apply CoarseIndex.ext
  · rfl
  · change
      shapeCoordinate (pairAt parent.val slot.1.val).1 order.x =
        (levelFourChildShape parent sigma slot).get .X
    rw [show order.x = coordinateOfLeg (sigma .X) by exact horder .X,
      pairAt_eq_levelFourPairAtSlot, levelFourChildShape_get,
      shapeCoordinate_coordinateOfLeg]
    rfl
  · change
      shapeCoordinate (pairAt parent.val slot.1.val).1 order.y =
        (levelFourChildShape parent sigma slot).get .Y
    rw [show order.y = coordinateOfLeg (sigma .Y) by exact horder .Y,
      pairAt_eq_levelFourPairAtSlot, levelFourChildShape_get,
      shapeCoordinate_coordinateOfLeg]
    rfl
  · change
      shapeCoordinate (pairAt parent.val slot.1.val).1 order.z =
        (levelFourChildShape parent sigma slot).get .Z
    rw [show order.z = coordinateOfLeg (sigma .Z) by exact horder .Z,
      pairAt_eq_levelFourPairAtSlot, levelFourChildShape_get,
      shapeCoordinate_coordinateOfLeg]
    rfl

/-- Exact complete-split law on both labelled occurrences of every raw ordered top slot. -/
def levelFourOccurrenceLaw
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) :
    ComplementaryOccurrenceLaw
      (fun slot ↦ levelFourSlotNumerator top root region parent slot *
        (levelFourChildSamples * levelFourChildSamples))
      (SplitWord 2) where
  count occurrence word :=
    match occurrence.2 with
    | .left =>
        levelFourSlotNumerator top root region parent occurrence.1 * levelFourChildSamples *
          levelFourLeftChildWordCount betaThree region parent sigma occurrence.1 c word
    | .right =>
        levelFourSlotNumerator top root region parent occurrence.1 * levelFourChildSamples *
          levelFourRightChildWordCount betaThree region parent sigma occurrence.1 c word
  rowSum occurrence := by
    obtain ⟨slot, side⟩ := occurrence
    by_cases hslot : levelFourSlotNumerator top root region parent slot = 0
    · cases side <;> simp [ComplementaryOccurrence.orderedState, hslot]
    · cases side with
      | left =>
          calc
            (∑ word,
                levelFourSlotNumerator top root region parent slot * levelFourChildSamples *
                  levelFourLeftChildWordCount betaThree region parent sigma slot c word) =
                (levelFourSlotNumerator top root region parent slot * levelFourChildSamples) *
                  ∑ word,
                    levelFourLeftChildWordCount betaThree region parent sigma slot c word := by
              rw [Finset.mul_sum]
            _ = (levelFourSlotNumerator top root region parent slot * levelFourChildSamples) *
                levelFourChildSamples := by
              rw [(hvalid slot c hslot).1]
            _ = levelFourSlotNumerator top root region parent slot *
                (levelFourChildSamples * levelFourChildSamples) := by
              ac_rfl
      | right =>
          calc
            (∑ word,
                levelFourSlotNumerator top root region parent slot * levelFourChildSamples *
                  levelFourRightChildWordCount betaThree region parent sigma slot c word) =
                (levelFourSlotNumerator top root region parent slot * levelFourChildSamples) *
                  ∑ word,
                    levelFourRightChildWordCount betaThree region parent sigma slot c word := by
              rw [Finset.mul_sum]
            _ = (levelFourSlotNumerator top root region parent slot * levelFourChildSamples) *
                levelFourChildSamples := by
              rw [(hvalid slot c hslot).2]
            _ = levelFourSlotNumerator top root region parent slot *
                (levelFourChildSamples * levelFourChildSamples) := by
              ac_rfl

@[simp] theorem levelFourOccurrenceLaw_count_left
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (slot : LevelFourValidSlot parent) (word : SplitWord 2) :
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
        (slot, .left) word =
      levelFourSlotNumerator top root region parent slot * levelFourChildSamples *
        levelFourLeftChildWordCount betaThree region parent sigma slot c word :=
  rfl

@[simp] theorem levelFourOccurrenceLaw_count_right
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (slot : LevelFourValidSlot parent) (word : SplitWord 2) :
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
        (slot, .right) word =
      levelFourSlotNumerator top root region parent slot * levelFourChildSamples *
        levelFourRightChildWordCount betaThree region parent sigma slot c word :=
  rfl

/-- Each labelled side of a raw slot has the full Cartesian child-profile mass.  In particular,
the two sides are not divided by two when their coarse child shapes coincide. -/
theorem sum_levelFourOccurrenceLaw_count
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent)) :
    (∑ word,
        (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
          occurrence word) =
      levelFourSlotNumerator top root region parent occurrence.1 *
        (levelFourChildSamples * levelFourChildSamples) :=
  (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).rowSum occurrence

/-- The complete-split row carried by a right occurrence is the left-child row at the canonical
complementary slot. -/
theorem levelFourRightChildWordCount_eq_left_complementSlot
    (betaThree : BetaThreeRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) (word : SplitWord 2) :
    levelFourRightChildWordCount betaThree region parent sigma slot c word =
      levelFourLeftChildWordCount betaThree region parent sigma
        (levelFourComplementSlot parent slot) c word := by
  simp only [levelFourRightChildWordCount, levelFourLeftChildWordCount]
  rw [levelFourPairAtSlot_complement, levelFourChildShape_complement]
  rfl

/-- The proof-free beta-three lookup in `fixedParentSlotCount` is the intrinsic left-child
complete-split row under the order/orientation agreement. -/
theorem betaThreeWordNumerator_eq_levelFourLeftChildWordCount
    (betaThree : BetaThreeRows) (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) (c : Leg) (word : SplitWord 2) :
    betaThreeWordNumerator betaThree
        (shapeEightIndex (pairAt parent.val slot.1.val).1 * regionCount + region.val)
        (coordinateForLeg order c).val
        (shapeCoordinate (pairAt parent.val slot.1.val).1
          (coordinateForLeg order c).val) word =
      levelFourLeftChildWordCount betaThree region parent sigma slot c word := by
  rw [horder c, pairAt_eq_levelFourPairAtSlot]
  simp only [levelFourLeftChildWordCount, levelFourChildShape_get,
    Shape.orientedLeg_apply, shapeCoordinate_coordinateOfLeg]
  rfl

/-- The proof-free global index of the complementary slot is the evaluator's reversed-pair
index. -/
theorem pairIndexAt_levelFourComplementSlot
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    pairIndexAt parent.val (levelFourComplementSlot parent slot).1.val =
      reversePairIndexAt parent.val slot.1.val := by
  unfold pairIndexAt reversePairIndexAt
  apply congrArg levelFourPairs.idxOf
  rw [pairAt_eq_levelFourPairAtSlot parent (levelFourComplementSlot parent slot),
    pairAt_eq_levelFourPairAtSlot parent slot,
    levelFourPairAtSlot_complement]

/-- Raw mass at the complementary typed slot is exactly the reverse-pair lookup used by the
proof-free evaluator. -/
theorem levelFourSlotNumerator_complement
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (slot : LevelFourValidSlot parent) :
    levelFourSlotNumerator top root region parent (levelFourComplementSlot parent slot) =
      topNumeratorFrom top root.val region.val (reversePairIndexAt parent.val slot.1.val) := by
  unfold levelFourSlotNumerator topSplitNumerator
  rw [pairIndexAt_levelFourComplementSlot]

/-- Reindexing a right occurrence by slot complementation exposes the left-child complete-split
row of the original slot. -/
theorem levelFourOccurrenceLaw_count_complement_right
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (slot : LevelFourValidSlot parent) (word : SplitWord 2) :
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
        (levelFourComplementSlot parent slot, .right) word =
      levelFourSlotNumerator top root region parent (levelFourComplementSlot parent slot) *
        levelFourChildSamples *
          levelFourLeftChildWordCount betaThree region parent sigma slot c word := by
  rw [levelFourOccurrenceLaw_count_right,
    levelFourRightChildWordCount_eq_left_complementSlot,
    levelFourComplementSlot_involutive parent slot]

/-- The evaluator's symmetrized per-child table is exactly the sum of the raw left occurrence and
the canonically reindexed raw right occurrence.  This is the finite provenance theorem behind
`orderedTopSplitNumerator`; self-complementary slots still contribute the two labelled summands. -/
theorem fixedParentSlotCount_eq_labelled_occurrence_pair
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (slot : LevelFourValidSlot parent) (c : Leg) (word : SplitWord 2) :
    fixedParentSlotCount top betaThree order root.val region.val parent.val slot.1.val c word =
      (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
          (slot, .left) word +
        (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
          (levelFourComplementSlot parent slot, .right) word := by
  rw [levelFourOccurrenceLaw_count_left,
    levelFourOccurrenceLaw_count_complement_right]
  simp only [fixedParentSlotCount]
  rw [betaThreeWordNumerator_eq_levelFourLeftChildWordCount
    betaThree order sigma horder region parent slot c word]
  unfold orderedTopSplitNumerator
  change
    (levelFourSlotNumerator top root region parent slot +
        topNumeratorFrom top root.val region.val
          (reversePairIndexAt parent.val slot.1.val)) *
          levelFourLeftChildWordCount betaThree region parent sigma slot c word *
            childRowRescale = _
  rw [← levelFourSlotNumerator_complement top root region parent slot]
  simp only [levelFourChildSamples, childRowRescale]
  ring

/-- Semantic exact coarse-cell profile obtained by pooling the two labelled occurrences. -/
noncomputable def levelFourOccurrenceExactCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (q : CoarseIndex PUnit) (word : SplitWord 2) : ℕ :=
  recursiveOccurrenceExactProfile (levelFourOccurrenceCoarseIndex parent sigma)
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) q word

/-- The explicit occurrence coarse map can be replaced by the canonical slot complement
permutation before applying the generic evaluator reindexing theorem. -/
theorem levelFourOccurrenceExactCount_eq_complementaryPooled
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (q : CoarseIndex PUnit) (word : SplitWord 2) :
    levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid c q word =
      recursiveComplementaryOccurrencePooledProfile
        (levelFourComplementSlotPerm parent) (levelFourSlotCoarseIndex parent sigma)
        (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) q word := by
  unfold levelFourOccurrenceExactCount recursiveOccurrenceExactProfile
    recursiveComplementaryOccurrencePooledProfile recursiveOccurrencePooledProfile
  apply Finset.sum_congr rfl
  intro occurrence _
  rw [levelFourOccurrenceCoarseIndex_eq_childState]

/-- The semantic exact occurrence table is the sum of the evaluator's symmetrized contribution
over the typed valid slots. -/
theorem levelFourOccurrenceExactCount_eq_sum_fixedParentSlotCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (q : CoarseIndex PUnit) (word : SplitWord 2) :
    levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid c q word =
      ∑ slot : LevelFourValidSlot parent,
        if levelFourSlotCoarseIndex parent sigma slot = q then
          fixedParentSlotCount top betaThree order root.val region.val parent.val
            slot.1.val c word
        else 0 := by
  rw [levelFourOccurrenceExactCount_eq_complementaryPooled,
    recursiveComplementaryOccurrencePooledProfile_eq_evaluator]
  apply Finset.sum_congr rfl
  intro slot _
  rw [levelFourComplementSlotPerm_symm]
  change
    (if levelFourSlotCoarseIndex parent sigma slot = q then
        (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
            (slot, .left) word +
          (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c).count
            (levelFourComplementSlot parent slot, .right) word
      else 0) = _
  rw [← fixedParentSlotCount_eq_labelled_occurrence_pair
    top betaThree order sigma horder root region parent hvalid slot c word]

/-- The semantic raw-occurrence table is definitionally faithful to the proof-free exact target
table exported for the evaluator. -/
theorem levelFourOccurrenceExactCount_eq_fixedParentExactCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (q : CoarseIndex PUnit) (word : SplitWord 2) :
    levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid c q word =
      fixedParentExactCount top betaThree order root.val region.val parent.val c q word := by
  rw [levelFourOccurrenceExactCount_eq_sum_fixedParentSlotCount
    top betaThree order sigma horder root region parent hvalid c q word]
  unfold fixedParentExactCount
  rw [sum_validSlots_eq_sum_validSlot]
  apply Finset.sum_congr rfl
  intro slot _
  rw [fixedParentCoarseIndex_eq_levelFourSlotCoarseIndex order sigma horder parent slot]

/-- Semantic pooled positive logical-`Y` compatibility profile. -/
noncomputable def levelFourOccurrenceYPooledCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (cellPart : PUnit) (y : ℕ) (word : SplitWord 2) : ℕ :=
  recursiveOccurrenceYPooledProfile (levelFourOccurrenceCoarseIndex parent sigma)
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Y)
    cellPart y word

/-- The semantic positive `Y` table is the sum of the evaluator's symmetrized contribution over
the typed valid slots in that compatibility cell. -/
theorem levelFourOccurrenceYPooledCount_eq_sum_fixedParentSlotCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (cellPart : PUnit) (y : ℕ) (word : SplitWord 2) :
    levelFourOccurrenceYPooledCount top betaThree root region parent sigma hvalid
        cellPart y word =
      ∑ slot : LevelFourValidSlot parent,
        if yCompatibilityCell (levelFourSlotCoarseIndex parent sigma slot) =
            .pooled cellPart y then
          fixedParentSlotCount top betaThree order root.val region.val parent.val
            slot.1.val .Y word
        else 0 := by
  calc
    levelFourOccurrenceYPooledCount top betaThree root region parent sigma hvalid
        cellPart y word =
      recursiveComplementaryOccurrencePooledProfile
        (levelFourComplementSlotPerm parent)
        (fun slot ↦ yCompatibilityCell (levelFourSlotCoarseIndex parent sigma slot))
        (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Y)
        (.pooled cellPart y) word := by
      unfold levelFourOccurrenceYPooledCount recursiveOccurrenceYPooledProfile
        recursiveComplementaryOccurrencePooledProfile recursiveOccurrencePooledProfile
      apply Finset.sum_congr rfl
      intro occurrence _
      simp only [levelFourOccurrenceCoarseIndex_eq_childState]
    _ = _ := by
      rw [recursiveComplementaryOccurrencePooledProfile_eq_evaluator]
      apply Finset.sum_congr rfl
      intro slot _
      rw [levelFourComplementSlotPerm_symm]
      change
        (if yCompatibilityCell (levelFourSlotCoarseIndex parent sigma slot) =
              .pooled cellPart y then
            (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Y).count
                (slot, .left) word +
              (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Y).count
                (levelFourComplementSlot parent slot, .right) word
          else 0) = _
      rw [← fixedParentSlotCount_eq_labelled_occurrence_pair
        top betaThree order sigma horder root region parent hvalid slot .Y word]

/-- The semantic raw-occurrence `Y` table equals the proof-free pooled target exported for the
evaluator. -/
theorem levelFourOccurrenceYPooledCount_eq_fixedParentYPooledCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (cellPart : PUnit) (y : ℕ) (word : SplitWord 2) :
    levelFourOccurrenceYPooledCount top betaThree root region parent sigma hvalid
        cellPart y word =
      fixedParentYPooledCount top betaThree order root.val region.val parent.val y word := by
  rw [levelFourOccurrenceYPooledCount_eq_sum_fixedParentSlotCount
    top betaThree order sigma horder root region parent hvalid cellPart y word]
  unfold fixedParentYPooledCount
  rw [sum_validSlots_eq_sum_validSlot]
  apply Finset.sum_congr rfl
  intro slot _
  simp only [fixedParentCoarseIndex_eq_levelFourSlotCoarseIndex
    order sigma horder parent slot, yCompatibilityCell_eq_pooled_iff]
  rfl

/-- Semantic pooled positive logical-`Z` compatibility profile. -/
noncomputable def levelFourOccurrenceZPooledCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (cellPart : PUnit) (z : ℕ) (word : SplitWord 2) : ℕ :=
  recursiveOccurrenceZPooledProfile (levelFourOccurrenceCoarseIndex parent sigma)
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Z)
    cellPart z word

/-- The semantic positive `Z` table is the sum of the evaluator's symmetrized contribution over
the typed valid slots in that compatibility cell. -/
theorem levelFourOccurrenceZPooledCount_eq_sum_fixedParentSlotCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (cellPart : PUnit) (z : ℕ) (word : SplitWord 2) :
    levelFourOccurrenceZPooledCount top betaThree root region parent sigma hvalid
        cellPart z word =
      ∑ slot : LevelFourValidSlot parent,
        if zCompatibilityCell (levelFourSlotCoarseIndex parent sigma slot) =
            .pooled cellPart z then
          fixedParentSlotCount top betaThree order root.val region.val parent.val
            slot.1.val .Z word
        else 0 := by
  calc
    levelFourOccurrenceZPooledCount top betaThree root region parent sigma hvalid
        cellPart z word =
      recursiveComplementaryOccurrencePooledProfile
        (levelFourComplementSlotPerm parent)
        (fun slot ↦ zCompatibilityCell (levelFourSlotCoarseIndex parent sigma slot))
        (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Z)
        (.pooled cellPart z) word := by
      unfold levelFourOccurrenceZPooledCount recursiveOccurrenceZPooledProfile
        recursiveComplementaryOccurrencePooledProfile recursiveOccurrencePooledProfile
      apply Finset.sum_congr rfl
      intro occurrence _
      simp only [levelFourOccurrenceCoarseIndex_eq_childState]
    _ = _ := by
      rw [recursiveComplementaryOccurrencePooledProfile_eq_evaluator]
      apply Finset.sum_congr rfl
      intro slot _
      rw [levelFourComplementSlotPerm_symm]
      change
        (if zCompatibilityCell (levelFourSlotCoarseIndex parent sigma slot) =
              .pooled cellPart z then
            (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Z).count
                (slot, .left) word +
              (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid .Z).count
                (levelFourComplementSlot parent slot, .right) word
          else 0) = _
      rw [← fixedParentSlotCount_eq_labelled_occurrence_pair
        top betaThree order sigma horder root region parent hvalid slot .Z word]

/-- The semantic raw-occurrence `Z` table equals the proof-free pooled target exported for the
evaluator. -/
theorem levelFourOccurrenceZPooledCount_eq_fixedParentZPooledCount
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (cellPart : PUnit) (z : ℕ) (word : SplitWord 2) :
    levelFourOccurrenceZPooledCount top betaThree root region parent sigma hvalid
        cellPart z word =
      fixedParentZPooledCount top betaThree order root.val region.val parent.val z word := by
  rw [levelFourOccurrenceZPooledCount_eq_sum_fixedParentSlotCount
    top betaThree order sigma horder root region parent hvalid cellPart z word]
  unfold fixedParentZPooledCount
  rw [sum_validSlots_eq_sum_validSlot]
  apply Finset.sum_congr rfl
  intro slot _
  simp only [fixedParentCoarseIndex_eq_levelFourSlotCoarseIndex
    order sigma horder parent slot, zCompatibilityCell_eq_pooled_iff]
  rfl

/-- Complete semantic target package derived from raw ordered slots and the finite boundary
checker.  Only child-row normalization and the paper's local boundary symmetries are inputs. -/
noncomputable def levelFourOccurrenceTargetData
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val) :
    RecursiveOccurrenceTargetData (depth := 2) (levelFourOccurrenceCoarseIndex parent sigma)
      (fun slot ↦ levelFourSlotNumerator top root region parent slot *
        (levelFourChildSamples * levelFourChildSamples)) where
  law c := levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c
  yBoundary q hz word := by
    change
      levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid .Y q word =
        levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid .X q
          (AlgebraicComplexity.complementSplitWord word)
    rw [levelFourOccurrenceExactCount_eq_fixedParentExactCount
        top betaThree order sigma horder root region parent hvalid .Y q word,
      levelFourOccurrenceExactCount_eq_fixedParentExactCount
        top betaThree order sigma horder root region parent hvalid .X q
          (AlgebraicComplexity.complementSplitWord word)]
    exact fixedParentExactCount_yBoundary top betaThree order root.val region.val parent.val
      hboundary q hz word
  zBoundaryOfX q hy word := by
    change
      levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid .Z q word =
        levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid .X q
          (AlgebraicComplexity.complementSplitWord word)
    rw [levelFourOccurrenceExactCount_eq_fixedParentExactCount
        top betaThree order sigma horder root region parent hvalid .Z q word,
      levelFourOccurrenceExactCount_eq_fixedParentExactCount
        top betaThree order sigma horder root region parent hvalid .X q
          (AlgebraicComplexity.complementSplitWord word)]
    exact fixedParentExactCount_zBoundaryOfX top betaThree order root.val region.val parent.val
      hboundary q hy word
  zBoundaryOfY q hx word := by
    change
      levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid .Z q word =
        levelFourOccurrenceExactCount top betaThree root region parent sigma hvalid .Y q
          (AlgebraicComplexity.complementSplitWord word)
    rw [levelFourOccurrenceExactCount_eq_fixedParentExactCount
        top betaThree order sigma horder root region parent hvalid .Z q word,
      levelFourOccurrenceExactCount_eq_fixedParentExactCount
        top betaThree order sigma horder root region parent hvalid .Y q
          (AlgebraicComplexity.complementSplitWord word)]
    exact fixedParentExactCount_zBoundaryOfY top betaThree order root.val region.val parent.val
      hboundary q hx word

/-- The compatibility targets built from the raw labelled-occurrence semantics are exactly the
proof-free targets consumed by the evaluator and finite checker. -/
theorem levelFourOccurrenceTargets_eq_fixedParentCompatibilityTargets
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val) :
    (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
        hvalid hboundary).toCompatibilityTargets =
      fixedParentCompatibilityTargets top betaThree order root.val region.val parent.val
        hboundary := by
  apply compatibilityTargets_extensionality
  · funext q word
    exact levelFourOccurrenceExactCount_eq_fixedParentExactCount
      top betaThree order sigma horder root region parent hvalid .X q word
  · funext q word
    exact levelFourOccurrenceExactCount_eq_fixedParentExactCount
      top betaThree order sigma horder root region parent hvalid .Y q word
  · funext q word
    exact levelFourOccurrenceExactCount_eq_fixedParentExactCount
      top betaThree order sigma horder root region parent hvalid .Z q word
  · funext part y word
    exact levelFourOccurrenceYPooledCount_eq_fixedParentYPooledCount
      top betaThree order sigma horder root region parent hvalid part y word
  · funext part z word
    exact levelFourOccurrenceZPooledCount_eq_fixedParentZPooledCount
      top betaThree order sigma horder root region parent hvalid part z word

end MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
