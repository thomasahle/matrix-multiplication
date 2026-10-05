/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.SignedDyadicLogCanonical
import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetSupport

/-!
# Executable validity checks for level-four constituent rows

Generated level-four chunks use the bounded Boolean checker below to turn literal row snapshots
into the `LocalRows.IsValid` hypotheses needed by the mathematical fixed-marginal theorem.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourValidity

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SignedDyadicLogForm
open AlgebraicComplexity
open AlgebraicComplexity.Tensor
open AlgebraicComplexity.MoreAsymmetryCompatibility

/-- The constituent-local compatibility theorem has one part tag. -/
abbrev FixedParentPart : Type := PUnit

/-- Extensionality for serialized level-four local rows. -/
theorem localRows_ext {left right : LocalRows coordinateCount}
    (hsupport : left.support = right.support)
    (hreference : left.referenceNumerators = right.referenceNumerators)
    (hmarginal : left.marginalXNumerators = right.marginalXNumerators)
    (hweightX : left.weightX = right.weightX)
    (hweightY : left.weightY = right.weightY)
    (hweightZ : left.weightZ = right.weightZ)
    (hlogicalY : left.logicalY = right.logicalY)
    (hlogicalZ : left.logicalZ = right.logicalZ) : left = right := by
  cases left
  cases right
  simp_all

/-- Extensionality for an outer-weighted level-four row. -/
theorem weightedLocalRows_ext {left right : WeightedLocalRows coordinateCount}
    (houter : left.outerNumerator = right.outerNumerator)
    (hrows : left.rows = right.rows) : left = right := by
  cases left
  cases right
  simp_all

/-- Executable version of `LocalRows.IsValid` for the nine-symbol level-four support. -/
def localRowsValid (rows : LocalRows coordinateCount) : Bool :=
  decide (0 < rows.support.length) &&
    (decide (rows.referenceNumerators = List.ofFn rows.referenceNumerator) &&
      (decide (rows.marginalXNumerators =
        List.ofFn (marginalNumerator rows.coordinateX rows.referenceNumerator)) &&
        ((List.ofFn rows.weightX).all (fun value ↦ decide (0 < value)) &&
          ((List.ofFn rows.weightY).all (fun value ↦ decide (0 < value)) &&
            (List.ofFn rows.weightZ).all (fun value ↦ decide (0 < value))))))

/-- Soundness of the bounded Boolean row checker. -/
theorem localRows_isValid_of_valid
    (rows : LocalRows coordinateCount) (hvalid : localRowsValid rows = true) :
    rows.IsValid := by
  unfold localRowsValid at hvalid
  obtain ⟨hsupport, hrest⟩ := Bool.and_eq_true_iff.mp hvalid
  obtain ⟨hreference, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hmarginal, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hweightX, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hweightY, hweightZ⟩ := Bool.and_eq_true_iff.mp hrest
  refine ⟨of_decide_eq_true hsupport, of_decide_eq_true hreference,
    of_decide_eq_true hmarginal, ?_, ?_, ?_⟩
  · intro x
    exact of_decide_eq_true
      ((List.all_eq_true.mp hweightX) _ (List.mem_ofFn.mpr ⟨x, rfl⟩))
  · intro y
    exact of_decide_eq_true
      ((List.all_eq_true.mp hweightY) _ (List.mem_ofFn.mpr ⟨y, rfl⟩))
  · intro z
    exact of_decide_eq_true
      ((List.all_eq_true.mp hweightZ) _ (List.mem_ofFn.mpr ⟨z, rfl⟩))

/-- Check all structural, marginal, and positive-dual conditions on explicit parents. -/
def rowsValidOnParentsFrom (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) : Bool :=
  parents.all fun parent ↦
    localRowsValid
      (localRowsFrom top betaThree order (weights parent) region region parent)

/-- A successful bounded checker supplies validity for every serialized parent in a chunk. -/
theorem localRows_isValid_of_mem (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ)
    (hvalid : rowsValidOnParentsFrom top betaThree order weights region parents = true)
    {parent : ℕ} (hparent : parent ∈ parents) :
    (localRowsFrom top betaThree order (weights parent) region region parent).IsValid := by
  exact localRows_isValid_of_valid _
    ((List.all_eq_true.mp hvalid) parent hparent)

/-- A checked canonical form has exactly the semantic branch value reconstructed from the rows. -/
theorem branchRateOnParentsFrom_eq_eval_of_canonical
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (parents : List ℕ) (branch : Fin 3) (expected : Form)
    (hcanonical :
      Form.canonical (Form.normalizePowersOfTwo
        (branchFormOnParentsFrom top betaThree orders weights region parents branch)) = expected) :
    branchRateOnParentsFrom top betaThree orders weights region parents branch =
      Form.eval 116 expected := by
  have heval := congrArg (Form.eval 116) hcanonical
  rw [Form.eval_canonical, Form.eval_normalizePowersOfTwo,
    branchFormOnParentsFrom_eval] at heval
  exact heval

/-! ## Exact compatibility-target reconstruction

The retained-exponent rows above are entropy summaries.  The hashing theorem needs the stronger
finite statement that those summaries arise from exact complete-split profiles.  The definitions
below reconstruct the profiles directly from the checked top and beta-three tables for one fixed
positive level-four parent.  They use the unnormalized common denominator `2^116`, so no real
division or floating-point data enters this interface.

The only non-definitional fact is `FixedParentSlotBoundaryValid`: on a boundary split, the two
relevant child rows are related by digitwise complementation.  It is deliberately stated per
slot.  Generated clients can check this finite proposition for each selected parent, after which
the theorems in this section derive all universally quantified `CompatibilityTargets` boundary
laws and both target-realization propositions.
-/

/-- Read the physical coordinate carrying one pre-orientation tensor leg. -/
def coordinateForLeg (order : CoordinateOrder) : Leg → Fin 3
  | .X => order.x
  | .Y => order.y
  | .Z => order.z

/-- Big-endian ternary code of a length-four complete-split word. -/
def splitWordDepthTwoCode (word : SplitWord 2) : ℕ :=
  (word ⟨0, by decide⟩ : ℕ) * 27 +
    (word ⟨1, by decide⟩ : ℕ) * 9 +
      (word ⟨2, by decide⟩ : ℕ) * 3 +
        (word ⟨3, by decide⟩ : ℕ)

/-- Exact numerator attached to a length-four word in one padded beta-three row.  The explicit
weight guard prevents an `idxOf` default from assigning mass outside the intended constituent
coordinate. -/
def betaThreeWordNumerator (betaThree : BetaThreeRows)
    (row coordinate total : ℕ) (word : SplitWord 2) : ℕ :=
  if splitWordWeight word = total then
    betaThreeNumeratorFrom betaThree row coordinate
      ((ternarySupportCodes levelThreeWordLength total).idxOf
        (splitWordDepthTwoCode word))
  else 0

/-- Coarse child shape of one fixed parent-local split, in pre-orientation logical coordinates. -/
def fixedParentCoarseIndex (order : CoordinateOrder) (parent slot : ℕ) :
    CoarseIndex FixedParentPart :=
  let left := (pairAt parent slot).1
  { part := PUnit.unit
    x := shapeCoordinate left order.x
    y := shapeCoordinate left order.y
    z := shapeCoordinate left order.z }

/-- One exact child-occurrence profile contribution at denominator `2^116`.  The ordered split
mass includes both left and right occurrences; the second beta-three denominator is inserted
homogeneously through `childRowRescale`. -/
def fixedParentSlotCount (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent slot : ℕ) (leg : Leg)
    (word : SplitWord 2) : ℕ :=
  let physical := coordinateForLeg order leg
  let left := (pairAt parent slot).1
  let childRow := shapeEightIndex left * regionCount + region
  orderedTopSplitNumerator top root region parent slot *
    betaThreeWordNumerator betaThree childRow physical
      (shapeCoordinate left physical) word * childRowRescale

/-- The explicit weight guard makes every slot contribution vanish off its coarse coordinate. -/
theorem fixedParentSlotCount_eq_zero_of_weight_ne
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent slot : ℕ) (leg : Leg)
    (word : SplitWord 2)
    (hweight : splitWordWeight word ≠
      (fixedParentCoarseIndex order parent slot).get leg) :
    fixedParentSlotCount top betaThree order root region parent slot leg word = 0 := by
  cases leg with
  | X =>
      have hw : splitWordWeight word ≠
          shapeCoordinate (pairAt parent slot).1 order.x := by
        simpa [fixedParentCoarseIndex, CoarseIndex.get] using hweight
      simp [fixedParentSlotCount, betaThreeWordNumerator, coordinateForLeg, hw]
  | Y =>
      have hw : splitWordWeight word ≠
          shapeCoordinate (pairAt parent slot).1 order.y := by
        simpa [fixedParentCoarseIndex, CoarseIndex.get] using hweight
      simp [fixedParentSlotCount, betaThreeWordNumerator, coordinateForLeg, hw]
  | Z =>
      have hw : splitWordWeight word ≠
          shapeCoordinate (pairAt parent slot).1 order.z := by
        simpa [fixedParentCoarseIndex, CoarseIndex.get] using hweight
      simp [fixedParentSlotCount, betaThreeWordNumerator, coordinateForLeg, hw]

/-- Exact profile count in one concrete coarse cell. -/
def fixedParentExactCount (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) (leg : Leg)
    (q : CoarseIndex FixedParentPart) (word : SplitWord 2) : ℕ :=
  ((validSlots parent).map fun slot ↦
    if fixedParentCoarseIndex order parent slot = q then
      fixedParentSlotCount top betaThree order root region parent slot leg word
    else 0).sum

/-- A nonzero exact cell count has the split-word weight named by that cell. -/
theorem fixedParentExactCount_supported
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) (leg : Leg)
    (q : CoarseIndex FixedParentPart) (word : SplitWord 2)
    (hcount : fixedParentExactCount top betaThree order root region parent leg q word ≠ 0) :
    splitWordWeight word = q.get leg := by
  by_contra hweight
  apply hcount
  unfold fixedParentExactCount
  apply List.sum_eq_zero
  intro contribution hcontribution
  rw [List.mem_map] at hcontribution
  obtain ⟨slot, hslot, rfl⟩ := hcontribution
  by_cases hq : fixedParentCoarseIndex order parent slot = q
  · rw [if_pos hq]
    have hslotWeight :
        splitWordWeight word ≠
          (fixedParentCoarseIndex order parent slot).get leg := by
      intro hs
      apply hweight
      rw [← hq]
      exact hs
    exact fixedParentSlotCount_eq_zero_of_weight_ne
      top betaThree order root region parent slot leg word hslotWeight
  · simp [hq]

/-- Finite complement check required of one selected level-four parent.  This is the exact
certificate-facing boundary: all quantified types (`Fin pairSlotCount` and `SplitWord 2`) are
finite, while membership excludes padded pair slots. -/
def FixedParentSlotBoundaryValid (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : Prop :=
  ∀ slot : Fin pairSlotCount, slot.val ∈ validSlots parent →
    ∀ word : SplitWord 2,
      ((fixedParentCoarseIndex order parent slot).z = 0 →
        fixedParentSlotCount top betaThree order root region parent slot .Y word =
          fixedParentSlotCount top betaThree order root region parent slot .X
            (AlgebraicComplexity.complementSplitWord word)) ∧
      ((fixedParentCoarseIndex order parent slot).y = 0 →
        fixedParentSlotCount top betaThree order root region parent slot .Z word =
          fixedParentSlotCount top betaThree order root region parent slot .X
            (AlgebraicComplexity.complementSplitWord word)) ∧
      ((fixedParentCoarseIndex order parent slot).x = 0 →
        fixedParentSlotCount top betaThree order root region parent slot .Z word =
          fixedParentSlotCount top betaThree order root region parent slot .Y
            (AlgebraicComplexity.complementSplitWord word))

/-- A depth-two split word assembled from its four digits. -/
def splitWordDepthTwoOfDigits (a b c d : SplitDigit) : SplitWord 2 :=
  ![a, b, c, d]

/-- Executable bounded checker for `FixedParentSlotBoundaryValid`.  The four nested digit loops
are a computable enumeration of `SplitWord 2`; unlike `Finset.univ.toList`, they introduce no
noncomputable ordering choice. -/
def fixedParentSlotBoundaryValid (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) : Bool :=
  (List.ofFn (fun slot : Fin pairSlotCount ↦ slot)).all fun slot ↦
    if slot.val ∈ validSlots parent then
      (List.ofFn (fun a : SplitDigit ↦ a)).all fun a ↦
      (List.ofFn (fun b : SplitDigit ↦ b)).all fun b ↦
      (List.ofFn (fun c : SplitDigit ↦ c)).all fun c ↦
      (List.ofFn (fun d : SplitDigit ↦ d)).all fun d ↦
        let word := splitWordDepthTwoOfDigits a b c d
        decide
            (((fixedParentCoarseIndex order parent slot).z = 0 →
                fixedParentSlotCount top betaThree order root region parent slot .Y word =
                  fixedParentSlotCount top betaThree order root region parent slot .X
                    (AlgebraicComplexity.complementSplitWord word)) ∧
              ((fixedParentCoarseIndex order parent slot).y = 0 →
                fixedParentSlotCount top betaThree order root region parent slot .Z word =
                  fixedParentSlotCount top betaThree order root region parent slot .X
                    (AlgebraicComplexity.complementSplitWord word)) ∧
              ((fixedParentCoarseIndex order parent slot).x = 0 →
                fixedParentSlotCount top betaThree order root region parent slot .Z word =
                  fixedParentSlotCount top betaThree order root region parent slot .Y
                    (AlgebraicComplexity.complementSplitWord word)))
    else true

/-- Soundness of the bounded complement checker. -/
theorem fixedParentSlotBoundaryValid_sound
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : fixedParentSlotBoundaryValid top betaThree order root region parent = true) :
    FixedParentSlotBoundaryValid top betaThree order root region parent := by
  intro slot hslot word
  have hslotChecked := (List.all_eq_true.mp hvalid) slot
    (List.mem_ofFn.mpr ⟨slot, rfl⟩)
  rw [if_pos hslot] at hslotChecked
  let a : SplitDigit := word ⟨0, by decide⟩
  let b : SplitDigit := word ⟨1, by decide⟩
  let c : SplitDigit := word ⟨2, by decide⟩
  let d : SplitDigit := word ⟨3, by decide⟩
  have ha := (List.all_eq_true.mp hslotChecked) a (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hb := (List.all_eq_true.mp ha) b (List.mem_ofFn.mpr ⟨b, rfl⟩)
  have hc := (List.all_eq_true.mp hb) c (List.mem_ofFn.mpr ⟨c, rfl⟩)
  have hd := (List.all_eq_true.mp hc) d (List.mem_ofFn.mpr ⟨d, rfl⟩)
  have hword : splitWordDepthTwoOfDigits a b c d = word := by
    funext position
    fin_cases position <;> rfl
  simpa [hword] using (of_decide_eq_true hd)

private theorem validSlot_lt_pairSlotCount {parent slot : ℕ}
    (hslot : slot ∈ validSlots parent) : slot < pairSlotCount := by
  unfold validSlots at hslot
  exact List.mem_range.mp (List.mem_filter.mp hslot).1

/-- Slotwise complement validity implies the universal logical-Y boundary law. -/
theorem fixedParentExactCount_yBoundary
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent)
    (q : CoarseIndex FixedParentPart) (hz : q.z = 0) (word : SplitWord 2) :
    fixedParentExactCount top betaThree order root region parent .Y q word =
      fixedParentExactCount top betaThree order root region parent .X q
        (AlgebraicComplexity.complementSplitWord word) := by
  unfold fixedParentExactCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro slot hslot
  by_cases hq : fixedParentCoarseIndex order parent slot = q
  · simp only [hq, ↓reduceIte]
    have hzslot : (fixedParentCoarseIndex order parent slot).z = 0 := by
      rw [hq]
      exact hz
    exact (hvalid ⟨slot, validSlot_lt_pairSlotCount hslot⟩ hslot word).1 hzslot
  · simp [hq]

/-- Slotwise complement validity implies the `Y=0` logical-Z boundary law. -/
theorem fixedParentExactCount_zBoundaryOfX
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent)
    (q : CoarseIndex FixedParentPart) (hy : q.y = 0) (word : SplitWord 2) :
    fixedParentExactCount top betaThree order root region parent .Z q word =
      fixedParentExactCount top betaThree order root region parent .X q
        (AlgebraicComplexity.complementSplitWord word) := by
  unfold fixedParentExactCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro slot hslot
  by_cases hq : fixedParentCoarseIndex order parent slot = q
  · simp only [hq, ↓reduceIte]
    have hyslot : (fixedParentCoarseIndex order parent slot).y = 0 := by
      rw [hq]
      exact hy
    exact (hvalid ⟨slot, validSlot_lt_pairSlotCount hslot⟩ hslot word).2.1 hyslot
  · simp [hq]

/-- Slotwise complement validity implies the `X=0` logical-Z boundary law. -/
theorem fixedParentExactCount_zBoundaryOfY
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent)
    (q : CoarseIndex FixedParentPart) (hx : q.x = 0) (word : SplitWord 2) :
    fixedParentExactCount top betaThree order root region parent .Z q word =
      fixedParentExactCount top betaThree order root region parent .Y q
        (AlgebraicComplexity.complementSplitWord word) := by
  unfold fixedParentExactCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro slot hslot
  by_cases hq : fixedParentCoarseIndex order parent slot = q
  · simp only [hq, ↓reduceIte]
    have hxslot : (fixedParentCoarseIndex order parent slot).x = 0 := by
      rw [hq]
      exact hx
    exact (hvalid ⟨slot, validSlot_lt_pairSlotCount hslot⟩ hslot word).2.2 hxslot
  · simp [hq]

/-- Positive logical-Y compatibility-cell count, pooled by the logical-Y child coordinate. -/
def fixedParentYPooledCount (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent total : ℕ)
    (word : SplitWord 2) : ℕ :=
  ((validSlots parent).map fun slot ↦
    let q := fixedParentCoarseIndex order parent slot
    if q.z ≠ 0 ∧ q.y = total then
      fixedParentSlotCount top betaThree order root region parent slot .Y word
    else 0).sum

/-- Positive logical-Z compatibility-cell count, pooled by the logical-Z child coordinate. -/
def fixedParentZPooledCount (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent total : ℕ)
    (word : SplitWord 2) : ℕ :=
  ((validSlots parent).map fun slot ↦
    let q := fixedParentCoarseIndex order parent slot
    if q.x ≠ 0 ∧ q.y ≠ 0 ∧ q.z = total then
      fixedParentSlotCount top betaThree order root region parent slot .Z word
    else 0).sum

/-- Pooled logical-Y counts remain supported on the pooled coordinate. -/
theorem fixedParentYPooledCount_supported
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent total : ℕ) (word : SplitWord 2)
    (hcount : fixedParentYPooledCount top betaThree order root region parent total word ≠ 0) :
    splitWordWeight word = total := by
  by_contra hweight
  apply hcount
  unfold fixedParentYPooledCount
  apply List.sum_eq_zero
  intro contribution hcontribution
  rw [List.mem_map] at hcontribution
  obtain ⟨slot, hslot, rfl⟩ := hcontribution
  dsimp only
  let q := fixedParentCoarseIndex order parent slot
  change (if q.z ≠ 0 ∧ q.y = total then
      fixedParentSlotCount top betaThree order root region parent slot .Y word else 0) = 0
  by_cases hcell : q.z ≠ 0 ∧ q.y = total
  · rw [if_pos hcell]
    have hslotWeight : splitWordWeight word ≠ q.get .Y := by
      simpa [CoarseIndex.get, hcell.2] using hweight
    exact fixedParentSlotCount_eq_zero_of_weight_ne
      top betaThree order root region parent slot .Y word hslotWeight
  · rw [if_neg hcell]

/-- Pooled logical-Z counts remain supported on the pooled coordinate. -/
theorem fixedParentZPooledCount_supported
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent total : ℕ) (word : SplitWord 2)
    (hcount : fixedParentZPooledCount top betaThree order root region parent total word ≠ 0) :
    splitWordWeight word = total := by
  by_contra hweight
  apply hcount
  unfold fixedParentZPooledCount
  apply List.sum_eq_zero
  intro contribution hcontribution
  rw [List.mem_map] at hcontribution
  obtain ⟨slot, hslot, rfl⟩ := hcontribution
  dsimp only
  let q := fixedParentCoarseIndex order parent slot
  change (if q.x ≠ 0 ∧ q.y ≠ 0 ∧ q.z = total then
      fixedParentSlotCount top betaThree order root region parent slot .Z word else 0) = 0
  by_cases hcell : q.x ≠ 0 ∧ q.y ≠ 0 ∧ q.z = total
  · rw [if_pos hcell]
    have hslotWeight : splitWordWeight word ≠ q.get .Z := by
      simpa [CoarseIndex.get, hcell.2.2] using hweight
    exact fixedParentSlotCount_eq_zero_of_weight_ne
      top betaThree order root region parent slot .Z word hslotWeight
  · rw [if_neg hcell]

/-- Compatibility targets reconstructed from the exact checked child rows of one parent. -/
def fixedParentCompatibilityTargets (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent) :
    CompatibilityTargets FixedParentPart 2 where
  xExact := fixedParentExactCount top betaThree order root region parent .X
  yExact := fixedParentExactCount top betaThree order root region parent .Y
  zExact := fixedParentExactCount top betaThree order root region parent .Z
  yPooled _ := fixedParentYPooledCount top betaThree order root region parent
  zPooled _ := fixedParentZPooledCount top betaThree order root region parent
  yBoundary := fixedParentExactCount_yBoundary top betaThree order root region parent hvalid
  zBoundaryOfX := fixedParentExactCount_zBoundaryOfX top betaThree order root region parent hvalid
  zBoundaryOfY := fixedParentExactCount_zBoundaryOfY top betaThree order root region parent hvalid

/-- Exact complete-split profiles reconstructed from all individual coarse cells. -/
noncomputable def fixedParentExactCompatibilityProfiles
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ) :
    ExactCompatibilityProfileFamily FixedParentPart 2 where
  samples leg q := ∑ word,
    fixedParentExactCount top betaThree order root region parent leg q word
  profile leg q := CompleteSplitProfile.ofCounts
    (fixedParentExactCount top betaThree order root region parent leg q)
    rfl (fixedParentExactCount_supported top betaThree order root region parent leg q)

/-- The reconstructed exact profiles realize all three exact target tables. -/
theorem fixedParentExactCompatibilityProfiles_realizesTargets
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent) :
    (fixedParentExactCompatibilityProfiles top betaThree order root region parent).RealizesTargets
      (fixedParentCompatibilityTargets top betaThree order root region parent hvalid) := by
  constructor
  · intro q word
    rfl
  constructor <;> intro q word <;> rfl

private theorem fixedParentYBoundaryAggregate_supported
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent total : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent)
    (word : SplitWord 2)
    (hcount :
      CompatibilityTargets.yBoundaryAggregate
        (fixedParentCompatibilityTargets top betaThree order root region parent hvalid)
        PUnit.unit total word ≠ 0) :
    splitWordWeight word = total := by
  simpa [yBoundaryIndex, CoarseIndex.get] using
    (fixedParentExactCount_supported top betaThree order root region parent .Y
      (yBoundaryIndex 2 PUnit.unit total) word hcount)

private theorem fixedParentZBoundaryAggregate_supported
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent total : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent)
    (word : SplitWord 2)
    (hcount :
      CompatibilityTargets.zBoundaryAggregate
        (fixedParentCompatibilityTargets top betaThree order root region parent hvalid)
        PUnit.unit total word ≠ 0) :
    splitWordWeight word = total := by
  let targets := fixedParentCompatibilityTargets top betaThree order root region parent hvalid
  by_contra hweight
  have hfirst : targets.zExact (zXBoundaryIndex 2 PUnit.unit total) word = 0 := by
    by_contra hnonzero
    apply hweight
    simpa [zXBoundaryIndex, CoarseIndex.get] using
      (fixedParentExactCount_supported top betaThree order root region parent .Z
        (zXBoundaryIndex 2 PUnit.unit total) word hnonzero)
  have hsecond : targets.zExact (zYBoundaryIndex 2 PUnit.unit total) word = 0 := by
    by_contra hnonzero
    apply hweight
    simpa [zYBoundaryIndex, CoarseIndex.get] using
      (fixedParentExactCount_supported top betaThree order root region parent .Z
        (zYBoundaryIndex 2 PUnit.unit total) word hnonzero)
  apply hcount
  simp [CompatibilityTargets.zBoundaryAggregate, targets, hfirst, hsecond]

/-- A count table with its sample size chosen to be the exact sum. -/
noncomputable def completeSplitProfileOfSupportedCounts (total : ℕ)
    (counts : SplitWord 2 → ℕ)
    (hsupported : ∀ word, counts word ≠ 0 → splitWordWeight word = total) :
    CompleteSplitProfile 2 total (∑ word, counts word) :=
  CompleteSplitProfile.ofCounts counts rfl hsupported

/-- Canonical boundary-plus-positive pooled tables reconstructed from one fixed parent. -/
noncomputable def fixedParentExactSplitAvgFamily
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent) :
    ExactSplitAvgFamily FixedParentPart 2 :=
  let targets := fixedParentCompatibilityTargets top betaThree order root region parent hvalid
  { y := fun _ total ↦ ExactSplitAvgTable.canonical
      (completeSplitProfileOfSupportedCounts total
        (targets.yBoundaryAggregate PUnit.unit total)
        (fixedParentYBoundaryAggregate_supported top betaThree order root region parent total
          hvalid))
      (completeSplitProfileOfSupportedCounts total
        (targets.yPooled PUnit.unit total)
        (fixedParentYPooledCount_supported top betaThree order root region parent total))
    z := fun _ total ↦ ExactSplitAvgTable.canonical
      (completeSplitProfileOfSupportedCounts total
        (targets.zBoundaryAggregate PUnit.unit total)
        (fixedParentZBoundaryAggregate_supported top betaThree order root region parent total
          hvalid))
      (completeSplitProfileOfSupportedCounts total
        (targets.zPooled PUnit.unit total)
        (fixedParentZPooledCount_supported top betaThree order root region parent total)) }

/-- The canonical pooled tables realize the exact boundary and positive-cell targets. -/
theorem fixedParentExactSplitAvgFamily_realizesTargets
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (root region parent : ℕ)
    (hvalid : FixedParentSlotBoundaryValid top betaThree order root region parent) :
    (fixedParentExactSplitAvgFamily top betaThree order root region parent hvalid).RealizesTargets
      (fixedParentCompatibilityTargets top betaThree order root region parent hvalid) := by
  constructor
  · intro part total word
    cases part
    constructor
    · rfl
    · change
        (completeSplitProfileOfSupportedCounts total
          (CompatibilityTargets.yPooled
            (fixedParentCompatibilityTargets top betaThree order root region parent hvalid)
            PUnit.unit total) _).counts word = _
      rfl
  · intro part total word
    cases part
    constructor
    · rfl
    · change
        (completeSplitProfileOfSupportedCounts total
          (CompatibilityTargets.zPooled
            (fixedParentCompatibilityTargets top betaThree order root region parent hvalid)
            PUnit.unit total) _).counts word = _
      rfl

end MatrixMultiplication.SimplifiedExponentLevelFourValidity
