/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence

/-!
# Exact level-three retained-exponent recurrence

This module turns the reconstructed complete-split rows into the three local constituent rates
used at level three.  It is data-parametric only in the cached top-to-level-three occurrence
masses and the positive integer dual factors; every probability numerator is read from the exact
primary tables.

For a positive `(node, region)` row:

* the outer occurrence mass is `mass3 * A_3` at denominator `2^(20+12)`;
* logical `X` uses the ordered split law `alpha_3` and its integer product-family dual;
* logical `Y` charges `k=0` rows separately and pools the rest by `j`;
* logical `Z` charges `i=0` or `j=0` rows separately and pools the rest by `k`.

Child rows have denominator `2^12`.  Multiplying by the ordered occurrence weight and rescaling
by another `2^12` places every compatibility row at the parent's exact `2^36` denominator.

Every quotient-dependent constructor has a `For` form taking the quotient slot map explicitly.
The historical names remain sorted-pair specializations, so existing clients retain their exact
statements while new certificate families cannot silently inherit the wrong pushforward.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

def outerBits : ℕ := 20 + 12
def referenceBits : ℕ := 12
def compatibilityExtraBits : ℕ := 24
def coordinateCount : ℕ := 5
def nodeCount : ℕ := 126
def regionCount : ℕ := 6
def splitSlotCount : ℕ := 10
def childRowRescale : ℕ := 2 ^ 12

/-- Physical coordinates assigned to the three logical tensor roles in one region.

A concrete certificate separately proves that `x`, `y`, and `z` are distinct.  Keeping the
executable order proof-free is useful for generated reduction, and—crucially—the regional family
may repeat the same order any number of times. -/
structure CoordinateOrder where
  x : Fin 3
  y : Fin 3
  z : Fin 3
  deriving DecidableEq, Repr

/-- The three physical coordinates in an order are pairwise distinct. -/
def CoordinateOrder.IsPermutation (order : CoordinateOrder) : Prop :=
  order.x ≠ order.y ∧ order.x ≠ order.z ∧ order.y ≠ order.z

/-- Positive integer factors for one maximum-entropy dual. -/
structure DualWeights where
  x : Fin coordinateCount → ℕ
  y : Fin coordinateCount → ℕ
  z : Fin coordinateCount → ℕ

namespace DualWeights

/-- Select the factor row belonging to one physical coordinate. -/
def forCoordinate (weights : DualWeights) (coordinate : Fin 3) :
    Fin coordinateCount → ℕ :=
  if coordinate = 0 then weights.x else if coordinate = 1 then weights.y else weights.z

end DualWeights

/-- Certificate-order valid split slots of one positive level-three node. -/
def validSlots (node : ℕ) : List ℕ :=
  (List.range splitSlotCount).filter (splitSlotIsValid node)

/-- The split support as finite coordinate triples.  Valid total-four shapes have every
coordinate below five, so `% coordinateCount` is extensionally the identity on this list while
keeping the executable constructor proof-free. -/
def splitSupport (order : CoordinateOrder) (node : ℕ) :
    List (CoordinateTriple coordinateCount) :=
  (validSlots node).map fun slot ↦
    let shape := splitShapeAt node slot
    { x := ⟨shapeCoordinate shape order.x % coordinateCount, Nat.mod_lt _ (by decide)⟩
      y := ⟨shapeCoordinate shape order.y % coordinateCount, Nat.mod_lt _ (by decide)⟩
      z := ⟨shapeCoordinate shape order.z % coordinateCount, Nat.mod_lt _ (by decide)⟩ }

/-- Ordered split-law numerator list at denominator `2^12`. -/
def referenceNumerators (data : PrimaryTables) (node region : ℕ) : List ℕ :=
  (validSlots node).map fun slot ↦
    dyadicNumeratorAt data.pos3Alpha (node * regionCount + region) slot

/-- Exact logical-X marginal of the ordered split law. -/
def marginalXNumerators (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List ℕ :=
  (List.range coordinateCount).map fun value ↦
    ((validSlots node).map fun slot ↦
      if shapeCoordinate (splitShapeAt node slot) order.x = value then
        dyadicNumeratorAt data.pos3Alpha (node * regionCount + region) slot
      else 0).sum

/-- Quotient-pushed child row weighted by `alpha(u)+alpha(parent-u)` at denominator `2^36`. -/
def weightedChildRowFor (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node region slot coordinate : ℕ) : List ℕ :=
  (List.range levelTwoSupportWidth).map fun symbol ↦
    orderedSplitNumerator data node region slot *
      quotientBetaTwoNumerator supportSlot data node region slot coordinate symbol *
        childRowRescale

/-- Sorted-pair specialization of the weighted child row. -/
def weightedChildRow (data : PrimaryTables) (node region slot coordinate : ℕ) : List ℕ :=
  weightedChildRowFor sortedPairSupportSlot data node region slot coordinate

/-- Whether a split belongs to the individually charged logical-`Y` boundary cell. -/
def yFirstSlot (order : CoordinateOrder) (node slot : ℕ) : Bool :=
  decide (shapeCoordinate (splitShapeAt node slot) order.z = 0)

/-- Whether a split belongs to an individually charged logical-`Z` boundary cell. -/
def zFirstSlot (order : CoordinateOrder) (node slot : ℕ) : Bool :=
  decide (shapeCoordinate (splitShapeAt node slot) order.x = 0 ∨
    shapeCoordinate (splitShapeAt node slot) order.y = 0)

/-- Individually charged logical-Y boundary rows (`k=0`) for a supplied quotient. -/
def yFirstRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  ((validSlots node).filter (yFirstSlot order node)).map fun slot ↦
    weightedChildRowFor supportSlot data node region slot order.y

/-- Sorted-pair specialization of the logical-Y boundary rows. -/
def yFirstRows (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  yFirstRowsFor sortedPairSupportSlot data order node region

/-- Individually charged logical-Z boundary rows for a supplied quotient. -/
def zFirstRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  ((validSlots node).filter (zFirstSlot order node)).map fun slot ↦
    weightedChildRowFor supportSlot data node region slot order.z

/-- Sorted-pair specialization of the logical-Z boundary rows. -/
def zFirstRows (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  zFirstRowsFor sortedPairSupportSlot data order node region

/-- Pool non-boundary quotient rows satisfying a fixed split-coordinate value. -/
def pooledChildRowFor (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (node region childCoordinate groupCoordinate group : ℕ)
    (first : ℕ → Bool) : List ℕ :=
  (List.range levelTwoSupportWidth).map fun symbol ↦
    ((validSlots node).map fun slot ↦
      if first slot = false ∧
          shapeCoordinate (splitShapeAt node slot) groupCoordinate = group then
        orderedSplitNumerator data node region slot *
          quotientBetaTwoNumerator supportSlot data node region slot childCoordinate symbol *
            childRowRescale
      else 0).sum

/-- Sorted-pair specialization of one pooled child row. -/
def pooledChildRow (data : PrimaryTables)
    (node region childCoordinate groupCoordinate group : ℕ)
    (first : ℕ → Bool) : List ℕ :=
  pooledChildRowFor sortedPairSupportSlot data
    node region childCoordinate groupCoordinate group first

/-- Logical-Y compatibility cells for a supplied quotient, pooled by `j`. -/
def yGroupRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  (List.range coordinateCount).map fun group ↦
    pooledChildRowFor supportSlot data
      node region order.y order.y group (yFirstSlot order node)

/-- Sorted-pair specialization of logical-Y compatibility cells. -/
def yGroupRows (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  yGroupRowsFor sortedPairSupportSlot data order node region

/-- Logical-Z compatibility cells for a supplied quotient, pooled by `k`. -/
def zGroupRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  (List.range coordinateCount).map fun group ↦
    pooledChildRowFor supportSlot data
      node region order.z order.z group (zFirstSlot order node)

/-- Sorted-pair specialization of logical-Z compatibility cells. -/
def zGroupRows (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : List (List ℕ) :=
  zGroupRowsFor sortedPairSupportSlot data order node region

/-- Parent, boundary, and pooled logical-Y rows for a supplied quotient. -/
def logicalYRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : CompatibilityRows :=
  { pooled := quotientBetaThreeRegionRow supportSlot data node region order.y
    first := yFirstRowsFor supportSlot data order node region
    groups := yGroupRowsFor supportSlot data order node region }

/-- Sorted-pair specialization of the complete logical-Y rows. -/
def logicalYRows (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : CompatibilityRows :=
  logicalYRowsFor sortedPairSupportSlot data order node region

/-- Parent, boundary, and pooled logical-Z rows for a supplied quotient. -/
def logicalZRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : CompatibilityRows :=
  { pooled := quotientBetaThreeRegionRow supportSlot data node region order.z
    first := zFirstRowsFor supportSlot data order node region
    groups := zGroupRowsFor supportSlot data order node region }

/-- Sorted-pair specialization of the complete logical-Z rows. -/
def logicalZRows (data : PrimaryTables) (order : CoordinateOrder)
    (node region : ℕ) : CompatibilityRows :=
  logicalZRowsFor sortedPairSupportSlot data order node region

/-- Exact local rows for one positive node/region under a supplied quotient. -/
def localRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (weights : DualWeights) (node region : ℕ) :
    LocalRows coordinateCount :=
  { support := splitSupport order node
    referenceNumerators := referenceNumerators data node region
    marginalXNumerators := marginalXNumerators data order node region
    weightX := weights.forCoordinate order.x
    weightY := weights.forCoordinate order.y
    weightZ := weights.forCoordinate order.z
    logicalY := logicalYRowsFor supportSlot data order node region
    logicalZ := logicalZRowsFor supportSlot data order node region }

/-- Sorted-pair specialization of one local level-three row family. -/
def localRows (data : PrimaryTables) (order : CoordinateOrder)
    (weights : DualWeights) (node region : ℕ) :
    LocalRows coordinateCount :=
  localRowsFor sortedPairSupportSlot data order weights node region

/-- Exact outer occurrence numerator at denominator `2^32`. -/
def outerNumerator (data : PrimaryTables) (massThree : Array ℕ) (node region : ℕ) : ℕ :=
  (massThree[positiveNodeGlobalRow node]?.getD 0) *
    dyadicNumeratorAt data.pos3A node region

/-- One quotient-parametric local row family with its exact outer occurrence numerator. -/
def weightedLocalRowsFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ) :
    WeightedLocalRows coordinateCount :=
  { outerNumerator := outerNumerator data massThree node region
    rows := localRowsFor supportSlot data order weights node region }

/-- Sorted-pair specialization of a weighted local row family. -/
def weightedLocalRows (data : PrimaryTables) (massThree : Array ℕ)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ) :
    WeightedLocalRows coordinateCount :=
  weightedLocalRowsFor sortedPairSupportSlot data massThree order weights node region

/-- Active node list for one output region.  Omitting zero outer masses keeps generated form
normalization proportional to the actual certificate support. -/
def activeNodes (data : PrimaryTables) (massThree : Array ℕ) (region : ℕ) : List ℕ :=
  (List.range nodeCount).filter fun node ↦
    decide (0 < outerNumerator data massThree node region)

/-- Quotient-parametric weighted entries at every positive-mass node of one region. -/
def regionEntriesFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ) :
    List (WeightedLocalRows coordinateCount) :=
  (activeNodes data massThree region).map fun node ↦
    weightedLocalRowsFor supportSlot data massThree (orders region) (weights node) node region

/-- Sorted-pair specialization of the weighted regional entries. -/
def regionEntries (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ) :
    List (WeightedLocalRows coordinateCount) :=
  regionEntriesFor sortedPairSupportSlot data massThree orders weights region

/-- The same quotient-parametric entries over an explicit generated node list. -/
def regionEntriesOnNodesFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ) :
    List (WeightedLocalRows coordinateCount) :=
  nodes.map fun node ↦
    weightedLocalRowsFor supportSlot data massThree (orders region) (weights node) node region

/-- Sorted-pair specialization of the explicit-node regional entries. -/
def regionEntriesOnNodes (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ) :
    List (WeightedLocalRows coordinateCount) :=
  regionEntriesOnNodesFor sortedPairSupportSlot data massThree orders weights region nodes

/-- Quotient-parametric regional entries equal the explicit construction on active nodes. -/
theorem regionEntriesFor_eq_onNodes (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ) :
    regionEntriesFor supportSlot data massThree orders weights region =
      regionEntriesOnNodesFor supportSlot data massThree orders weights region
        (activeNodes data massThree region) := by
  rfl

/-- The region entries are the explicit-node construction on the computed active-node list. -/
theorem regionEntries_eq_onNodes (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ) :
    regionEntries data massThree orders weights region =
      regionEntriesOnNodes data massThree orders weights region
        (activeNodes data massThree region) := by
  rfl

/-- Semantic branch rate for a quotient over an explicit node subfamily. -/
noncomputable def branchRateOnNodesFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (branch : Fin 3) : ℝ :=
  weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
    (regionEntriesOnNodesFor supportSlot data massThree orders weights region nodes) branch

/-- Sorted-pair specialization of the explicit-node branch rate. -/
noncomputable def branchRateOnNodes (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (branch : Fin 3) : ℝ :=
  branchRateOnNodesFor sortedPairSupportSlot
    data massThree orders weights region nodes branch

/-- Exact quotient-parametric branch form over an explicit node subfamily. -/
def branchFormOnNodesFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (branch : Fin 3) :=
  weightedFamilyBranchForm referenceBits compatibilityExtraBits
    (regionEntriesOnNodesFor supportSlot data massThree orders weights region nodes) branch

/-- Sorted-pair specialization of the explicit-node exact branch form. -/
def branchFormOnNodes (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (branch : Fin 3) :=
  branchFormOnNodesFor sortedPairSupportSlot
    data massThree orders weights region nodes branch

/-- A quotient-parametric exact branch form evaluates to its semantic branch sum. -/
theorem branchFormOnNodesFor_eval (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (branch : Fin 3) :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval
        ((referenceBits + compatibilityExtraBits) + outerBits)
        (branchFormOnNodesFor supportSlot data massThree orders weights region nodes branch) =
      branchRateOnNodesFor supportSlot data massThree orders weights region nodes branch := by
  exact weightedFamilyBranchForm_eval outerBits referenceBits compatibilityExtraBits
    (regionEntriesOnNodesFor supportSlot data massThree orders weights region nodes) branch

/-- The explicit-node exact form evaluates to the corresponding semantic branch sum. -/
theorem branchFormOnNodes_eval (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (branch : Fin 3) :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval
        ((referenceBits + compatibilityExtraBits) + outerBits)
    (branchFormOnNodes data massThree orders weights region nodes branch) =
      branchRateOnNodes data massThree orders weights region nodes branch := by
  exact branchFormOnNodesFor_eval sortedPairSupportSlot
    data massThree orders weights region nodes branch

/-- Explicit node chunks add to the quotient-parametric rate of their flattened family. -/
theorem branchRateOnNodesFor_flatten (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (chunks : List (List ℕ))
    (branch : Fin 3) :
    branchRateOnNodesFor supportSlot data massThree orders weights region chunks.flatten branch =
      (chunks.map fun nodes ↦
        branchRateOnNodesFor supportSlot data massThree orders weights region nodes branch).sum := by
  unfold branchRateOnNodesFor regionEntriesOnNodesFor
  induction chunks with
  | nil => rfl
  | cons nodes chunks ih =>
      simp only [List.flatten_cons, List.map_append, List.map_cons, List.sum_cons]
      rw [weightedFamilyBranchRate_append, ih]

/-- Sorted-pair explicit node chunks add exactly to their flattened-family rate. -/
theorem branchRateOnNodes_flatten (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (chunks : List (List ℕ))
    (branch : Fin 3) :
    branchRateOnNodes data massThree orders weights region chunks.flatten branch =
      (chunks.map fun nodes ↦
        branchRateOnNodes data massThree orders weights region nodes branch).sum :=
  branchRateOnNodesFor_flatten sortedPairSupportSlot
    data massThree orders weights region chunks branch

/-- Semantic three-branch rate of one quotient-parametric level-three region. -/
noncomputable def regionBranchRateFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) : ℝ :=
  weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
    (regionEntriesFor supportSlot data massThree orders weights region) branch

/-- Sorted-pair specialization of one region's semantic branch rate. -/
noncomputable def regionBranchRate (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) : ℝ :=
  regionBranchRateFor sortedPairSupportSlot data massThree orders weights region branch

/-- A quotient-parametric regional branch equals its explicit active-node branch. -/
theorem regionBranchRateFor_eq_onNodes (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :
    regionBranchRateFor supportSlot data massThree orders weights region branch =
      branchRateOnNodesFor supportSlot data massThree orders weights region
        (activeNodes data massThree region) branch := by
  rfl

/-- A regional branch is the explicit-node branch over its computed active-node list. -/
theorem regionBranchRate_eq_onNodes (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :
    regionBranchRate data massThree orders weights region branch =
      branchRateOnNodes data massThree orders weights region
        (activeNodes data massThree region) branch := by
  rfl

/-- Exact quotient-parametric common-denominator form for one regional branch. -/
def regionBranchFormFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :=
  weightedFamilyBranchForm referenceBits compatibilityExtraBits
    (regionEntriesFor supportSlot data massThree orders weights region) branch

/-- Sorted-pair specialization of one region's exact signed-log form. -/
def regionBranchForm (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :=
  regionBranchFormFor sortedPairSupportSlot data massThree orders weights region branch

/-- A quotient-parametric regional form evaluates to its semantic regional rate. -/
theorem regionBranchFormFor_eval (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval
        ((referenceBits + compatibilityExtraBits) + outerBits)
        (regionBranchFormFor supportSlot data massThree orders weights region branch) =
      regionBranchRateFor supportSlot data massThree orders weights region branch := by
  exact weightedFamilyBranchForm_eval outerBits referenceBits compatibilityExtraBits
    (regionEntriesFor supportSlot data massThree orders weights region) branch

/-- The exact regional form evaluates to the complete semantic regional branch rate. -/
theorem regionBranchForm_eval (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (branch : Fin 3) :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval
        ((referenceBits + compatibilityExtraBits) + outerBits)
    (regionBranchForm data massThree orders weights region branch) =
      regionBranchRate data massThree orders weights region branch := by
  exact regionBranchFormFor_eval sortedPairSupportSlot
    data massThree orders weights region branch

end MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
