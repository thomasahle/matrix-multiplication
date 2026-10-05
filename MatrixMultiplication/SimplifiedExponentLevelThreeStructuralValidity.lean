/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentLevelThreeCheckpoints

set_option autoImplicit false

/-!
# Structural validity of every level-three constituent row

`LocalRows.IsValid` asks for a nonempty support, two list identities identifying the stored joint
and logical-`X` marginal rows with the serialized support, and positivity of the three integer
dual factor rows.  It never inspects `logicalY`, `logicalZ`, or the quotient slot map, so for the
level-three family it is *not* a property of the certificate's numbers at all: it is a property of
the finite split geometry plus positivity of the supplied dual weights.

This module proves that.  The reusable endpoints are

* `localRowsFor_isValid_of_node_lt` — one local row is valid as soon as its node index is below
  `nodeCount` and its dual weights are coordinatewise positive, and
* `regionEntriesFor_isValid_of_weights_pos` — every entry of a region is valid as soon as the
  per-node dual weight family is positive, with no hypothesis on the node list whatsoever.

Both are quotient-parametric: `supportSlot` occurs in the statement only through the
`logicalY`/`logicalZ` fields that `IsValid` ignores, so a single proof serves the sorted-pair and
total-weight quotients alike.  Sorted-pair specializations and the outer-weighted
`WeightedLocalRows` shapes are supplied so that a client consuming a per-node `entry_isValid`
snapshot or a regional `regionEntries_valid` reduction changes no statement.

The finite bridge set proved on the way is small and independently reusable:

* `lt_nodeCount_of_mem_activeNodes` — an active node is a genuine node index;
* `levelThreeSplits_length_pos` — a positive total-eight parent really does split;
* `shapeCoordinate_le_total` — the public coordinate ≤ total bound;
* `splitShapeAt_total` — a raw valid slot reconstructs a total-four shape;
* `dualWeights_forCoordinate_pos` — the aggregate positivity of a role-selected factor row.

Only the finite shape geometry of `LevelFourShapeGeometry` and the checkpoint-level structural
lemma `localRowsFor_isValid_of_nonempty_validSlots` are used.  No primary table, occurrence mass,
dyadic numerator, canonical form, or generated payload enters any statement or proof below.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelThreeStructuralValidity

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelThreeCheckpoints
open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-! ## The finite bridge set -/

/-- **(a)** An active node of any region is a genuine level-three node index.

The active-node list is a filter of `List.range nodeCount`, so the bound is structural and holds
whatever the occurrence masses are.

Proof sketch: unfold the filtered range and take the range component of `List.mem_filter`. -/
theorem lt_nodeCount_of_mem_activeNodes {data : PrimaryTables} {massThree : Array ℕ}
    {region node : ℕ} (hnode : node ∈ activeNodes data massThree region) :
    node < nodeCount := by
  unfold activeNodes at hnode
  exact List.mem_range.mp (List.mem_filter.mp hnode).1

/-- **(b)** Every positive total-eight parent shape has at least one level-three split.

Proof sketch: `positiveShapes_eight_eq` reduces membership to twenty-one literal parents, and each
`levelThreeSplits` list is a filter of the fifteen-element `shapes 4` enumeration, so its length is
kernel-computable.  This is the same finite idiom used by `levelThreeSplits_length_le_ten`. -/
theorem levelThreeSplits_length_pos {parent : Shape} (h : parent ∈ positiveShapes 8) :
    0 < (levelThreeSplits parent).length := by
  have hcases :
      parent = ⟨1, 1, 6⟩ ∨ parent = ⟨1, 2, 5⟩ ∨ parent = ⟨1, 3, 4⟩ ∨
      parent = ⟨1, 4, 3⟩ ∨ parent = ⟨1, 5, 2⟩ ∨ parent = ⟨1, 6, 1⟩ ∨
      parent = ⟨2, 1, 5⟩ ∨ parent = ⟨2, 2, 4⟩ ∨ parent = ⟨2, 3, 3⟩ ∨
      parent = ⟨2, 4, 2⟩ ∨ parent = ⟨2, 5, 1⟩ ∨ parent = ⟨3, 1, 4⟩ ∨
      parent = ⟨3, 2, 3⟩ ∨ parent = ⟨3, 3, 2⟩ ∨ parent = ⟨3, 4, 1⟩ ∨
      parent = ⟨4, 1, 3⟩ ∨ parent = ⟨4, 2, 2⟩ ∨ parent = ⟨4, 3, 1⟩ ∨
      parent = ⟨5, 1, 2⟩ ∨ parent = ⟨5, 2, 1⟩ ∨ parent = ⟨6, 1, 1⟩ := by
    simpa only [positiveShapes_eight_eq, List.mem_cons, List.not_mem_nil, or_false] using h
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- The reconstruction's untyped node lookup lands in the twenty-one positive total-eight shapes.

This is the `ℕ`-indexed companion of `PositiveLevelThreeData.nodeShape_mem_positiveShapes`; the
recurrence indexes nodes by a plain natural, so the typed statement is not directly applicable.

Proof sketch: `node < 126` gives `node / 6 < 21 = (positiveShapes 8).length`, so the padded
optional lookup is an actual `getElem`, which is a member of the list it indexes. -/
theorem nodeShapeAt_mem_positiveShapes {node : ℕ} (hnode : node < nodeCount) :
    nodeShapeAt node ∈ positiveShapes 8 := by
  have hbound : node < 126 := by
    simpa only [nodeCount] using hnode
  have hindex : node / 6 < (positiveShapes 8).length := by
    rw [positiveShapes_eight_length]
    omega
  unfold nodeShapeAt
  rw [List.getElem?_eq_getElem hindex]
  exact List.getElem_mem (l := positiveShapes 8) hindex

/-- Slot `0` of a genuine node is a valid split slot, so the certificate-order slot list of any
node index below `nodeCount` is nonempty.

This is the hypothesis `localRowsFor_isValid_of_nonempty_validSlots` calls `hslots`, discharged
without looking at any table.

Proof sketch: `0` lies in `List.range splitSlotCount` because `splitSlotCount = 10`, and the
executable slot guard at `0` is exactly `0 < (levelThreeSplits (nodeShapeAt node)).length`, which
is `levelThreeSplits_length_pos` at the node's positive parent shape. -/
theorem validSlots_ne_nil {node : ℕ} (hnode : node < nodeCount) : validSlots node ≠ [] := by
  have hmem : 0 ∈ validSlots node := by
    unfold validSlots
    refine List.mem_filter.mpr ⟨List.mem_range.mpr ?_, ?_⟩
    · decide
    · simp only [splitSlotIsValid, decide_eq_true_eq]
      exact levelThreeSplits_length_pos (nodeShapeAt_mem_positiveShapes hnode)
  exact List.ne_nil_of_mem hmem

/-- **(c)** One coordinate of a shape is at most its coordinate sum.

The bound is stated for an arbitrary natural coordinate selector, matching `shapeCoordinate`'s own
signature; it therefore also covers the out-of-range selectors that fall through to `z`.

Proof sketch: unfold both definitions and split on the two selector tests; each branch is one of
the three summands. -/
theorem shapeCoordinate_le_total (shape : Shape) (coordinate : ℕ) :
    shapeCoordinate shape coordinate ≤ shape.total := by
  unfold shapeCoordinate Shape.total
  split_ifs <;> omega

/-- Membership in the certificate-order slot list implies the executable slot guard.

Proof sketch: the slot list is a filter, so membership carries the Boolean predicate. -/
theorem splitSlotIsValid_of_mem_validSlots {node slot : ℕ} (hslot : slot ∈ validSlots node) :
    splitSlotIsValid node slot = true := by
  unfold validSlots at hslot
  exact (List.mem_filter.mp hslot).2

/-- **(d)** A raw valid slot reads an actual element of the parent's split list.

Proof sketch: the guard is exactly the index bound, so the padded optional lookup is a genuine
`getElem`, which is a member of the list it indexes. -/
theorem splitShapeAt_mem_levelThreeSplits {node slot : ℕ}
    (hslot : splitSlotIsValid node slot = true) :
    splitShapeAt node slot ∈ levelThreeSplits (nodeShapeAt node) := by
  have hindex : slot < (levelThreeSplits (nodeShapeAt node)).length := by
    simpa only [splitSlotIsValid, decide_eq_true_eq] using hslot
  unfold splitShapeAt
  rw [List.getElem?_eq_getElem hindex]
  exact List.getElem_mem (l := levelThreeSplits (nodeShapeAt node)) hindex

/-- **(d)** A raw valid slot reconstructs a total-four shape.

Note that no bound on `node` is needed: whatever parent shape the padded node lookup returns, a
valid slot of it is by construction an element of `levelThreeSplits`, whose elements all have
total four.

Proof sketch: `mem_levelThreeSplits` on `splitShapeAt_mem_levelThreeSplits`. -/
theorem splitShapeAt_total {node slot : ℕ} (hslot : splitSlotIsValid node slot = true) :
    (splitShapeAt node slot).total = 4 :=
  (mem_levelThreeSplits (splitShapeAt_mem_levelThreeSplits hslot)).1

/-- **(c) + (d)** Every coordinate of every valid split shape is below `coordinateCount`.

This is the premise that removes the executable modulus from `splitSupport`: with it, the support
triple stored at a slot is the unsimplified shape coordinate that `marginalXNumerators` tests.

Proof sketch: chain the coordinate ≤ total bound with the total-four identity at a valid slot, and
compare against `coordinateCount = 5`. -/
theorem shapeCoordinate_splitShapeAt_lt_coordinateCount {node slot : ℕ}
    (hslot : splitSlotIsValid node slot = true) (coordinate : ℕ) :
    shapeCoordinate (splitShapeAt node slot) coordinate < coordinateCount := by
  have hle := shapeCoordinate_le_total (splitShapeAt node slot) coordinate
  rw [splitShapeAt_total hslot] at hle
  have hcount : coordinateCount = 5 := by
    simp only [coordinateCount]
  omega

/-- **(e)** Positivity of a role-selected dual factor row, from the three stored leg rows.

Generated dual weight tables store each factor minus one and therefore prove exactly the three
per-leg statements `0 < weights.x value`, `0 < weights.y value`, `0 < weights.z value`.  This
theorem aggregates them into the single coordinate-parametric form the structural validity lemma
consumes, for all three physical roles at once.

Proof sketch: `DualWeights.forCoordinate` is a two-test selector among the three stored rows.
Unfolding the selector before `split_ifs` beta-reduces the chosen factor row at `value`. -/
theorem dualWeights_forCoordinate_pos {weights : DualWeights}
    (hx : ∀ value, 0 < weights.x value)
    (hy : ∀ value, 0 < weights.y value)
    (hz : ∀ value, 0 < weights.z value)
    (coordinate : Fin 3) (value : Fin coordinateCount) :
    0 < weights.forCoordinate coordinate value := by
  unfold DualWeights.forCoordinate
  split_ifs
  · exact hx value
  · exact hy value
  · exact hz value

/-! ## The reusable endpoints -/

/-- **The singleton endpoint.**  A level-three local row is valid as soon as its node index is a
genuine node and its dual factors are coordinatewise positive.

Nothing else is assumed: no primary table value, no occurrence mass, no orientation property, and
no property of the quotient slot map.  This replaces a per-node serialized row snapshot together
with its executable `localRowsValid` check.

Proof sketch: discharge the three premises of
`localRowsFor_isValid_of_nonempty_validSlots`.  Nonemptiness of the slot list is
`validSlots_ne_nil`; the coordinate premise is the total-four bound at every valid slot; the
weight premise is passed through unchanged. -/
theorem localRowsFor_isValid_of_node_lt (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ)
    (hnode : node < nodeCount)
    (hweights : ∀ coordinate value, 0 < (weights.forCoordinate coordinate) value) :
    (localRowsFor supportSlot data order weights node region).IsValid := by
  refine localRowsFor_isValid_of_nonempty_validSlots supportSlot data order weights node region
    (validSlots_ne_nil hnode) ?_ hweights
  intro slot hslot
  exact shapeCoordinate_splitShapeAt_lt_coordinateCount
    (splitSlotIsValid_of_mem_validSlots hslot) (order.x : ℕ)

/-- The singleton endpoint in the shape a generated dual weight table proves directly.

Proof sketch: aggregate the three per-leg positivity rows with `dualWeights_forCoordinate_pos`. -/
theorem localRowsFor_isValid_of_node_lt_of_legPos (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ)
    (hnode : node < nodeCount)
    (hx : ∀ value, 0 < weights.x value)
    (hy : ∀ value, 0 < weights.y value)
    (hz : ∀ value, 0 < weights.z value) :
    (localRowsFor supportSlot data order weights node region).IsValid :=
  localRowsFor_isValid_of_node_lt supportSlot data order weights node region hnode
    (dualWeights_forCoordinate_pos hx hy hz)

/-- Sorted-pair specialization of the singleton endpoint. -/
theorem localRows_isValid_of_node_lt (data : PrimaryTables)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ)
    (hnode : node < nodeCount)
    (hweights : ∀ coordinate value, 0 < (weights.forCoordinate coordinate) value) :
    (localRows data order weights node region).IsValid :=
  localRowsFor_isValid_of_node_lt sortedPairSupportSlot data order weights node region hnode
    hweights

/-- The singleton endpoint in the outer-weighted shape.

This is verbatim the proposition a generated per-node validity leaf states, generalized over its
literal node, region, orientation, dual factors and quotient. -/
theorem weightedLocalRowsFor_rows_isValid_of_node_lt (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ)
    (hnode : node < nodeCount)
    (hweights : ∀ coordinate value, 0 < (weights.forCoordinate coordinate) value) :
    (weightedLocalRowsFor supportSlot data massThree order weights node region).rows.IsValid := by
  change (localRowsFor supportSlot data order weights node region).IsValid
  exact localRowsFor_isValid_of_node_lt supportSlot data order weights node region hnode hweights

/-- Sorted-pair specialization of the outer-weighted singleton endpoint. -/
theorem weightedLocalRows_rows_isValid_of_node_lt (data : PrimaryTables) (massThree : Array ℕ)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ)
    (hnode : node < nodeCount)
    (hweights : ∀ coordinate value, 0 < (weights.forCoordinate coordinate) value) :
    (weightedLocalRows data massThree order weights node region).rows.IsValid :=
  weightedLocalRowsFor_rows_isValid_of_node_lt sortedPairSupportSlot data massThree order weights
    node region hnode hweights

/-- **The regional endpoint.**  Every entry of a level-three region is valid as soon as the
per-node dual factor family is positive.

No chunk cover, no active-node reduction, and no per-node snapshot appears: the active-node list is
a filter of `List.range nodeCount`, so its elements carry their own node bound.  This replaces both
the per-node validity leaves of a region and its regional validity reduction.

Proof sketch: an entry of `regionEntriesFor` is the weighted row at some active node; membership
supplies the node bound through `lt_nodeCount_of_mem_activeNodes`, and the singleton endpoint
finishes. -/
theorem regionEntriesFor_isValid_of_weights_pos (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ)
    (hweights : ∀ node coordinate value, 0 < (((weights node).forCoordinate coordinate) value)) :
    ∀ entry ∈ regionEntriesFor supportSlot data massThree orders weights region,
      entry.rows.IsValid := by
  intro entry hentry
  unfold regionEntriesFor at hentry
  rcases List.mem_map.mp hentry with ⟨node, hnode, rfl⟩
  exact weightedLocalRowsFor_rows_isValid_of_node_lt supportSlot data massThree (orders region)
    (weights node) node region (lt_nodeCount_of_mem_activeNodes hnode) (hweights node)

/-- The regional endpoint in the shape a generated dual weight table proves directly. -/
theorem regionEntriesFor_isValid_of_legPos (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ)
    (hx : ∀ node value, 0 < (weights node).x value)
    (hy : ∀ node value, 0 < (weights node).y value)
    (hz : ∀ node value, 0 < (weights node).z value) :
    ∀ entry ∈ regionEntriesFor supportSlot data massThree orders weights region,
      entry.rows.IsValid :=
  regionEntriesFor_isValid_of_weights_pos supportSlot data massThree orders weights region
    fun node ↦ dualWeights_forCoordinate_pos (hx node) (hy node) (hz node)

/-- Sorted-pair specialization of the regional endpoint. -/
theorem regionEntries_isValid_of_weights_pos (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ)
    (hweights : ∀ node coordinate value, 0 < (((weights node).forCoordinate coordinate) value)) :
    ∀ entry ∈ regionEntries data massThree orders weights region, entry.rows.IsValid :=
  regionEntriesFor_isValid_of_weights_pos sortedPairSupportSlot data massThree orders weights
    region hweights

/-- Sorted-pair regional endpoint in the shape a generated dual weight table proves directly. -/
theorem regionEntries_isValid_of_legPos (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights) (region : ℕ)
    (hx : ∀ node value, 0 < (weights node).x value)
    (hy : ∀ node value, 0 < (weights node).y value)
    (hz : ∀ node value, 0 < (weights node).z value) :
    ∀ entry ∈ regionEntries data massThree orders weights region, entry.rows.IsValid :=
  regionEntriesFor_isValid_of_legPos sortedPairSupportSlot data massThree orders weights region
    hx hy hz

/-- The regional endpoint over an explicit node subfamily.

Chunked clients that state their rows through `regionEntriesOnNodesFor` only have to know that
their serialized nodes are genuine node indices.

Proof sketch: an entry is the weighted row at a listed node; apply the singleton endpoint. -/
theorem regionEntriesOnNodesFor_isValid_of_weights_pos (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (hnodes : ∀ node ∈ nodes, node < nodeCount)
    (hweights : ∀ node coordinate value, 0 < (((weights node).forCoordinate coordinate) value)) :
    ∀ entry ∈ regionEntriesOnNodesFor supportSlot data massThree orders weights region nodes,
      entry.rows.IsValid := by
  intro entry hentry
  unfold regionEntriesOnNodesFor at hentry
  rcases List.mem_map.mp hentry with ⟨node, hnode, rfl⟩
  exact weightedLocalRowsFor_rows_isValid_of_node_lt supportSlot data massThree (orders region)
    (weights node) node region (hnodes node hnode) (hweights node)

end MatrixMultiplication.SimplifiedExponentLevelThreeStructuralValidity
