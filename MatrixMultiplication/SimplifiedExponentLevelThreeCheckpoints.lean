/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedExponentLevelThreeValidity

set_option autoImplicit false

/-!
# Compositional checkpoints for level-three recurrence rows

Generated level-three certificates check each node independently and then pack several checked
nodes into a small module.  This file supplies the paper-independent semantic interface for that
layout.  A `LevelThreeNodeStatistic` stores only the three canonical signed-log forms; the
`IsCheckedNode` relation separately proves that those forms are obtained from the reconstructed
recurrence.  This separation prevents a generated payload from turning a form literal into a
semantic claim without the corresponding recurrence equality.

The chunk-composition theorems use the existing singleton semantic bridge and exact
list-flattening laws.  They never normalize a joint form, so their proof cost is linear in the
number of named checkpoints rather than in the total number of logarithm terms.

The active-node enumeration has a similarly bounded interface.  Consecutive filtered ranges
compose structurally, so a generated client can check the two halves of the 126-node search with
separate reductions over only 63 candidates and recover the semantic `activeNodes` list without a
whole-vector decision procedure.

Four generic list lemmas justify the structural validity layer.  They identify mapped-list sums
with finite indexed sums, identify a mapped range with its canonical finite tuple, show that an
aligned list is recovered from its bounded `getD` function, and show that a finite-coordinate
marginal is exactly the `List.ofFn` serialization of its `Finset` pushforward.  Consequently a
generated node needs only prove nonempty support, the coordinate bound that removes an executable
modulus, and positivity of its dual weights; it never snapshots the full `LocalRows` record.

The final theorem transports those independently proved local-row facts across an explicit chunk
cover of the active nodes.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelThreeCheckpoints

open scoped BigOperators

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-! ## Generic aligned-list serialization -/

/-- A finite list is exactly the `List.ofFn` serialization of its in-range `getD` function.

The default value is irrelevant because the domain is `Fin values.length`.  Stating the lemma
with `getElem?` and `getD` matches the total lookup used by certificate row structures, while its
proof reduces to the standard `List.ofFn_get` theorem.

Proof sketch: replace each optional lookup by `List.getD`, use `List.getD_eq_get` at its bounded
index, and reconstruct the original list with `List.ofFn_get`. -/
theorem list_eq_ofFn_getElem?_getD {α : Type*} (values : List α) (default : α) :
    values =
      List.ofFn fun index : Fin values.length ↦ values[index.val]?.getD default := by
  calc
    values = List.ofFn (List.get values) := (List.ofFn_get values).symm
    _ = List.ofFn
        (fun index : Fin values.length ↦ values[index.val]?.getD default) := by
      congr 1
      funext index
      rw [← List.getD_eq_getElem?_getD, List.getD_eq_get]

/-- Summing a mapped list is the same as summing the corresponding finite-indexed family.

This small bridge is useful inside dependent `List.ofFn` proofs: it removes the finite sum before
an outer list extensionality argument introduces proof-dependent `getElem` casts.

Proof sketch: serialize the finite family as a list, rewrite that serialization as `List.map`, and
then take the sum of both sides. -/
theorem sum_map_eq_sum_get {α M : Type*} [AddCommMonoid M]
    (values : List α) (f : α → M) :
    (values.map f).sum = ∑ index : Fin values.length, f (values.get index) := by
  calc
    (values.map f).sum =
        (List.ofFn fun index : Fin values.length ↦ f (values.get index)).sum := by
      rw [List.ofFn_comp', List.ofFn_get]
    _ = ∑ index : Fin values.length, f (values.get index) := List.sum_ofFn

/-- Mapping a natural-number function over `List.range` is its canonical `List.ofFn` tuple.

Proof sketch: compare the two lists through `List.get`.  Their lengths are both `n`, and at index
`i` the range lookup and the `Fin` value are both the same natural number `i`. -/
theorem map_range_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn fun index : Fin n ↦ f index.val := by
  apply List.ext_get
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro index _hleft _hright
    rw [List.get_ofFn]
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, Fin.val_cast]

/-- An aligned finite list's coordinate marginal is the canonical `List.ofFn` pushforward.

The left side is the executable representation used by generated rows: enumerate coordinate
values and sum the numerators of list entries with that value.  The right side is the semantic
`marginalNumerator` over the finite index type of the same list.

Proof sketch: compare the two coordinate-count lists entrywise.  At one coordinate,
`sum_map_eq_sum_get` turns the finite-indexed sum into a map over the original state list, and
extensionality of `Fin` identifies the two equality tests. -/
theorem alignedMarginalList_eq_ofFn_marginalNumerator
    {α : Type*} (coordinateCount : ℕ) (states : List α)
    (coordinate : α → Fin coordinateCount) (numerator : α → ℕ) :
    (List.range coordinateCount).map (fun value ↦
        (states.map fun state ↦
          if (coordinate state).val = value then numerator state else 0).sum) =
      List.ofFn (marginalNumerator
        (fun index : Fin states.length ↦ coordinate (states.get index))
        (fun index : Fin states.length ↦ numerator (states.get index))) := by
  rw [map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext value
  unfold marginalNumerator
  calc
    (states.map fun state ↦
        if (coordinate state).val = value.val then numerator state else 0).sum =
        (states.map fun state ↦
          if coordinate state = value then numerator state else 0).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro state _hstate
      simp only [Fin.ext_iff]
    _ = ∑ index : Fin states.length,
          if coordinate (states.get index) = value then
            numerator (states.get index) else 0 :=
      sum_map_eq_sum_get states
        (fun state ↦ if coordinate state = value then numerator state else 0)

/-- Aligned list-backed local rows satisfy the two serialization identities required by
`LocalRows.IsValid`.

This theorem is independent of the level-three shape encoding.  It applies whenever the support
and reference rows are maps of one nonempty state list and the stored marginal is the explicit
coordinate pushforward of those same aligned entries.

Proof sketch: nonemptiness survives `List.map`.  The reference identity is
`list_eq_ofFn_getElem?_getD`; the marginal identity is
`alignedMarginalList_eq_ofFn_marginalNumerator`, after simplifying bounded lookups through the two
aligned maps.  The remaining fields are precisely the three supplied positivity hypotheses. -/
theorem LocalRows.isValid_of_aligned
    {α : Type*} {coordinateCount : ℕ} (rows : LocalRows coordinateCount)
    (states : List α) (supportValue : α → CoordinateTriple coordinateCount)
    (referenceValue : α → ℕ)
    (hstates : states ≠ [])
    (hsupport : rows.support = states.map supportValue)
    (hreference : rows.referenceNumerators = states.map referenceValue)
    (hmarginal : rows.marginalXNumerators =
      (List.range coordinateCount).map (fun value ↦
        (states.map fun state ↦
          if (supportValue state).x.val = value then referenceValue state else 0).sum))
    (hweightX : ∀ value, 0 < rows.weightX value)
    (hweightY : ∀ value, 0 < rows.weightY value)
    (hweightZ : ∀ value, 0 < rows.weightZ value) :
    rows.IsValid := by
  rcases rows with
    ⟨support, referenceNumerators, marginalXNumerators,
      weightX, weightY, weightZ, logicalY, logicalZ⟩
  dsimp only at hsupport hreference hmarginal hweightX hweightY hweightZ ⊢
  subst support
  subst referenceNumerators
  subst marginalXNumerators
  unfold LocalRows.IsValid
  refine ⟨?_, ?_, ?_, hweightX, hweightY, hweightZ⟩
  · simpa only [List.length_map] using List.length_pos_iff_ne_nil.mpr hstates
  · unfold LocalRows.referenceNumerator
    apply List.ext_get
    · simp only [List.length_map, List.length_ofFn]
    · intro index hleft _hright
      rw [List.get_ofFn]
      simp only [List.get_eq_getElem, Fin.val_cast]
      rw [← List.getD_eq_getElem?_getD]
      rw [List.getD_eq_getElem (l := states.map referenceValue) (d := 0) hleft]
  · unfold LocalRows.coordinateX LocalRows.supportAt LocalRows.referenceNumerator
    rw [alignedMarginalList_eq_ofFn_marginalNumerator coordinateCount states
      (fun state ↦ (supportValue state).x) referenceValue]
    apply congrArg List.ofFn
    funext value
    unfold marginalNumerator
    let e : Fin (states.map supportValue).length ≃ Fin states.length :=
      finCongr (by simp only [List.length_map])
    symm
    refine Fintype.sum_equiv e _ _ ?_
    intro state
    have hstate : state.val < states.length := by
      simpa only [List.length_map] using state.isLt
    have href : state.val < (states.map referenceValue).length := by
      simpa only [List.length_map] using hstate
    change
      (if ((states.map supportValue).get state).x = value then
          (states.map referenceValue)[state.val]?.getD 0
        else 0) =
        (if (supportValue (states.get (e state))).x = value then
          referenceValue (states.get (e state))
        else 0)
    rw [← List.getD_eq_getElem?_getD,
      List.getD_eq_getElem (l := states.map referenceValue) (d := 0) href]
    simp only [e, List.get_eq_getElem, List.getElem_map, finCongr_apply_coe]
    rfl

/-! ## Active-node range checkpoints -/

/-- Active nodes in one consecutive candidate range.

This is the bounded counterpart of `activeNodes`: generated certificate leaves can reduce a short
range independently, while the structural laws below reconstruct the full semantic enumeration.
-/
def activeNodesRange (data : PrimaryTables) (massThree : Array ℕ)
    (region start count : ℕ) : List ℕ :=
  (List.range' start count).filter fun node ↦
    decide (0 < outerNumerator data massThree node region)

/-- Adjacent active-node ranges concatenate to the corresponding combined range.

Proof sketch: `List.range'_append_1` splits the candidate interval, and `List.filter_append`
distributes the common positivity predicate over that split.  No certificate data or finite
reduction enters the proof. -/
theorem activeNodesRange_append (data : PrimaryTables) (massThree : Array ℕ)
    (region start left right : ℕ) :
    activeNodesRange data massThree region start left ++
        activeNodesRange data massThree region (start + left) right =
      activeNodesRange data massThree region start (left + right) := by
  unfold activeNodesRange
  rw [← List.filter_append, List.range'_append_1]

/-- Two independently checked 63-candidate snapshots reconstruct the full active-node list.

The explicit `low` and `high` arguments are the certificate boundary: each premise can be proved
in its own small generated module, while this theorem contains only structural list reasoning.

Proof sketch: identify `List.range nodeCount` with `List.range' 0 nodeCount`, unfold
`nodeCount = 63 + 63`, apply `activeNodesRange_append`, and substitute the two snapshots. -/
theorem activeNodes_eq_append_twoRanges
    (data : PrimaryTables) (massThree : Array ℕ) (region : ℕ)
    (low high : List ℕ)
    (hlow : activeNodesRange data massThree region 0 63 = low)
    (hhigh : activeNodesRange data massThree region 63 63 = high) :
    activeNodes data massThree region = low ++ high := by
  calc
    activeNodes data massThree region =
        activeNodesRange data massThree region 0 nodeCount := by
      unfold activeNodes activeNodesRange
      rw [List.range_eq_range']
    _ = activeNodesRange data massThree region 0 (63 + 63) := by rfl
    _ = activeNodesRange data massThree region 0 63 ++
        activeNodesRange data massThree region (0 + 63) 63 :=
      (activeNodesRange_append data massThree region 0 63 63).symm
    _ = low ++ high := by simpa only [Nat.zero_add, hlow, hhigh]

/-! ## Singleton and chunk checkpoints -/

/-- A singleton structural-power canonicalization identifies the exact semantic branch rate.

This is the kernel-friendly counterpart of
`branchRateOnNodesFor_eq_eval_of_canonical`: generated clients may use the structurally recursive
canonicalizer directly, without exposing intermediate power-normalized or coefficient-collected
forms.

Proof sketch: apply real evaluation to the checked form equality.  Structural power
canonicalization preserves evaluation, and `branchFormOnNodesFor_eval` identifies the source
form's evaluation with the reconstructed singleton rate. -/
theorem branchRateOnNodesFor_eq_eval_of_structuralPowerCanonical
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region node : ℕ) (branch : Fin 3) (expected : Form)
    (hcanonical :
      Form.structuralPowerCanonical
        (branchFormOnNodesFor supportSlot data massThree orders weights region [node] branch) =
          expected) :
    branchRateOnNodesFor supportSlot data massThree orders weights region [node] branch =
      Form.eval ((referenceBits + compatibilityExtraBits) + outerBits) expected := by
  have heval := congrArg
    (Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)) hcanonical
  rw [Form.eval_structuralPowerCanonical, branchFormOnNodesFor_eval] at heval
  exact heval

/-- The three exact signed-log forms retained for one level-three node.

This record contains data only.  Its connection to the reconstructed recurrence is expressed by
`IsCheckedNode`, keeping the certificate payload separate from its semantic justification. -/
structure LevelThreeNodeStatistic where
  canonical : Fin 3 → Form

/-- A node statistic is checked when each of its three forms is the structural power canonical
form of the corresponding singleton recurrence.

The relation is deliberately proof-valued rather than a Boolean stored in
`LevelThreeNodeStatistic`: generated literals remain reusable data, while this proposition is the
only route from those literals to a branch-rate theorem. -/
def IsCheckedNode
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region node : ℕ) (statistic : LevelThreeNodeStatistic) : Prop :=
  ∀ branch,
    Form.structuralPowerCanonical
      (branchFormOnNodesFor supportSlot data massThree orders weights region [node] branch) =
        statistic.canonical branch

/-- Pointwise checked statistics for an explicit node chunk.

`List.Forall₂` records both coverage and ordering: a statistic cannot be silently reused for a
different node, omitted, or inserted without rebuilding the relation proof. -/
def CheckedNodeChunk
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ)
    (statistics : List LevelThreeNodeStatistic) : Prop :=
  List.Forall₂
    (IsCheckedNode supportSlot data massThree orders weights region) nodes statistics

/-- A checked node chunk has branch rate equal to the sum of its independently checked forms.

Proof sketch: induct through the `Forall₂` witness.  At the head, split the node list as
`[node] ++ tail` using `branchRateOnNodesFor_flatten`, invoke the singleton structural-canonical
bridge, and use the induction hypothesis for the tail.  No form containing two nodes is ever
canonicalized. -/
theorem checkedChunk_branchRate
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) {nodes : List ℕ} {statistics : List LevelThreeNodeStatistic}
    (hchecked :
      CheckedNodeChunk supportSlot data massThree orders weights region nodes statistics)
    (branch : Fin 3) :
    branchRateOnNodesFor supportSlot data massThree orders weights region nodes branch =
      (statistics.map fun statistic ↦
        Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
          (statistic.canonical branch)).sum := by
  induction hchecked with
  | nil => rfl
  | @cons node statistic nodes statistics hnode htail ih =>
      have hsplit := branchRateOnNodesFor_flatten supportSlot data massThree orders weights
        region [[node], nodes] branch
      have hhead := branchRateOnNodesFor_eq_eval_of_structuralPowerCanonical
        supportSlot data massThree orders weights region node branch
          (statistic.canonical branch) (hnode branch)
      calc
        branchRateOnNodesFor supportSlot data massThree orders weights region
            (node :: nodes) branch =
            branchRateOnNodesFor supportSlot data massThree orders weights region [node] branch +
              branchRateOnNodesFor supportSlot data massThree orders weights region nodes branch :=
          by simpa using hsplit
        _ = Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
              (statistic.canonical branch) +
              (statistics.map fun tailStatistic ↦
                Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
                  (tailStatistic.canonical branch)).sum := by rw [hhead, ih]
        _ = ((statistic :: statistics).map fun tailStatistic ↦
              Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
                (tailStatistic.canonical branch)).sum := by
          simp only [List.map_cons, List.sum_cons]

/-- A `Forall₂` family of checked chunks composes over the flattened node family.

The right side is the evaluation sum over the flattened statistic lists.  This is the form needed
by regional generated clients: each inner list may be checked in its own small module, and the
outer proof uses only the already-proved chunk theorem and the recurrence's flattening law.

Proof sketch: first split the semantic rate over `nodeChunks` with
`branchRateOnNodesFor_flatten`.  Induct over the outer `Forall₂`, replacing each chunk rate by
`checkedChunk_branchRate`; list-map and sum laws identify the result with the flattened statistic
list. -/
theorem checkedChunks_branchRate_flatten
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) {nodeChunks : List (List ℕ)}
    {statisticChunks : List (List LevelThreeNodeStatistic)}
    (hchecked : List.Forall₂
      (CheckedNodeChunk supportSlot data massThree orders weights region)
      nodeChunks statisticChunks)
    (branch : Fin 3) :
    branchRateOnNodesFor supportSlot data massThree orders weights region
        nodeChunks.flatten branch =
      (statisticChunks.flatten.map fun statistic ↦
        Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
          (statistic.canonical branch)).sum := by
  rw [branchRateOnNodesFor_flatten]
  induction hchecked with
  | nil => rfl
  | @cons nodes statistics nodeChunks statisticChunks hchunk htail ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons,
        List.map_append, List.sum_append]
      rw [checkedChunk_branchRate supportSlot data massThree orders weights region
        hchunk branch, ih]

/-- A checked chunk family evaluates as one exact outer sum of its per-chunk form sums.

This is the certificate-facing checkpoint form of `checkedChunks_branchRate_flatten`.  A generated
client may name one `Form.sum` for each small node chunk and compose only those outer checkpoints;
the final proof never unfolds all singleton statistics into one large form.

Proof sketch: first replace the semantic rate by the flattened sum of singleton evaluations using
`checkedChunks_branchRate_flatten`.  Apply `Form.eval_sum` to the displayed outer and inner form
sums, then induct over the statistic chunks; `List.map_append` and `List.sum_append` identify the
flattened evaluation list with the sum of the per-chunk evaluation lists. -/
theorem checkedChunks_branchRate_sumForms
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) {nodeChunks : List (List ℕ)}
    {statisticChunks : List (List LevelThreeNodeStatistic)}
    (hchecked : List.Forall₂
      (CheckedNodeChunk supportSlot data massThree orders weights region)
      nodeChunks statisticChunks)
    (branch : Fin 3) :
    branchRateOnNodesFor supportSlot data massThree orders weights region
        nodeChunks.flatten branch =
      Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
        (Form.sum (statisticChunks.map fun statistics ↦
          Form.sum (statistics.map fun statistic ↦ statistic.canonical branch))) := by
  rw [checkedChunks_branchRate_flatten supportSlot data massThree orders weights region
    hchecked branch, Form.eval_sum]
  clear hchecked nodeChunks
  induction statisticChunks with
  | nil => rfl
  | cons statistics statisticChunks ih =>
      simp only [List.flatten_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, List.map_map, Form.eval_sum, ih]
      congr 1

/-! ## Structural validity and active-node covers -/

/-- The quotient-parametric local row is valid from bounded structural facts alone.

The coordinate premise is needed because `splitSupport` deliberately stores
`shapeCoordinate ... % coordinateCount` to keep its executable definition proof-free, whereas
`marginalXNumerators` compares the unsimplified shape coordinate.  On a valid slot, the stated
bound makes that modulus extensionally the identity.  No equality with a serialized row snapshot
is assumed.

Proof sketch: instantiate `LocalRows.isValid_of_aligned` with `validSlots node`.  Both support and
reference rows are definitionally maps of that list.  For the marginal, compare the two outer
coordinate maps and the two inner slot maps; `Nat.mod_eq_of_lt` identifies their tests on every
valid slot.  The three local weight fields are selected by `DualWeights.forCoordinate`, so the
single coordinate-parametric positivity hypothesis supplies them all. -/
theorem localRowsFor_isValid_of_nonempty_validSlots
    (supportSlot : ℕ → ℕ → ℕ) (data : PrimaryTables)
    (order : CoordinateOrder) (weights : DualWeights) (node region : ℕ)
    (hslots : validSlots node ≠ [])
    (hcoordinate : ∀ slot ∈ validSlots node,
      shapeCoordinate (splitShapeAt node slot) order.x < coordinateCount)
    (hweights : ∀ coordinate value,
      0 < (weights.forCoordinate coordinate) value) :
    (localRowsFor supportSlot data order weights node region).IsValid := by
  let supportValue : ℕ → CoordinateTriple coordinateCount := fun slot ↦
    let shape := splitShapeAt node slot
    { x := ⟨shapeCoordinate shape order.x % coordinateCount,
        Nat.mod_lt _ (by exact Nat.succ_pos 4)⟩
      y := ⟨shapeCoordinate shape order.y % coordinateCount,
        Nat.mod_lt _ (by exact Nat.succ_pos 4)⟩
      z := ⟨shapeCoordinate shape order.z % coordinateCount,
        Nat.mod_lt _ (by exact Nat.succ_pos 4)⟩ }
  let referenceValue : ℕ → ℕ := fun slot ↦
    dyadicNumeratorAt data.pos3Alpha (node * regionCount + region) slot
  refine LocalRows.isValid_of_aligned
    (rows := localRowsFor supportSlot data order weights node region)
    (states := validSlots node) (supportValue := supportValue)
    (referenceValue := referenceValue) hslots ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · unfold localRowsFor marginalXNumerators
    apply List.map_congr_left
    intro value _hvalue
    apply congrArg List.sum
    apply List.map_congr_left
    intro slot hslot
    dsimp only [supportValue, referenceValue]
    simp only [Nat.mod_eq_of_lt (hcoordinate slot hslot)]
  · exact hweights order.x
  · exact hweights order.y
  · exact hweights order.z

/-- Validity of explicit local rows transports from checked chunks to every regional entry.

The theorem does not prescribe how a generated client proves each local `IsValid` fact.  It only
checks that the supplied chunks cover the computed active-node list and then transports the
pointwise facts through the definition of `regionEntriesFor`.

Proof sketch: membership in `regionEntriesFor` yields an active node whose weighted row is the
given entry.  Rewrite active-node membership using the cover equality, use `List.mem_flatten` to
locate a chunk containing the node, and apply the supplied pointwise validity proof. -/
theorem regionEntriesFor_valid_of_checkedCover
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodeChunks : List (List ℕ))
    (hactive : activeNodes data massThree region = nodeChunks.flatten)
    (hvalid : ∀ nodes ∈ nodeChunks, ∀ node ∈ nodes,
      (localRowsFor supportSlot data (orders region) (weights node) node region).IsValid) :
    ∀ entry ∈ regionEntriesFor supportSlot data massThree orders weights region,
      entry.rows.IsValid := by
  intro entry hentry
  unfold regionEntriesFor at hentry
  rcases List.mem_map.mp hentry with ⟨node, hnode, rfl⟩
  have hnodeFlatten : node ∈ nodeChunks.flatten := by
    rw [← hactive]
    exact hnode
  rcases List.mem_flatten.mp hnodeFlatten with ⟨nodes, hnodes, hnodeIn⟩
  simpa only [weightedLocalRowsFor] using hvalid nodes hnodes node hnodeIn

end MatrixMultiplication.SimplifiedExponentLevelThreeCheckpoints
