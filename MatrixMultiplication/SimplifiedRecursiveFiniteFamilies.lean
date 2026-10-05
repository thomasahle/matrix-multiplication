/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SimplifiedRecursiveFiniteChecks

/-!
# Family checkers for the simplified recursive certificate

`SimplifiedRecursiveFiniteChecks` verifies one level-three node or one level-four parent.  A
generated certificate should not repeat the outer finite-enumeration proof around every local
checker.  This file supplies that thin reusable layer for a complete level-four parent family.

The local checker is already support-aware: a structurally valid top slot with zero numerator is
accepted without inspecting its deliberately omitted beta-three row.  Consequently checking all
105 positive parent shapes is both semantically correct and equivalent to checking just the active
parent support; inactive parents reduce immediately to `true`.

The direct family checker remains useful as a regression, but it can sum the same beta-three row
many times when several top slots share a child.  The compact API below instead lets an untrusted
producer submit a list of distinct `(row, coordinate, total)` keys.  Lean separately checks that
the list covers every active labelled child and that every listed row has mass `2^48`.  The
soundness theorem then recovers the full semantic family proposition.  Thus compression affects
only evaluation cost, never the trusted statement.

For large regional key sets, the indexed coverage variant also accepts an untrusted key-to-index
function and a separately supplied key array.  Each required key is checked against the indicated
array entry; a structural `keyArray.toList = keys` proof connects coverage to the list normalized
once above.  This avoids repeated linear membership reductions while preserving exactly the same
semantic conclusion.

No optimizer output, certificate hash, orientation choice, or generated table occurs here.
-/

namespace MatrixMultiplication.SimplifiedRecursiveFiniteFamilies

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveFiniteChecks
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Executable universal quantification over `Fin n`, using its canonical ordered list. -/
private def allFin (n : ℕ) (predicate : Fin n → Bool) : Bool :=
  (List.ofFn (fun i : Fin n ↦ i)).all predicate

/-- A successful `allFin` computation proves its predicate at every finite index.

Proof sketch: the requested index occurs in `List.ofFn id`; project its Boolean equality from
`List.all_eq_true`. -/
private theorem allFin_sound {n : ℕ} (predicate : Fin n → Bool)
    (hcheck : allFin n predicate = true) (i : Fin n) : predicate i = true := by
  exact (List.all_eq_true.mp hcheck) i (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- Executable universal quantification over the three tensor legs. -/
private def allLegs (predicate : Leg → Bool) : Bool :=
  predicate .X && predicate .Y && predicate .Z

/-- A successful three-leg computation proves the predicate at any leg. -/
private theorem allLegs_sound (predicate : Leg → Bool) (hcheck : allLegs predicate = true)
    (c : Leg) : predicate c = true := by
  cases c <;> simp_all [allLegs]

/-- Check child-row normalization for every positive level-four parent shape at fixed root,
incoming region, and logical orientation. -/
def levelFourParentFamilyChildRowsValidCheck
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (sigma : Orientation) : Bool :=
  allFin positiveLevelFourShapeCount fun parent ↦
    levelFourChildRowsValidCheck top betaThree root region parent sigma

/-- Passing the family checker proves child-row normalization for every level-four parent.

Proof sketch: project the requested parent from the outer finite enumeration, then apply the
proved soundness theorem of the local checker.  Inactive parents need no separate case because the
local check contains the top-support guard. -/
theorem levelFourParentFamilyChildRowsValid_of_check
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (sigma : Orientation)
    (hcheck : levelFourParentFamilyChildRowsValidCheck
      top betaThree root region sigma = true) :
    ∀ parent, LevelFourChildRowsValid top betaThree root region parent sigma := by
  intro parent
  exact levelFourChildRowsValid_of_check top betaThree root region parent sigma
    (allFin_sound _ hcheck parent)

/-! ## Distinct child-row keys -/

/-- Sufficient statistic for one guarded beta-three child row.

`row` selects a global `(shape, incoming-region)` row, `coordinate` selects its physical tensor
leg, and `total` records the complete-split weight used by the intrinsic child shape. -/
structure LevelFourChildRowKey where
  row : ℕ
  coordinate : ℕ
  total : ℕ
  deriving DecidableEq, Repr

/-- Key of the ordered left child at one active level-four slot. -/
def levelFourLeftChildRowKey
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) : LevelFourChildRowKey :=
  let pair := levelFourPairAtSlot parent slot.1 slot.2
  { row := shapeEightIndex pair.1 * 6 + region.val
    coordinate := (coordinateOfLeg (sigma c)).val
    total := (levelFourChildShape parent sigma slot).get c }

/-- Key of the labelled right child at one active level-four slot. -/
def levelFourRightChildRowKey
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) : LevelFourChildRowKey :=
  let pair := levelFourPairAtSlot parent slot.1 slot.2
  let right := RecursiveChildShape.complement
    (levelFourParentIndex_total_twice parent sigma) (levelFourChildShape parent sigma slot)
  { row := shapeEightIndex pair.2 * 6 + region.val
    coordinate := (coordinateOfLeg (sigma c)).val
    total := right.get c }

namespace LevelFourChildRowKey

/-- A submitted key names a beta-three row of exact mass `2^48`. -/
def IsNormalized (betaThree : BetaThreeRows) (key : LevelFourChildRowKey) : Prop :=
  ∑ word : SplitWord 2,
    levelThreeWordCountAt betaThree key.row key.coordinate key.total word =
      levelFourChildSamples

instance (betaThree : BetaThreeRows) (key : LevelFourChildRowKey) :
    Decidable (key.IsNormalized betaThree) := by
  unfold IsNormalized
  infer_instance

end LevelFourChildRowKey

/-- Normalization of a left-child key is definitionally the left child-row sum. -/
theorem levelFourLeftChildRowKey_isNormalized_iff
    (betaThree : BetaThreeRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) :
    (levelFourLeftChildRowKey region parent sigma slot c).IsNormalized betaThree ↔
      ∑ word, levelFourLeftChildWordCount betaThree region parent sigma slot c word =
        levelFourChildSamples :=
  Iff.rfl

/-- Normalization of a right-child key is definitionally the right child-row sum. -/
theorem levelFourRightChildRowKey_isNormalized_iff
    (betaThree : BetaThreeRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) (c : Leg) :
    (levelFourRightChildRowKey region parent sigma slot c).IsNormalized betaThree ↔
      ∑ word, levelFourRightChildWordCount betaThree region parent sigma slot c word =
        levelFourChildSamples :=
  Iff.rfl

/-- Check normalization of each submitted distinct child-row key exactly once. -/
def levelFourChildRowKeysNormalizedCheck
    (betaThree : BetaThreeRows) (keys : List LevelFourChildRowKey) : Bool :=
  keys.all fun key ↦ decide (key.IsNormalized betaThree)

/-- Normalization checks distribute over concatenated certificate chunks.

This law lets generated clients kernel-check bounded key lists separately and assemble the result
without reducing one large Boolean expression again. -/
@[simp] theorem levelFourChildRowKeysNormalizedCheck_append
    (betaThree : BetaThreeRows) (left right : List LevelFourChildRowKey) :
    levelFourChildRowKeysNormalizedCheck betaThree (left ++ right) =
      (levelFourChildRowKeysNormalizedCheck betaThree left &&
        levelFourChildRowKeysNormalizedCheck betaThree right) := by
  simp [levelFourChildRowKeysNormalizedCheck]

/-- Two successful bounded chunk checks give a successful check of their concatenation. -/
theorem levelFourChildRowKeysNormalizedCheck_append_eq_true
    (betaThree : BetaThreeRows) (left right : List LevelFourChildRowKey)
    (hleft : levelFourChildRowKeysNormalizedCheck betaThree left = true)
    (hright : levelFourChildRowKeysNormalizedCheck betaThree right = true) :
    levelFourChildRowKeysNormalizedCheck betaThree (left ++ right) = true := by
  simp [hleft, hright]

/-- Passing the key-normalization checker proves normalization of every key in the submitted list.

Proof sketch: project the key's Boolean equality from `List.all_eq_true`, then decode its decidable
natural-number equality. -/
theorem levelFourChildRowKey_normalized_of_check
    (betaThree : BetaThreeRows) (keys : List LevelFourChildRowKey)
    (hcheck : levelFourChildRowKeysNormalizedCheck betaThree keys = true)
    {key : LevelFourChildRowKey} (hkey : key ∈ keys) : key.IsNormalized betaThree := by
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) key hkey)

/-- Check that a submitted key list covers both labelled children of every active slot of one
level-four parent.  Zero-numerator slots impose no coverage requirement. -/
def levelFourChildRowKeyCoverageCheck
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : List LevelFourChildRowKey) : Bool :=
  (List.ofFn (fun slot : Fin levelFourPairSlotCount ↦ slot)).all fun slot ↦
    if hslot : levelFourPairSlotValid parent slot then
      if _hactive : levelFourSlotNumerator top root region parent ⟨slot, hslot⟩ ≠ 0 then
        allLegs fun c ↦ decide
          (levelFourLeftChildRowKey region parent sigma ⟨slot, hslot⟩ c ∈ keys ∧
            levelFourRightChildRowKey region parent sigma ⟨slot, hslot⟩ c ∈ keys)
      else true
    else true

/-- Passing the coverage checker proves membership of both keys at every active labelled slot.

Proof sketch: specialize the padded-slot enumeration, enter its structural-validity and nonzero
branches, project the requested leg, and decode the checked pair of list memberships. -/
theorem levelFourChildRowKeyCoverage_of_check
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : List LevelFourChildRowKey)
    (hcheck : levelFourChildRowKeyCoverageCheck top root region parent sigma keys = true) :
    ∀ slot c, levelFourSlotNumerator top root region parent slot ≠ 0 →
      levelFourLeftChildRowKey region parent sigma slot c ∈ keys ∧
        levelFourRightChildRowKey region parent sigma slot c ∈ keys := by
  intro slot c hactive
  have hslot := (List.all_eq_true.mp hcheck) slot.1
    (List.mem_ofFn.mpr ⟨slot.1, rfl⟩)
  rw [dif_pos slot.2, dif_pos hactive] at hslot
  exact of_decide_eq_true (allLegs_sound _ hslot c)

/-- Pointwise child-key coverage plus one shared normalization check implies semantic validity.

This is the relation-level soundness boundary shared by the list-membership and indexed-array
certificate formats.  It assumes only that every active computed key belongs to the normalized
list; how a client establishes that membership is deliberately abstract.
-/
theorem levelFourChildRowsValid_of_key_coverage
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : List LevelFourChildRowKey)
    (hcoverage : ∀ slot c, levelFourSlotNumerator top root region parent slot ≠ 0 →
      levelFourLeftChildRowKey region parent sigma slot c ∈ keys ∧
        levelFourRightChildRowKey region parent sigma slot c ∈ keys)
    (hnormalized : levelFourChildRowKeysNormalizedCheck betaThree keys = true) :
    LevelFourChildRowsValid top betaThree root region parent sigma := by
  intro slot c hactive
  have hkeys := hcoverage slot c hactive
  have hleft := levelFourChildRowKey_normalized_of_check betaThree keys hnormalized hkeys.1
  have hright := levelFourChildRowKey_normalized_of_check betaThree keys hnormalized hkeys.2
  constructor
  · exact (levelFourLeftChildRowKey_isNormalized_iff
      betaThree region parent sigma slot c).mp hleft
  · exact (levelFourRightChildRowKey_isNormalized_iff
      betaThree region parent sigma slot c).mp hright

/-- Coverage and one-time key normalization imply the original semantic child-row predicate.

Proof sketch: use coverage to find the left and right keys in the submitted list, use the global
normalization check at those memberships, and unfold the keys.  Their guarded row formulas are
definitionally the two child-count formulas. -/
theorem levelFourChildRowsValid_of_keyChecks
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : List LevelFourChildRowKey)
    (hcoverage : levelFourChildRowKeyCoverageCheck
      top root region parent sigma keys = true)
    (hnormalized : levelFourChildRowKeysNormalizedCheck betaThree keys = true) :
    LevelFourChildRowsValid top betaThree root region parent sigma :=
  levelFourChildRowsValid_of_key_coverage top betaThree root region parent sigma keys
    (levelFourChildRowKeyCoverage_of_check
      top root region parent sigma keys hcoverage) hnormalized

/-! ## Indexed coverage certificates -/

/-- Check indexed child-key coverage over an explicit bounded list of padded slot indices.

Structurally invalid and zero-numerator slots impose no obligation, exactly as in the full parent
checker.  Generated clients use this list form to seal small slot shards independently.
-/
def levelFourSlotListChildRowKeyIndexedCoverageCheck
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slots : List (Fin levelFourPairSlotCount))
    (keys : Array LevelFourChildRowKey) (index : LevelFourChildRowKey → ℕ) : Bool :=
  slots.all fun slot ↦
    if hslot : levelFourPairSlotValid parent slot then
      if _hactive : levelFourSlotNumerator top root region parent ⟨slot, hslot⟩ ≠ 0 then
        allLegs fun c ↦
          let left := levelFourLeftChildRowKey region parent sigma ⟨slot, hslot⟩ c
          let right := levelFourRightChildRowKey region parent sigma ⟨slot, hslot⟩ c
          decide (keys[index left]? = some left ∧ keys[index right]? = some right)
      else true
    else true

/-- Indexed slot-list coverage checks distribute over concatenated slot shards. -/
@[simp] theorem levelFourSlotListChildRowKeyIndexedCoverageCheck_append
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (left right : List (Fin levelFourPairSlotCount))
    (keys : Array LevelFourChildRowKey) (index : LevelFourChildRowKey → ℕ) :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
        top root region parent sigma (left ++ right) keys index =
      (levelFourSlotListChildRowKeyIndexedCoverageCheck
          top root region parent sigma left keys index &&
        levelFourSlotListChildRowKeyIndexedCoverageCheck
          top root region parent sigma right keys index) := by
  simp [levelFourSlotListChildRowKeyIndexedCoverageCheck]

/-- Two successful bounded slot-shard checks compose to a successful appended check. -/
theorem levelFourSlotListChildRowKeyIndexedCoverageCheck_append_eq_true
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (left right : List (Fin levelFourPairSlotCount))
    (keys : Array LevelFourChildRowKey) (index : LevelFourChildRowKey → ℕ)
    (hleft : levelFourSlotListChildRowKeyIndexedCoverageCheck
      top root region parent sigma left keys index = true)
    (hright : levelFourSlotListChildRowKeyIndexedCoverageCheck
      top root region parent sigma right keys index = true) :
    levelFourSlotListChildRowKeyIndexedCoverageCheck
        top root region parent sigma (left ++ right) keys index = true := by
  rw [levelFourSlotListChildRowKeyIndexedCoverageCheck_append, hleft, hright]
  rfl

/-- A successful slot-list check covers every active labelled slot named by that list.

Proof sketch: project the requested slot from `List.all`, enter its validity and activity branches,
decode the leg check, and turn the two exact array reads into array membership.
-/
theorem levelFourSlotListChildRowKeyIndexedCoverage_of_check
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slots : List (Fin levelFourPairSlotCount))
    (keys : Array LevelFourChildRowKey) (index : LevelFourChildRowKey → ℕ)
    (hcheck : levelFourSlotListChildRowKeyIndexedCoverageCheck
      top root region parent sigma slots keys index = true) :
    ∀ slot ∈ slots, ∀ (hslot : levelFourPairSlotValid parent slot) c,
      levelFourSlotNumerator top root region parent ⟨slot, hslot⟩ ≠ 0 →
        levelFourLeftChildRowKey region parent sigma ⟨slot, hslot⟩ c ∈ keys ∧
          levelFourRightChildRowKey region parent sigma ⟨slot, hslot⟩ c ∈ keys := by
  intro slot hmem hslot c hactive
  have hchecked := (List.all_eq_true.mp hcheck) slot hmem
  rw [dif_pos hslot, dif_pos hactive] at hchecked
  have hkeys := of_decide_eq_true (allLegs_sound _ hchecked c)
  exact ⟨Array.mem_of_getElem? hkeys.1, Array.mem_of_getElem? hkeys.2⟩

/-- One of six canonical five-slot shards partitioning the thirty padded level-four slots. -/
def levelFourCoverageSlotShard (shard : Fin 6) : List (Fin levelFourPairSlotCount) :=
  List.ofFn fun offset : Fin 5 ↦
    ⟨5 * shard.val + offset.val, by
      unfold levelFourPairSlotCount
      omega⟩

/-- Every padded level-four slot belongs to one canonical five-slot shard.

Proof sketch: there are only thirty slots.  Splitting on the slot value lets the kernel select its
quotient-by-five shard and verify membership in the corresponding five-element `List.ofFn`.
-/
theorem levelFourCoverageSlotShard_complete (slot : Fin levelFourPairSlotCount) :
    ∃ shard : Fin 6, slot ∈ levelFourCoverageSlotShard shard := by
  fin_cases slot <;> decide +revert

/-- Six successful canonical shard checks cover every active labelled slot of one parent.

Proof sketch: choose the shard containing the requested padded slot using
`levelFourCoverageSlotShard_complete`, then specialize that shard's bounded checker through the
slot-list soundness theorem.
-/
theorem levelFourChildRowKeyIndexedCoverage_of_shards
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : Array LevelFourChildRowKey) (index : LevelFourChildRowKey → ℕ)
    (hcheck : ∀ shard : Fin 6,
      levelFourSlotListChildRowKeyIndexedCoverageCheck
        top root region parent sigma (levelFourCoverageSlotShard shard) keys index = true) :
    ∀ slot c, levelFourSlotNumerator top root region parent slot ≠ 0 →
      levelFourLeftChildRowKey region parent sigma slot c ∈ keys ∧
        levelFourRightChildRowKey region parent sigma slot c ∈ keys := by
  intro slot c hactive
  obtain ⟨shard, hslot⟩ := levelFourCoverageSlotShard_complete slot.1
  exact levelFourSlotListChildRowKeyIndexedCoverage_of_check
    top root region parent sigma (levelFourCoverageSlotShard shard) keys index (hcheck shard)
      slot.1 hslot slot.2 c hactive

/-- Check active child-key coverage through an untrusted key-to-index function.

The index function and array have no authority by themselves.  At every active slot and leg, the
checker requires the indicated entry to equal the complete computed key, including its row,
physical coordinate, and complete-split total.
-/
def levelFourChildRowKeyIndexedCoverageCheck
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : Array LevelFourChildRowKey) (index : LevelFourChildRowKey → ℕ) : Bool :=
  levelFourSlotListChildRowKeyIndexedCoverageCheck top root region parent sigma
    (List.ofFn (fun slot : Fin levelFourPairSlotCount ↦ slot)) keys index

/-- Passing the indexed checker proves ordinary key-list coverage at every active labelled slot.

Proof sketch: specialize the finite slot/leg check, decode its two successful array reads, and use
`Array.mem_of_getElem?` to obtain membership in the submitted array.
-/
theorem levelFourChildRowKeyIndexedCoverage_of_check
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : Array LevelFourChildRowKey) (index : LevelFourChildRowKey → ℕ)
    (hcheck : levelFourChildRowKeyIndexedCoverageCheck
      top root region parent sigma keys index = true) :
    ∀ slot c, levelFourSlotNumerator top root region parent slot ≠ 0 →
      levelFourLeftChildRowKey region parent sigma slot c ∈ keys ∧
        levelFourRightChildRowKey region parent sigma slot c ∈ keys := by
  intro slot c hactive
  exact levelFourSlotListChildRowKeyIndexedCoverage_of_check
    top root region parent sigma (List.ofFn (fun i : Fin levelFourPairSlotCount ↦ i)) keys index
      hcheck slot.1 (List.mem_ofFn.mpr ⟨slot.1, rfl⟩) slot.2 c hactive

/-- Pointwise array coverage, an array/list identity, and list normalization imply child validity.

Proof sketch: convert the two array memberships to memberships of `keyArray.toList`, rewrite that
list through the supplied structural identity, and invoke the relation-level coverage theorem.
-/
theorem levelFourChildRowsValid_of_array_key_coverage
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : List LevelFourChildRowKey) (keyArray : Array LevelFourChildRowKey)
    (harray : keyArray.toList = keys)
    (hcoverage : ∀ slot c, levelFourSlotNumerator top root region parent slot ≠ 0 →
      levelFourLeftChildRowKey region parent sigma slot c ∈ keyArray ∧
        levelFourRightChildRowKey region parent sigma slot c ∈ keyArray)
    (hnormalized : levelFourChildRowKeysNormalizedCheck betaThree keys = true) :
    LevelFourChildRowsValid top betaThree root region parent sigma := by
  apply levelFourChildRowsValid_of_key_coverage
    top betaThree root region parent sigma keys _ hnormalized
  intro slot c hactive
  have harrayKeys := hcoverage slot c hactive
  have hleftMem : levelFourLeftChildRowKey region parent sigma slot c ∈ keyArray.toList := by
    simpa using harrayKeys.1
  have hrightMem : levelFourRightChildRowKey region parent sigma slot c ∈ keyArray.toList := by
    simpa using harrayKeys.2
  rw [harray] at hleftMem hrightMem
  exact ⟨hleftMem, hrightMem⟩

/-- Indexed coverage and one shared normalization check imply semantic child-row validity.

Proof sketch: indexed soundness supplies membership of the computed left and right keys in the
normalized list.  The existing normalization projection and definitional key-row equivalences then
give the two required child sums.
-/
theorem levelFourChildRowsValid_of_indexed_key_check
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (keys : List LevelFourChildRowKey) (keyArray : Array LevelFourChildRowKey)
    (index : LevelFourChildRowKey → ℕ)
    (harray : keyArray.toList = keys)
    (hcoverage : levelFourChildRowKeyIndexedCoverageCheck
      top root region parent sigma keyArray index = true)
    (hnormalized : levelFourChildRowKeysNormalizedCheck betaThree keys = true) :
    LevelFourChildRowsValid top betaThree root region parent sigma :=
  levelFourChildRowsValid_of_array_key_coverage
    top betaThree root region parent sigma keys keyArray harray
      (levelFourChildRowKeyIndexedCoverage_of_check
        top root region parent sigma keyArray index hcoverage) hnormalized

/-- Check child-row key coverage over an explicit finite list of level-four parents.

This list-indexed form is the compositional certificate boundary.  Generated clients can check
small parent shards independently and combine them without reducing the 105-parent family in one
kernel decision.
-/
def levelFourParentListChildRowKeyCoverageCheck
    (top : TopBranchRows) (root region : Fin 6) (sigma : Orientation)
    (parents : List (Fin positiveLevelFourShapeCount))
    (keys : List LevelFourChildRowKey) : Bool :=
  parents.all fun parent ↦
    levelFourChildRowKeyCoverageCheck top root region parent sigma keys

/-- Coverage checks distribute over concatenation of parent shards. -/
theorem levelFourParentListChildRowKeyCoverageCheck_append
    (top : TopBranchRows) (root region : Fin 6) (sigma : Orientation)
    (left right : List (Fin positiveLevelFourShapeCount))
    (keys : List LevelFourChildRowKey) :
    levelFourParentListChildRowKeyCoverageCheck
        top root region sigma (left ++ right) keys =
      (levelFourParentListChildRowKeyCoverageCheck top root region sigma left keys &&
        levelFourParentListChildRowKeyCoverageCheck top root region sigma right keys) := by
  simp [levelFourParentListChildRowKeyCoverageCheck]

/-- Two successful parent-shard checks compose to a successful appended check. -/
theorem levelFourParentListChildRowKeyCoverageCheck_append_eq_true
    (top : TopBranchRows) (root region : Fin 6) (sigma : Orientation)
    (left right : List (Fin positiveLevelFourShapeCount))
    (keys : List LevelFourChildRowKey)
    (hleft : levelFourParentListChildRowKeyCoverageCheck
      top root region sigma left keys = true)
    (hright : levelFourParentListChildRowKeyCoverageCheck
      top root region sigma right keys = true) :
    levelFourParentListChildRowKeyCoverageCheck
        top root region sigma (left ++ right) keys = true := by
  rw [levelFourParentListChildRowKeyCoverageCheck_append, hleft, hright]
  rfl

/-- A successful list check yields coverage for every parent named by that list.

Proof sketch: unfold the list checker through `List.all_eq_true` and specialize the resulting
pointwise statement at the requested member. -/
theorem levelFourParentListChildRowKeyCoverage_of_check
    (top : TopBranchRows) (root region : Fin 6) (sigma : Orientation)
    (parents : List (Fin positiveLevelFourShapeCount))
    (keys : List LevelFourChildRowKey)
    (hcheck : levelFourParentListChildRowKeyCoverageCheck
      top root region sigma parents keys = true) :
    ∀ parent ∈ parents,
      levelFourChildRowKeyCoverageCheck top root region parent sigma keys = true := by
  intro parent hparent
  exact (List.all_eq_true.mp hcheck) parent hparent

/-- Sharded coverage plus shared key normalization proves validity on every listed parent.

Proof sketch: extract the requested parent's local coverage fact from the shard and feed it, with
the one shared normalization certificate, to `levelFourChildRowsValid_of_keyChecks`. -/
theorem levelFourParentListChildRowsValid_of_keyChecks
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (sigma : Orientation) (parents : List (Fin positiveLevelFourShapeCount))
    (keys : List LevelFourChildRowKey)
    (hcoverage : levelFourParentListChildRowKeyCoverageCheck
      top root region sigma parents keys = true)
    (hnormalized : levelFourChildRowKeysNormalizedCheck betaThree keys = true) :
    ∀ parent ∈ parents, LevelFourChildRowsValid top betaThree root region parent sigma := by
  intro parent hparent
  exact levelFourChildRowsValid_of_keyChecks top betaThree root region parent sigma keys
    (levelFourParentListChildRowKeyCoverage_of_check
      top root region sigma parents keys hcoverage parent hparent)
    hnormalized

/-- Check key coverage simultaneously for all 105 positive level-four parent shapes. -/
def levelFourParentFamilyChildRowKeyCoverageCheck
    (top : TopBranchRows) (root region : Fin 6) (sigma : Orientation)
    (keys : List LevelFourChildRowKey) : Bool :=
  allFin positiveLevelFourShapeCount fun parent ↦
    levelFourChildRowKeyCoverageCheck top root region parent sigma keys

/-- Passing the family coverage check proves coverage for any requested positive parent. -/
theorem levelFourParentFamilyChildRowKeyCoverage_of_check
    (top : TopBranchRows) (root region : Fin 6) (sigma : Orientation)
    (keys : List LevelFourChildRowKey)
    (hcheck : levelFourParentFamilyChildRowKeyCoverageCheck
      top root region sigma keys = true) :
    ∀ parent, levelFourChildRowKeyCoverageCheck
      top root region parent sigma keys = true := by
  intro parent
  exact allFin_sound _ hcheck parent

/-- One global key-normalization proof plus one regional coverage proof establishes semantic child
normalization for every parent in that region. -/
theorem levelFourParentFamilyChildRowsValid_of_keyChecks
    (top : TopBranchRows) (betaThree : BetaThreeRows) (root region : Fin 6)
    (sigma : Orientation) (keys : List LevelFourChildRowKey)
    (hcoverage : levelFourParentFamilyChildRowKeyCoverageCheck
      top root region sigma keys = true)
    (hnormalized : levelFourChildRowKeysNormalizedCheck betaThree keys = true) :
    ∀ parent, LevelFourChildRowsValid top betaThree root region parent sigma := by
  intro parent
  exact levelFourChildRowsValid_of_keyChecks top betaThree root region parent sigma keys
    (levelFourParentFamilyChildRowKeyCoverage_of_check
      top root region sigma keys hcoverage parent)
    hnormalized

end MatrixMultiplication.SimplifiedRecursiveFiniteFamilies
