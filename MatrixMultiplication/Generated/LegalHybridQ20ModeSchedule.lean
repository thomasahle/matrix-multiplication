/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry

set_option autoImplicit false

/-!
# Exact row and mode schedule for the legal-hybrid q20 source image

This is the finite schedule used by the legal-hybrid candidate described in
`better_bound/paper.tex:148-159` and assembled by the two rules at
`better_bound/paper.tex:2041-2095`.  It records the 225 active `(region, parent)` keys and the
complete 60-row exceptional-reader mask.  The remaining 165 rows use the ordinary-feature rule.
Among the exceptional rows, 45 use the raw identity reader and 15 use the raw cyclic reader.

The literals were transcribed from the canonical q20 numerical image with candidate SHA-256
`0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d`, mode-mask SHA-256
`90a12654b2bcc0e2d860ebf8667de2efd9a7a96f51605de29c00a40ff77deb67`, standard-witness
SHA-256 `6b45b2c1c24ce9c1d08881d48708919c37ea7d90989762e9b6bb7b5aebb52b6a`, and directed-result
SHA-256 `9ad86e7a945337f88cdbe6f4dfc443e9f6388a3039a8fa5449180c79ad12d1be`.
The fail-closed checker that validates those relations has SHA-256
`d703298914c5f48b61b7c6ffffa18db2e9a03598dd5512c8bafec6b9a2c9c76d`.

This module proves only exact finite schedule facts.  It does not import a numerical certificate,
prove that a row realizes either reader, construct a tensor restriction, or certify an exponent.
The `XZY` convention is stored as the tiny coordinate permutation `[0, 2, 1]`; importing the
tensor-level orientation stack solely for those three values would violate the intended data-leaf
boundary.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule

open AlgebraicComplexity.LevelFourReconstruction

/-- The positive level-four parent index has the nonzero cardinality needed by numeric literals. -/
instance instNeZeroPositiveLevelFourShapeCount :
    NeZero positiveLevelFourShapeCount :=
  ⟨by decide⟩

/-- The two extraction modes used by the final regional assembly. -/
inductive RowMode
  | modeA
  | modeB
  deriving DecidableEq, Repr

/-- The literal checker branch selected for one active row. -/
inductive RowAction
  | ordinaryFeature
  | rawIdentity
  | rawCyclic
  deriving DecidableEq, Repr

/-- Collapse the three checker actions to the two assembly modes. -/
def RowAction.mode : RowAction → RowMode
  | .ordinaryFeature => .modeA
  | .rawIdentity => .modeA
  | .rawCyclic => .modeB

/-- A root-region and positive level-four parent index. -/
abbrev RowKey := Fin 6 × Fin positiveLevelFourShapeCount

/-- One exceptional-reader mask record, including its independently reconstructed parent shape. -/
structure ModeRecord where
  key : RowKey
  shape : Shape
  mode : RowMode
  deriving DecidableEq, Repr

/-- Logical-to-physical coordinate map for the fixed `XZY` orientation. -/
def orientationLogicalToPhysical : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

/-- Logical coordinate zero stays at physical coordinate zero under `XZY`. -/
theorem orientationLogicalToPhysical_zero : orientationLogicalToPhysical 0 = 0 := rfl

/-- Logical coordinate one moves to physical coordinate two under `XZY`. -/
theorem orientationLogicalToPhysical_one : orientationLogicalToPhysical 1 = 2 := rfl

/-- Logical coordinate two moves to physical coordinate one under `XZY`. -/
theorem orientationLogicalToPhysical_two : orientationLogicalToPhysical 2 = 1 := rfl

/-! ## Active row keys, split at the evaluator's regional boundary -/

/-- Region-zero active parents, in the checker's lexicographic row order. -/
def regionZeroRowKeys : List RowKey :=
  ([19, 20, 21, 30, 31, 32, 33, 34, 41, 42, 43, 44, 45, 46, 52, 53, 54, 55,
      56, 57, 62, 63, 64, 65, 66, 67, 70, 71, 72, 73, 74, 75, 78, 79, 80, 81,
      82, 86, 87] : List (Fin positiveLevelFourShapeCount)).map fun parent ↦ (0, parent)

/-- Region-one active parents, in the checker's lexicographic row order. -/
def regionOneRowKeys : List RowKey :=
  ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21,
      22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
      40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
      58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
      76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
      94, 95, 96, 97, 98, 99, 100, 101, 102, 103] :
      List (Fin positiveLevelFourShapeCount)).map fun parent ↦ (1, parent)

/-- Region two has no active q20 row. -/
def regionTwoRowKeys : List RowKey := []

/-- Region three has no active q20 row. -/
def regionThreeRowKeys : List RowKey := []

/-- Region-four active parents, in the checker's lexicographic row order. -/
def regionFourRowKeys : List RowKey :=
  ([18, 19, 20, 21, 22, 30, 31, 32, 33, 34, 35, 41, 42, 43, 44, 45, 46, 47,
      51, 52, 53, 54, 55, 56, 57, 58, 61, 62, 63, 64, 65, 66, 67, 70, 71, 72,
      73, 74, 75, 78, 79, 80, 81, 82, 85, 86, 87, 88] :
      List (Fin positiveLevelFourShapeCount)).map fun parent ↦ (4, parent)

/-- Region-five active parents, in the checker's lexicographic row order. -/
def regionFiveRowKeys : List RowKey :=
  ([19, 20, 21, 31, 32, 33, 34, 42, 43, 44, 45, 46, 52, 53, 54, 55, 56, 57,
      61, 62, 63, 64, 65, 66, 67, 70, 71, 72, 73, 74, 75, 78, 79, 80, 81, 82] :
      List (Fin positiveLevelFourShapeCount)).map fun parent ↦ (5, parent)

/-- Region zero contains 39 active rows. -/
theorem regionZeroRowKeys_length : regionZeroRowKeys.length = 39 := by decide

/-- Region one contains 102 active rows. -/
theorem regionOneRowKeys_length : regionOneRowKeys.length = 102 := by decide

/-- Region two contains no active row. -/
theorem regionTwoRowKeys_length : regionTwoRowKeys.length = 0 := rfl

/-- Region three contains no active row. -/
theorem regionThreeRowKeys_length : regionThreeRowKeys.length = 0 := rfl

/-- Region four contains 48 active rows. -/
theorem regionFourRowKeys_length : regionFourRowKeys.length = 48 := by decide

/-- Region five contains 36 active rows. -/
theorem regionFiveRowKeys_length : regionFiveRowKeys.length = 36 := by decide

/-- Region zero's active-key block has no duplicate. -/
theorem regionZeroRowKeys_nodup : regionZeroRowKeys.Nodup := by decide

/-- Region one's active-key block has no duplicate. -/
theorem regionOneRowKeys_nodup : regionOneRowKeys.Nodup := by decide

/-- The empty region-two key block has no duplicate. -/
theorem regionTwoRowKeys_nodup : regionTwoRowKeys.Nodup := by decide

/-- The empty region-three key block has no duplicate. -/
theorem regionThreeRowKeys_nodup : regionThreeRowKeys.Nodup := by decide

/-- Region four's active-key block has no duplicate. -/
theorem regionFourRowKeys_nodup : regionFourRowKeys.Nodup := by decide

/-- Region five's active-key block has no duplicate. -/
theorem regionFiveRowKeys_nodup : regionFiveRowKeys.Nodup := by decide

/-- Exact regional key block.  This selector is total on the six root regions. -/
def regionalRowKeys (region : Fin 6) : List RowKey :=
  match region.val with
  | 0 => regionZeroRowKeys
  | 1 => regionOneRowKeys
  | 2 => regionTwoRowKeys
  | 3 => regionThreeRowKeys
  | 4 => regionFourRowKeys
  | _ => regionFiveRowKeys

/-- Canonical 225-row key order used by all downstream indexed selectors. -/
def activeRowKeys : List RowKey :=
  ((regionZeroRowKeys ++ regionOneRowKeys) ++ regionFourRowKeys) ++ regionFiveRowKeys

/-- The active schedule has exactly 225 entries. -/
theorem activeRowKeys_length : activeRowKeys.length = 225 := by
  simp only [activeRowKeys, List.length_append, regionZeroRowKeys_length,
    regionOneRowKeys_length, regionFourRowKeys_length, regionFiveRowKeys_length]

private theorem mappedRowKeys_disjoint_of_ne
    {leftRegion rightRegion : Fin 6} (hne : leftRegion ≠ rightRegion)
    (left right : List (Fin positiveLevelFourShapeCount)) :
    List.Disjoint
      (left.map fun parent ↦ (leftRegion, parent))
      (right.map fun parent ↦ (rightRegion, parent)) := by
  rw [List.disjoint_left]
  intro key hleft hright
  rcases List.mem_map.mp hleft with ⟨leftParent, _, rfl⟩
  rcases List.mem_map.mp hright with ⟨rightParent, _, hkey⟩
  exact hne (congrArg Prod.fst hkey).symm

private theorem disjoint_append_left {α : Type*} {left middle right : List α}
    (hleft : List.Disjoint left right) (hmiddle : List.Disjoint middle right) :
    List.Disjoint (left ++ middle) right := by
  rw [List.disjoint_left] at hleft hmiddle ⊢
  intro value hvalue hright
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact hleft hvalue hright
  · exact hmiddle hvalue hright

/-- No active `(region, parent)` key occurs twice. -/
theorem activeRowKeys_nodup : activeRowKeys.Nodup := by
  have hzeroOne : List.Disjoint regionZeroRowKeys regionOneRowKeys := by
    unfold regionZeroRowKeys regionOneRowKeys
    exact mappedRowKeys_disjoint_of_ne (by decide) _ _
  have hzeroFour : List.Disjoint regionZeroRowKeys regionFourRowKeys := by
    unfold regionZeroRowKeys regionFourRowKeys
    exact mappedRowKeys_disjoint_of_ne (by decide) _ _
  have honeFour : List.Disjoint regionOneRowKeys regionFourRowKeys := by
    unfold regionOneRowKeys regionFourRowKeys
    exact mappedRowKeys_disjoint_of_ne (by decide) _ _
  have hzeroFive : List.Disjoint regionZeroRowKeys regionFiveRowKeys := by
    unfold regionZeroRowKeys regionFiveRowKeys
    exact mappedRowKeys_disjoint_of_ne (by decide) _ _
  have honeFive : List.Disjoint regionOneRowKeys regionFiveRowKeys := by
    unfold regionOneRowKeys regionFiveRowKeys
    exact mappedRowKeys_disjoint_of_ne (by decide) _ _
  have hfourFive : List.Disjoint regionFourRowKeys regionFiveRowKeys := by
    unfold regionFourRowKeys regionFiveRowKeys
    exact mappedRowKeys_disjoint_of_ne (by decide) _ _
  have hzeroOneNodup :=
    regionZeroRowKeys_nodup.append regionOneRowKeys_nodup hzeroOne
  have hzeroOneFourNodup := hzeroOneNodup.append regionFourRowKeys_nodup
    (disjoint_append_left hzeroFour honeFour)
  exact hzeroOneFourNodup.append regionFiveRowKeys_nodup
    (disjoint_append_left (disjoint_append_left hzeroFive honeFive) hfourFive)

/-! ## Complete exceptional-reader mask -/

/-- The 57 exceptional-reader rows in region one. -/
def regionOneMixedModeRecords : List ModeRecord :=
  [⟨(1, 2), ⟨1, 3, 12⟩, .modeA⟩,
    ⟨(1, 3), ⟨1, 4, 11⟩, .modeA⟩,
    ⟨(1, 4), ⟨1, 5, 10⟩, .modeA⟩,
    ⟨(1, 5), ⟨1, 6, 9⟩, .modeA⟩,
    ⟨(1, 6), ⟨1, 7, 8⟩, .modeB⟩,
    ⟨(1, 7), ⟨1, 8, 7⟩, .modeA⟩,
    ⟨(1, 8), ⟨1, 9, 6⟩, .modeA⟩,
    ⟨(1, 9), ⟨1, 10, 5⟩, .modeA⟩,
    ⟨(1, 10), ⟨1, 11, 4⟩, .modeA⟩,
    ⟨(1, 16), ⟨2, 3, 11⟩, .modeB⟩,
    ⟨(1, 17), ⟨2, 4, 10⟩, .modeA⟩,
    ⟨(1, 18), ⟨2, 5, 9⟩, .modeA⟩,
    ⟨(1, 19), ⟨2, 6, 8⟩, .modeA⟩,
    ⟨(1, 20), ⟨2, 7, 7⟩, .modeA⟩,
    ⟨(1, 21), ⟨2, 8, 6⟩, .modeA⟩,
    ⟨(1, 22), ⟨2, 9, 5⟩, .modeA⟩,
    ⟨(1, 23), ⟨2, 10, 4⟩, .modeA⟩,
    ⟨(1, 24), ⟨2, 11, 3⟩, .modeB⟩,
    ⟨(1, 25), ⟨2, 12, 2⟩, .modeA⟩,
    ⟨(1, 28), ⟨3, 2, 11⟩, .modeA⟩,
    ⟨(1, 29), ⟨3, 3, 10⟩, .modeA⟩,
    ⟨(1, 30), ⟨3, 4, 9⟩, .modeA⟩,
    ⟨(1, 31), ⟨3, 5, 8⟩, .modeA⟩,
    ⟨(1, 32), ⟨3, 6, 7⟩, .modeA⟩,
    ⟨(1, 33), ⟨3, 7, 6⟩, .modeA⟩,
    ⟨(1, 34), ⟨3, 8, 5⟩, .modeA⟩,
    ⟨(1, 35), ⟨3, 9, 4⟩, .modeA⟩,
    ⟨(1, 36), ⟨3, 10, 3⟩, .modeA⟩,
    ⟨(1, 37), ⟨3, 11, 2⟩, .modeA⟩,
    ⟨(1, 40), ⟨4, 2, 10⟩, .modeA⟩,
    ⟨(1, 41), ⟨4, 3, 9⟩, .modeA⟩,
    ⟨(1, 42), ⟨4, 4, 8⟩, .modeB⟩,
    ⟨(1, 43), ⟨4, 5, 7⟩, .modeB⟩,
    ⟨(1, 44), ⟨4, 6, 6⟩, .modeB⟩,
    ⟨(1, 45), ⟨4, 7, 5⟩, .modeA⟩,
    ⟨(1, 46), ⟨4, 8, 4⟩, .modeA⟩,
    ⟨(1, 47), ⟨4, 9, 3⟩, .modeA⟩,
    ⟨(1, 48), ⟨4, 10, 2⟩, .modeB⟩,
    ⟨(1, 49), ⟨4, 11, 1⟩, .modeA⟩,
    ⟨(1, 51), ⟨5, 2, 9⟩, .modeA⟩,
    ⟨(1, 52), ⟨5, 3, 8⟩, .modeB⟩,
    ⟨(1, 53), ⟨5, 4, 7⟩, .modeB⟩,
    ⟨(1, 54), ⟨5, 5, 6⟩, .modeB⟩,
    ⟨(1, 55), ⟨5, 6, 5⟩, .modeA⟩,
    ⟨(1, 56), ⟨5, 7, 4⟩, .modeA⟩,
    ⟨(1, 57), ⟨5, 8, 3⟩, .modeA⟩,
    ⟨(1, 58), ⟨5, 9, 2⟩, .modeA⟩,
    ⟨(1, 59), ⟨5, 10, 1⟩, .modeB⟩,
    ⟨(1, 62), ⟨6, 3, 7⟩, .modeA⟩,
    ⟨(1, 63), ⟨6, 4, 6⟩, .modeB⟩,
    ⟨(1, 64), ⟨6, 5, 5⟩, .modeB⟩,
    ⟨(1, 65), ⟨6, 6, 4⟩, .modeA⟩,
    ⟨(1, 66), ⟨6, 7, 3⟩, .modeB⟩,
    ⟨(1, 72), ⟨7, 4, 5⟩, .modeA⟩,
    ⟨(1, 73), ⟨7, 5, 4⟩, .modeA⟩,
    ⟨(1, 74), ⟨7, 6, 3⟩, .modeA⟩,
    ⟨(1, 80), ⟨8, 4, 4⟩, .modeA⟩]

/-- The three exceptional-reader rows in region four. -/
def regionFourMixedModeRecords : List ModeRecord :=
  [⟨(4, 20), ⟨2, 7, 7⟩, .modeA⟩,
    ⟨(4, 32), ⟨3, 6, 7⟩, .modeB⟩,
    ⟨(4, 33), ⟨3, 7, 6⟩, .modeA⟩]

/-- Region one contributes 57 exceptional-reader mask records. -/
theorem regionOneMixedModeRecords_length : regionOneMixedModeRecords.length = 57 := by decide

/-- Region four contributes three exceptional-reader mask records. -/
theorem regionFourMixedModeRecords_length : regionFourMixedModeRecords.length = 3 := by decide

/-- Every region-one mask record is active and stores its committed positive-parent shape. -/
theorem regionOneMixedModeRecords_valid :
    ∀ record ∈ regionOneMixedModeRecords,
      record.key.1 = 1 ∧
        record.key ∈ regionOneRowKeys ∧
        record.shape = positiveLevelFourShape record.key.2 := by
  decide

/-- Every region-four mask record is active and stores its committed positive-parent shape. -/
theorem regionFourMixedModeRecords_valid :
    ∀ record ∈ regionFourMixedModeRecords,
      record.key.1 = 4 ∧
        record.key ∈ regionFourRowKeys ∧
        record.shape = positiveLevelFourShape record.key.2 := by
  decide

/-- Complete exceptional-reader mask, in lexicographic key order. -/
def mixedModeRecords : List ModeRecord :=
  regionOneMixedModeRecords ++ regionFourMixedModeRecords

/-- The complete exceptional-reader mask contains 60 records. -/
theorem mixedModeRecords_length : mixedModeRecords.length = 60 := by
  simp only [mixedModeRecords, List.length_append, regionOneMixedModeRecords_length,
    regionFourMixedModeRecords_length]

/-- Keys carrying either exceptional reader. -/
def mixedRowKeys : List RowKey :=
  regionOneMixedModeRecords.map (fun record ↦ record.key) ++
    regionFourMixedModeRecords.map (fun record ↦ record.key)

/-- Every exceptional-reader key occurs exactly once. -/
theorem mixedRowKeys_nodup : mixedRowKeys.Nodup := by decide

/-- Every exceptional-reader key is an active q20 row. -/
theorem mixedRowKeys_subset_active : ∀ key ∈ mixedRowKeys, key ∈ activeRowKeys := by
  intro key hkey
  rw [mixedRowKeys, List.mem_append] at hkey
  rcases hkey with hkey | hkey
  · rcases List.mem_map.mp hkey with ⟨record, hrecord, rfl⟩
    have hvalid := regionOneMixedModeRecords_valid record hrecord
    rw [activeRowKeys, List.mem_append, List.mem_append, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hvalid.2.1))
  · rcases List.mem_map.mp hkey with ⟨record, hrecord, rfl⟩
    have hvalid := regionFourMixedModeRecords_valid record hrecord
    rw [activeRowKeys, List.mem_append, List.mem_append, List.mem_append]
    exact Or.inl (Or.inr hvalid.2.1)

/-- The fifteen keys assigned the raw-cyclic reader (Mode B). -/
def modeBRowKeys : List RowKey :=
  (mixedModeRecords.filter fun record ↦ decide (record.mode = .modeB)).map
    fun record ↦ record.key

/-- Exactly 15 mask records select Mode B. -/
theorem modeBRowKeys_length : modeBRowKeys.length = 15 := by decide

/-- Every Mode-B key belongs to the active schedule. -/
theorem modeBRowKeys_subset_active : ∀ key ∈ modeBRowKeys, key ∈ activeRowKeys := by
  intro key hkey
  rw [modeBRowKeys] at hkey
  rcases List.mem_map.mp hkey with ⟨record, hrecord, rfl⟩
  have hmixed : record ∈ mixedModeRecords := (List.mem_filter.mp hrecord).1
  rw [mixedModeRecords, List.mem_append] at hmixed
  apply mixedRowKeys_subset_active
  rw [mixedRowKeys, List.mem_append]
  rcases hmixed with hmixed | hmixed
  · exact Or.inl (List.mem_map.mpr ⟨record, hmixed, rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨record, hmixed, rfl⟩)

private def modeForActiveKey (key : RowKey) : RowMode :=
  if key ∈ modeBRowKeys then .modeB else .modeA

private def actionForActiveKey (key : RowKey) : RowAction :=
  if key ∈ modeBRowKeys then .rawCyclic
  else if key ∈ mixedRowKeys then .rawIdentity
  else .ordinaryFeature

/-- Fail-closed mode lookup: inactive keys receive no schedule assignment. -/
def modeOfKey (key : RowKey) : Option RowMode :=
  if key ∈ activeRowKeys then some (modeForActiveKey key) else none

/-- Fail-closed checker-action lookup: inactive keys receive no action. -/
def actionOfKey (key : RowKey) : Option RowAction :=
  if key ∈ activeRowKeys then some (actionForActiveKey key) else none

/-- Mode lookup fails exactly on keys outside the active schedule. -/
theorem modeOfKey_eq_none_iff (key : RowKey) :
    modeOfKey key = none ↔ key ∉ activeRowKeys := by
  simp [modeOfKey]

/-- Checker-action lookup fails exactly on keys outside the active schedule. -/
theorem actionOfKey_eq_none_iff (key : RowKey) :
    actionOfKey key = none ↔ key ∉ activeRowKeys := by
  simp [actionOfKey]

/-- Canonical active key at a global row index. -/
def rowKey (row : Fin 225) : RowKey :=
  activeRowKeys.get ⟨row.val, by
    rw [activeRowKeys_length]
    exact row.isLt⟩

/-- Every globally indexed row returns a member of the active schedule. -/
theorem rowKey_mem_active (row : Fin 225) : rowKey row ∈ activeRowKeys := by
  exact List.get_mem activeRowKeys _

/-- Assembly mode at a global active-row index. -/
def rowMode (row : Fin 225) : RowMode := modeForActiveKey (rowKey row)

/-- Exact checker branch at a global active-row index. -/
def rowAction (row : Fin 225) : RowAction := actionForActiveKey (rowKey row)

/-- Fail-closed key lookup recovers the indexed row's mode. -/
theorem modeOfKey_rowKey (row : Fin 225) :
    modeOfKey (rowKey row) = some (rowMode row) := by
  simp [modeOfKey, rowMode, rowKey_mem_active]

/-- Fail-closed key lookup recovers the indexed row's checker action. -/
theorem actionOfKey_rowKey (row : Fin 225) :
    actionOfKey (rowKey row) = some (rowAction row) := by
  simp [actionOfKey, rowAction, rowKey_mem_active]

/-- The checker action at every indexed row collapses to its advertised assembly mode. -/
theorem rowAction_mode (row : Fin 225) : (rowAction row).mode = rowMode row := by
  unfold rowAction rowMode actionForActiveKey modeForActiveKey
  by_cases hcyclic : rowKey row ∈ modeBRowKeys
  · simp [hcyclic, RowAction.mode]
  · by_cases hmixed : rowKey row ∈ mixedRowKeys <;>
      simp [hcyclic, hmixed, RowAction.mode]

/-! ## Regional and global exact counts -/

/-- Number of active rows in a root region. -/
def regionalRowCount (region : Fin 6) : Nat := (regionalRowKeys region).length

/-- Number of Mode-A rows in a root region. -/
def regionalModeACount (region : Fin 6) : Nat :=
  ((regionalRowKeys region).map modeForActiveKey).count .modeA

/-- Number of Mode-B rows in a root region. -/
def regionalModeBCount (region : Fin 6) : Nat :=
  ((regionalRowKeys region).map modeForActiveKey).count .modeB

/-- Number of rows choosing one literal checker action in a root region. -/
def regionalActionCount (region : Fin 6) (action : RowAction) : Nat :=
  ((regionalRowKeys region).map actionForActiveKey).count action

/-- Region zero's active-row count is 39. -/
theorem regionalRowCount_zero : regionalRowCount 0 = 39 := by decide
/-- Region one's active-row count is 102. -/
theorem regionalRowCount_one : regionalRowCount 1 = 102 := by decide
/-- Region two's active-row count is zero. -/
theorem regionalRowCount_two : regionalRowCount 2 = 0 := by decide
/-- Region three's active-row count is zero. -/
theorem regionalRowCount_three : regionalRowCount 3 = 0 := by decide
/-- Region four's active-row count is 48. -/
theorem regionalRowCount_four : regionalRowCount 4 = 48 := by decide
/-- Region five's active-row count is 36. -/
theorem regionalRowCount_five : regionalRowCount 5 = 36 := by decide

/-- All 39 rows in region zero use Mode A. -/
theorem regionalModeACount_zero : regionalModeACount 0 = 39 := by decide
/-- Exactly 88 rows in region one use Mode A. -/
theorem regionalModeACount_one : regionalModeACount 1 = 88 := by decide
/-- Region two has no Mode-A row. -/
theorem regionalModeACount_two : regionalModeACount 2 = 0 := by decide
/-- Region three has no Mode-A row. -/
theorem regionalModeACount_three : regionalModeACount 3 = 0 := by decide
/-- Exactly 47 rows in region four use Mode A. -/
theorem regionalModeACount_four : regionalModeACount 4 = 47 := by decide
/-- All 36 rows in region five use Mode A. -/
theorem regionalModeACount_five : regionalModeACount 5 = 36 := by decide

/-- Region zero has no Mode-B row. -/
theorem regionalModeBCount_zero : regionalModeBCount 0 = 0 := by decide
/-- Exactly 14 rows in region one use Mode B. -/
theorem regionalModeBCount_one : regionalModeBCount 1 = 14 := by decide
/-- Region two has no Mode-B row. -/
theorem regionalModeBCount_two : regionalModeBCount 2 = 0 := by decide
/-- Region three has no Mode-B row. -/
theorem regionalModeBCount_three : regionalModeBCount 3 = 0 := by decide
/-- Exactly one row in region four uses Mode B. -/
theorem regionalModeBCount_four : regionalModeBCount 4 = 1 := by decide
/-- Region five has no Mode-B row. -/
theorem regionalModeBCount_five : regionalModeBCount 5 = 0 := by decide

/-- Region zero has 39 ordinary rows and no exceptional-reader row. -/
theorem regionalActionCounts_zero :
    regionalActionCount 0 .ordinaryFeature = 39 ∧
      regionalActionCount 0 .rawIdentity = 0 ∧
      regionalActionCount 0 .rawCyclic = 0 := by
  decide

/-- Region one has 45 ordinary, 43 raw-identity, and 14 raw-cyclic rows. -/
theorem regionalActionCounts_one :
    regionalActionCount 1 .ordinaryFeature = 45 ∧
      regionalActionCount 1 .rawIdentity = 43 ∧
      regionalActionCount 1 .rawCyclic = 14 := by
  decide

/-- Empty region two has zero rows in every checker-action class. -/
theorem regionalActionCounts_two :
    regionalActionCount 2 .ordinaryFeature = 0 ∧
      regionalActionCount 2 .rawIdentity = 0 ∧
      regionalActionCount 2 .rawCyclic = 0 := by
  decide

/-- Empty region three has zero rows in every checker-action class. -/
theorem regionalActionCounts_three :
    regionalActionCount 3 .ordinaryFeature = 0 ∧
      regionalActionCount 3 .rawIdentity = 0 ∧
      regionalActionCount 3 .rawCyclic = 0 := by
  decide

/-- Region four has 45 ordinary, two raw-identity, and one raw-cyclic row. -/
theorem regionalActionCounts_four :
    regionalActionCount 4 .ordinaryFeature = 45 ∧
      regionalActionCount 4 .rawIdentity = 2 ∧
      regionalActionCount 4 .rawCyclic = 1 := by
  decide

/-- Region five has 36 ordinary rows and no exceptional-reader row. -/
theorem regionalActionCounts_five :
    regionalActionCount 5 .ordinaryFeature = 36 ∧
      regionalActionCount 5 .rawIdentity = 0 ∧
      regionalActionCount 5 .rawCyclic = 0 := by
  decide

/-- Summing the six regional counts gives 210 Mode-A and 15 Mode-B rows. -/
theorem totalModeCounts :
    regionalModeACount 0 + regionalModeACount 1 + regionalModeACount 2 +
        regionalModeACount 3 + regionalModeACount 4 + regionalModeACount 5 = 210 ∧
      regionalModeBCount 0 + regionalModeBCount 1 + regionalModeBCount 2 +
        regionalModeBCount 3 + regionalModeBCount 4 + regionalModeBCount 5 = 15 := by
  rw [regionalModeACount_zero, regionalModeACount_one, regionalModeACount_two,
    regionalModeACount_three, regionalModeACount_four, regionalModeACount_five,
    regionalModeBCount_zero, regionalModeBCount_one, regionalModeBCount_two,
    regionalModeBCount_three, regionalModeBCount_four, regionalModeBCount_five]
  exact ⟨rfl, rfl⟩

/-- Summing the regional checker branches gives the exact `165/45/15` partition. -/
theorem totalActionCounts :
    regionalActionCount 0 .ordinaryFeature + regionalActionCount 1 .ordinaryFeature +
        regionalActionCount 2 .ordinaryFeature + regionalActionCount 3 .ordinaryFeature +
        regionalActionCount 4 .ordinaryFeature + regionalActionCount 5 .ordinaryFeature = 165 ∧
      regionalActionCount 0 .rawIdentity + regionalActionCount 1 .rawIdentity +
        regionalActionCount 2 .rawIdentity + regionalActionCount 3 .rawIdentity +
        regionalActionCount 4 .rawIdentity + regionalActionCount 5 .rawIdentity = 45 ∧
      regionalActionCount 0 .rawCyclic + regionalActionCount 1 .rawCyclic +
        regionalActionCount 2 .rawCyclic + regionalActionCount 3 .rawCyclic +
        regionalActionCount 4 .rawCyclic + regionalActionCount 5 .rawCyclic = 15 := by
  rw [(regionalActionCounts_zero).1, (regionalActionCounts_one).1,
    (regionalActionCounts_two).1, (regionalActionCounts_three).1,
    (regionalActionCounts_four).1, (regionalActionCounts_five).1,
    (regionalActionCounts_zero).2.1, (regionalActionCounts_one).2.1,
    (regionalActionCounts_two).2.1, (regionalActionCounts_three).2.1,
    (regionalActionCounts_four).2.1, (regionalActionCounts_five).2.1,
    (regionalActionCounts_zero).2.2, (regionalActionCounts_one).2.2,
    (regionalActionCounts_two).2.2, (regionalActionCounts_three).2.2,
    (regionalActionCounts_four).2.2, (regionalActionCounts_five).2.2]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Literal row-44 handoff used by the first semantic client -/

/-- Zero-based global row 44 has region-one parent index six. -/
theorem row44_key : rowKey 44 = ((1, 6) : RowKey) := by decide

/-- Zero-based global row 44 is assigned Mode B. -/
theorem row44_mode : rowMode 44 = .modeB := by decide

/-- Zero-based global row 44 selects the raw-cyclic checker branch. -/
theorem row44_action : rowAction 44 = .rawCyclic := by decide

/-- Zero-based global row 44 has positive parent shape `(1, 7, 8)`. -/
theorem row44_parentShape :
    positiveLevelFourShape (rowKey 44).2 = ⟨1, 7, 8⟩ := by
  decide

end MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule
