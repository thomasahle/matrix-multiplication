/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Tactic.FinCases
import MatrixMultiplication.Generated.LegalHybridQ20PrimaryData
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryPos3AData0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero3Data0
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry
import MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
import MatrixMultiplication.SparseTopBranchSupport

set_option autoImplicit false

/-!
# Both labelled children of the actual q20 top support have stored reference rows

The ordered split and its two child laws are defined in [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47,115-146`. This module checks the finite row
support needed to instantiate Total-Weight's common approximate-input construction,
`better_bound/paper.tex:1085-1124`, for this project's own q20 certificate. The candidate status is
described at `better_bound/paper.tex:148-159`; its source law and fixed schedule are recorded
in `better_bound/legal_hybrid/README.md`. No unpublished parameter assignment from
[alman2025more] is used.

An active positive-parent atom is decoded in the committed left-major ordered-pair convention.
Each labelled child separately requires either its positive shape/region row in the stored A3
field, or its nonpositive shape/region row in the stored zero-three field. Self-complementary
pairs retain both labelled obligations. Neither closure of the alpha support under complement
nor equality of an old top law or a positive beta cache is assumed.

Proof sketch: check at most 32 addresses from one native q20 block at a time; each native block
has at most 200 entries. A certified 119-entry child-index table supplies each pair lookup.
Transporting the decision procedure through its correctness equivalence keeps the full ordered-pair
list out of evaluation. Compose the fragments using list splitting, not payload reduction.
The sparse reconstruction theorem associates every active slot with an actual source address.
Only `PrimaryTables.top` is constrained. Lower-law normalization and supported joint references
are separate consumers of the resulting row-membership facts. No dense table is evaluated here,
and no assembled tensor restriction, compatibility cleanup, hole repair, or exponent is claimed.
-/

namespace MatrixMultiplication.LegalHybridQ20TopSupportCoverage

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.Generated.LegalHybridQ20Primary
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SparseTopBranchSupport

/-- The 75 positive shape/region addresses in the actual shared lower A3 field. -/
def positiveChildRowAddresses : List ℕ :=
  [1, 6, 7, 10, 11, 12, 13, 16, 17, 18, 19, 22, 23, 24,
    25, 28, 29, 31, 36, 37, 40, 41, 42, 43, 46, 47, 48, 49,
    52, 53, 54, 55, 58, 59, 60, 61, 64, 65, 66, 67, 70, 71,
    72, 73, 76, 77, 78, 79, 82, 83, 84, 85, 88, 89, 90, 91,
    94, 95, 96, 97, 100, 101, 102, 103, 106, 107, 108, 109,
    112, 113, 114, 115, 118, 119, 121]

/-- The small positive address list is precisely the stored A3 row projection. -/
theorem positiveChildRowAddresses_eq_pos3ARows :
    positiveChildRowAddresses =
      Generated.PairedTotalWeightPrimary.Pos3AData0.data.rowIndices.toList := by
  rw [Generated.PairedTotalWeightPrimary.Pos3AData0.data_eq_rawData]
  rfl

/-- The 28 nonpositive shape/region addresses in the actual shared lower zero-three field. -/
def boundaryChildRowAddresses : List ℕ :=
  [1, 7, 13, 19, 25, 28, 31, 37, 43, 49, 55, 97, 103, 139,
    145, 175, 180, 181, 184, 205, 208, 211, 229, 235, 247, 253, 259, 265]

/-- The small boundary address list is precisely the stored zero-three row projection. -/
theorem boundaryChildRowAddresses_eq_zero3Rows :
    boundaryChildRowAddresses =
      Generated.PairedTotalWeightPrimary.Zero3Data0.data.rowIndices.toList := by
  rw [Generated.PairedTotalWeightPrimary.Zero3Data0.data_eq_rawData]
  rfl

/-- Flat ordered-pair index decoded from one positive-parent q20 atom. -/
def topAtomPairIndex (atom : ℕ) : Fin levelFourPairCount :=
  ⟨(atom - topZeroAtomCount) % topPairCount, by
    simp only [topPairCount, levelFourPairCount]
    exact Nat.mod_lt _ (by norm_num)⟩

/-- Incoming region decoded from one positive-parent q20 atom. -/
def topAtomRegion (atom : ℕ) : Fin 6 :=
  ⟨((atom - topZeroAtomCount) / topPairCount) % 6, Nat.mod_lt _ (by norm_num)⟩

/-- Stored-row coverage for one physical child; its two positivity cases use distinct fields. -/
def ChildRowCovered (shape : Shape) (region : Fin 6) : Prop :=
  (shape.IsPositive →
    (positiveShapes 8).idxOf shape * regionCount + region.val ∈ positiveChildRowAddresses) ∧
  (¬shape.IsPositive →
    shapeEightIndex shape * regionCount + region.val ∈ boundaryChildRowAddresses)

/-- Coverage is decided from a child's three coordinates and the two finite row-address lists. -/
instance childRowCoveredDecidable (shape : Shape) (region : Fin 6) :
    Decidable (ChildRowCovered shape region) := by
  unfold ChildRowCovered
  infer_instance

/-- Both labelled children of a positive-parent atom are covered; top boundary atoms are omitted.
The conjunction deliberately keeps two obligations when the children coincide. -/
def TopAtomRowsCovered (atom : ℕ) : Prop :=
  if topZeroAtomCount ≤ atom then
    let pair := levelFourPair (topAtomPairIndex atom)
    ChildRowCovered pair.1 (topAtomRegion atom) ∧ ChildRowCovered pair.2 (topAtomRegion atom)
  else True

/-- The committed geometry certificates use the same left-major ordered pairs; this dispatch
selects one literal 119-entry child-index table without evaluating the semantic pair list. -/
private def pairIndexBlock (block : Fin 15) : List (ℕ × ℕ) :=
  match block.val with
  | 0 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk0.expectedIndices
  | 1 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk1.expectedIndices
  | 2 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk2.expectedIndices
  | 3 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk3.expectedIndices
  | 4 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk4.expectedIndices
  | 5 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk5.expectedIndices
  | 6 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk6.expectedIndices
  | 7 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk7.expectedIndices
  | 8 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk8.expectedIndices
  | 9 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk9.expectedIndices
  | 10 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk10.expectedIndices
  | 11 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk11.expectedIndices
  | 12 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk12.expectedIndices
  | 13 => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk13.expectedIndices
  | _ => Generated.SimplifiedVolumeRecurrence.PairGeometryChunk14.expectedIndices

/-- Each dispatched table is its certified consecutive window of the semantic geometry. -/
private theorem pairIndexBlock_eq (block : Fin 15) :
    pairIndexBlock block = computedPairShapeIndexRange (119 * block.val) 119 := by
  fin_cases block
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk0.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk1.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk2.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk3.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk4.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk5.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk6.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk7.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk8.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk9.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk10.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk11.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk12.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk13.recurrence_eq.symm
  · exact Generated.SimplifiedVolumeRecurrence.PairGeometryChunk14.recurrence_eq.symm

/-- Decode a pair index using quotient-selected chunk and remainder-selected entry. -/
private def fastPairIndices (pair : Fin levelFourPairCount) : ℕ × ℕ :=
  (pairIndexBlock ⟨pair.val / 119, by
    have hpair := pair.isLt
    simp only [levelFourPairCount] at hpair
    omega⟩)[pair.val % 119]?.getD default

/-- Quotient/remainder indexing recovers both physical child-shape indices. -/
private theorem fastPairIndices_eq (pair : Fin levelFourPairCount) :
    fastPairIndices pair =
      (shapeEightIndex (levelFourPair pair).1, shapeEightIndex (levelFourPair pair).2) := by
  have hmod : pair.val % 119 < 119 := Nat.mod_lt _ (by decide)
  have hpair : pair.val < levelFourPairs.length := by
    rw [levelFourPairs_length]
    exact pair.isLt
  unfold fastPairIndices
  rw [pairIndexBlock_eq]
  unfold computedPairShapeIndexRange
  rw [List.getElem?_map, List.getElem?_take_of_lt hmod, List.getElem?_drop,
    Nat.div_add_mod, List.getElem?_eq_getElem hpair]
  rfl

/-- Read a child shape from the small 45-shape alphabet. -/
private def shapeAtIndex (index : ℕ) : Shape := (shapes 8)[index]?.getD default

/-- The small-alphabet lookup inverts the stored child-shape index. -/
private theorem shapeAtIndex_shapeEightIndex (shape : Shape) (htotal : shape.total = 8) :
    shapeAtIndex (shapeEightIndex shape) = shape := by
  unfold shapeAtIndex shapeEightIndex
  rw [List.getElem?_idxOf (mem_shapes_iff_total.mpr htotal)]
  rfl

/-- Computational child pair, with no call to the semantic ordered-pair constructor. -/
private def fastPair (pair : Fin levelFourPairCount) : Shape × Shape :=
  let indices := fastPairIndices pair
  (shapeAtIndex indices.1, shapeAtIndex indices.2)

/-- Both labelled children agree with the semantic pair, including when they coincide. -/
private theorem fastPair_eq (pair : Fin levelFourPairCount) :
    fastPair pair = levelFourPair pair := by
  unfold fastPair
  rw [fastPairIndices_eq]
  change (shapeAtIndex (shapeEightIndex (levelFourPair pair).1),
    shapeAtIndex (shapeEightIndex (levelFourPair pair).2)) = levelFourPair pair
  rw [shapeAtIndex_shapeEightIndex _ (levelFourPair_geometry pair).1,
    shapeAtIndex_shapeEightIndex _ (levelFourPair_geometry pair).2.1]

/-- The same child-row predicate, evaluated through the certified small-table lookup. -/
private def topAtomRowsCoveredFast (atom : ℕ) : Prop :=
  if topZeroAtomCount ≤ atom then
    let pair := fastPair (topAtomPairIndex atom)
    ChildRowCovered pair.1 (topAtomRegion atom) ∧ ChildRowCovered pair.2 (topAtomRegion atom)
  else True

/-- Computational coverage, using the core conditional decision without equality casts. -/
private instance topAtomRowsCoveredFastDecidable (atom : ℕ) :
    Decidable (topAtomRowsCoveredFast atom) := by
  unfold topAtomRowsCoveredFast
  infer_instance

/-- Correctness transport is a proposition, hence opaque to Boolean evaluation. -/
private theorem topAtomRowsCoveredFast_iff (atom : ℕ) :
    topAtomRowsCoveredFast atom ↔ TopAtomRowsCovered atom := by
  simp only [topAtomRowsCoveredFast, TopAtomRowsCovered, fastPair_eq]

/-- Atom coverage uses certified small pair tables and the two labelled child decisions.
The equivalence proof occurs only in proof fields, never in the Boolean computation. -/
instance topAtomRowsCoveredDecidable (atom : ℕ) : Decidable (TopAtomRowsCovered atom) := by
  exact decidable_of_iff (topAtomRowsCoveredFast atom) (topAtomRowsCoveredFast_iff atom)

/-- Boolean support-only check for a bounded address fragment, with no numerator reduction. -/
def topAtomRowsCoveredCheck (atoms : List ℕ) : Bool :=
  atoms.all fun atom ↦ decide (TopAtomRowsCovered atom)

/-- The twelve native source blocks, before the two public q20 chunks are concatenated. -/
def topAtomBlock (block : Fin 12) : List ℕ :=
  match block.val with
  | 0 => TopData0.DataBlock0.data.atomIndices.toList
  | 1 => TopData0.DataBlock1.data.atomIndices.toList
  | 2 => TopData0.DataBlock2.data.atomIndices.toList
  | 3 => TopData0.DataBlock3.data.atomIndices.toList
  | 4 => TopData0.DataBlock4.data.atomIndices.toList
  | 5 => TopData0.DataBlock5.data.atomIndices.toList
  | 6 => TopData0.DataBlock6.data.atomIndices.toList
  | 7 => TopData0.DataBlock7.data.atomIndices.toList
  | 8 => TopData1.DataBlock0.data.atomIndices.toList
  | 9 => TopData1.DataBlock1.data.atomIndices.toList
  | 10 => TopData1.DataBlock2.data.atomIndices.toList
  | _ => TopData1.DataBlock3.data.atomIndices.toList

/-- One of seven consecutive fragments of a native block, each containing at most 32 addresses. -/
def topAtomShard (block : Fin 12) (shard : Fin 7) : List ℕ :=
  ((topAtomBlock block).drop (32 * shard.val)).take 32

/-- Native alignment and count certificates bound the address length without reading the payload. -/
private theorem nativeAtomLength_le
    {data : Generated.SimplifiedVolume.SparseMassChunk} {ambient lower upper : ℕ}
    (hvalid : data.IsValid ambient lower upper) (hcount : data.valueCount ≤ 224) :
    data.atomIndices.toList.length ≤ 224 := by
  rw [Array.length_toList, hvalid.1]
  exact hcount

/-- Every native q20 address block fits in seven 32-entry fragments. -/
private theorem topAtomBlock_length_le (block : Fin 12) :
    (topAtomBlock block).length ≤ 224 := by
  fin_cases block
  · exact nativeAtomLength_le TopData0.DataBlock0.data_isValid
      (TopData0.DataBlock0.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData0.DataBlock1.data_isValid
      (TopData0.DataBlock1.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData0.DataBlock2.data_isValid
      (TopData0.DataBlock2.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData0.DataBlock3.data_isValid
      (TopData0.DataBlock3.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData0.DataBlock4.data_isValid
      (TopData0.DataBlock4.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData0.DataBlock5.data_isValid
      (TopData0.DataBlock5.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData0.DataBlock6.data_isValid
      (TopData0.DataBlock6.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData0.DataBlock7.data_isValid
      (TopData0.DataBlock7.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData1.DataBlock0.data_isValid
      (TopData1.DataBlock0.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData1.DataBlock1.data_isValid
      (TopData1.DataBlock1.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData1.DataBlock2.data_isValid
      (TopData1.DataBlock2.valueCount_eq.trans_le (by decide))
  · exact nativeAtomLength_le TopData1.DataBlock3.data_isValid
      (TopData1.DataBlock3.valueCount_eq.trans_le (by decide))

/-- Seven consecutive slices reconstruct a bounded list by the take/drop identity. -/
private theorem sevenShards_flatten (atoms : List ℕ) (hlen : atoms.length ≤ 224) :
    (List.ofFn fun shard : Fin 7 ↦ (atoms.drop (32 * shard.val)).take 32).flatten =
      atoms := by
  have hdrop : atoms.drop 224 = [] := List.drop_eq_nil_of_le hlen
  have hsplit (offset : ℕ) :
      (atoms.drop offset).take 32 ++ atoms.drop (offset + 32) = atoms.drop offset := by
    simpa only [List.drop_drop] using List.take_append_drop 32 (atoms.drop offset)
  change (atoms.drop 0).take 32 ++ ((atoms.drop 32).take 32 ++
    ((atoms.drop 64).take 32 ++ ((atoms.drop 96).take 32 ++
    ((atoms.drop 128).take 32 ++ ((atoms.drop 160).take 32 ++
    ((atoms.drop 192).take 32 ++ [])))))) = atoms
  calc
    _ = ((atoms.drop 0).take 32 ++ (atoms.drop 32).take 32 ++
        (atoms.drop 64).take 32 ++ (atoms.drop 96).take 32 ++
        (atoms.drop 128).take 32 ++ (atoms.drop 160).take 32 ++
        (atoms.drop 192).take 32) ++ atoms.drop 224 := by
      simp only [hdrop, List.append_nil, List.append_assoc]
    _ = atoms := by
      simp only [List.append_assoc]
      rw [hsplit 192, hsplit 160, hsplit 128, hsplit 96, hsplit 64, hsplit 32,
        hsplit 0, List.drop_zero]

/-- The small fragments cover each native source block exactly, without a global payload slice. -/
theorem topAtomShards_flatten (block : Fin 12) :
    (List.ofFn (topAtomShard block)).flatten = topAtomBlock block := by
  exact sevenShards_flatten (topAtomBlock block) (topAtomBlock_length_le block)

/-- Both labelled child rows are covered on each fragment of native q20 block 0. -/
theorem topAtomBlock0_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨0, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 1. -/
theorem topAtomBlock1_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨1, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 2. -/
theorem topAtomBlock2_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨2, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 3. -/
theorem topAtomBlock3_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨3, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 4. -/
theorem topAtomBlock4_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨4, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 5. -/
theorem topAtomBlock5_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨5, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 6. -/
theorem topAtomBlock6_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨6, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 7. -/
theorem topAtomBlock7_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨7, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 8. -/
theorem topAtomBlock8_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨8, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 9. -/
theorem topAtomBlock9_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨9, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 10. -/
theorem topAtomBlock10_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨10, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- Both labelled child rows are covered on each fragment of native q20 block 11. -/
theorem topAtomBlock11_shard_checked (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard ⟨11, by decide⟩ shard) = true := by
  fin_cases shard <;> decide +kernel

/-- All bounded native-block checks compose without another payload reduction. -/
theorem topAtomShard_checked (block : Fin 12) (shard : Fin 7) :
    topAtomRowsCoveredCheck (topAtomShard block shard) = true := by
  fin_cases block
  · exact topAtomBlock0_shard_checked shard
  · exact topAtomBlock1_shard_checked shard
  · exact topAtomBlock2_shard_checked shard
  · exact topAtomBlock3_shard_checked shard
  · exact topAtomBlock4_shard_checked shard
  · exact topAtomBlock5_shard_checked shard
  · exact topAtomBlock6_shard_checked shard
  · exact topAtomBlock7_shard_checked shard
  · exact topAtomBlock8_shard_checked shard
  · exact topAtomBlock9_shard_checked shard
  · exact topAtomBlock10_shard_checked shard
  · exact topAtomBlock11_shard_checked shard

/-- The source support is exactly the concatenation of the twelve native address blocks.
Only array/list append identities are used, not a check of all 2,244 addresses. -/
theorem topSupportAtomIndices_eq_blocks :
    topSupportAtomIndices = (List.ofFn topAtomBlock).flatten := by
  unfold topSupportAtomIndices
  rw [TopData0.data_eq_rawData, TopData1.data_eq_rawData]
  change _ =
    TopData0.DataBlock0.data.atomIndices.toList ++
    (TopData0.DataBlock1.data.atomIndices.toList ++
    (TopData0.DataBlock2.data.atomIndices.toList ++
    (TopData0.DataBlock3.data.atomIndices.toList ++
    (TopData0.DataBlock4.data.atomIndices.toList ++
    (TopData0.DataBlock5.data.atomIndices.toList ++
    (TopData0.DataBlock6.data.atomIndices.toList ++
    (TopData0.DataBlock7.data.atomIndices.toList ++
    (TopData1.DataBlock0.data.atomIndices.toList ++
    (TopData1.DataBlock1.data.atomIndices.toList ++
    (TopData1.DataBlock2.data.atomIndices.toList ++
    (TopData1.DataBlock3.data.atomIndices.toList ++ [])))))))))))
  simp only [TopData0.rawData, TopData1.rawData, ArrayCore.appendMassChunk,
    ArrayCore.concatArrays_toList, List.append_assoc, List.append_nil]

/-- Every actual q20 sparse support address satisfies the labelled child-row check. -/
theorem topAtomRowsCovered_of_mem {atom : ℕ} (hmem : atom ∈ topSupportAtomIndices) :
    TopAtomRowsCovered atom := by
  rw [topSupportAtomIndices_eq_blocks] at hmem
  obtain ⟨blockAtoms, hblock, hatom⟩ := List.mem_flatten.mp hmem
  obtain ⟨block, rfl⟩ := List.mem_ofFn.mp hblock
  rw [← topAtomShards_flatten block] at hatom
  obtain ⟨shardAtoms, hshard, hatom⟩ := List.mem_flatten.mp hatom
  obtain ⟨shard, rfl⟩ := List.mem_ofFn.mp hshard
  exact of_decide_eq_true
    ((List.all_eq_true.mp (topAtomShard_checked block shard)) atom hatom)

/-- Any sparse entry of a primary record with this q20 top field has a checked source address. -/
theorem atom_mem_topSupport_of_massEntry (data : PrimaryTables)
    (htop : data.top = topChunks) {entry : ℕ × ℕ}
    (hentry : entry ∈ massEntries data.top) : entry.1 ∈ topSupportAtomIndices := by
  rw [htop] at hentry
  change entry ∈ sparseMassEntries TopData0.data ++
    (sparseMassEntries TopData1.data ++ []) at hentry
  rw [List.append_nil] at hentry
  rcases List.mem_append.mp hentry with hleft | hright
  · unfold sparseMassEntries at hleft
    have hindex := (List.of_mem_zip hleft).1
    exact List.mem_append_left _ hindex
  · unfold sparseMassEntries at hright
    have hindex := (List.of_mem_zip hright).1
    exact List.mem_append_right _ hindex

/-- The pair decoder is inverse to the exact valid sparse top-cell address formula. -/
@[simp] theorem topAtomPairIndex_exact (root region : Fin 6) (pair : Fin levelFourPairCount) :
    topAtomPairIndex
      (topZeroAtomCount +
        (root.val * regionCount + region.val) * topPairCount + pair.val) = pair := by
  apply Fin.ext
  have hpair := pair.isLt
  simp only [topAtomPairIndex, topZeroAtomCount, topPairCount, regionCount,
    levelFourPairCount] at hpair ⊢
  omega

/-- The region decoder retains the incoming physical region, independently of the root label. -/
@[simp] theorem topAtomRegion_exact (root region : Fin 6) (pair : Fin levelFourPairCount) :
    topAtomRegion
      (topZeroAtomCount +
        (root.val * regionCount + region.val) * topPairCount + pair.val) = region := by
  apply Fin.ext
  have hroot := root.isLt
  have hregion := region.isLt
  have hpair := pair.isLt
  simp only [topAtomRegion, topZeroAtomCount, topPairCount, regionCount,
    levelFourPairCount] at hpair ⊢
  omega

/-- The evaluator's valid local-slot lookup has the intrinsic flat ordered-pair index. -/
theorem q20_pairIndexAt_eq (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    pairIndexAt parent.val slot.1.val =
      (levelFourPairIndexAtSlot parent slot.1 slot.2).val := by
  unfold pairIndexAt levelFourPairIndexAtSlot levelFourPairIndexOf
  rw [pairAt_eq_levelFourPairAtSlot parent slot]

/-- Both labelled children of every active q20 row have their appropriate stored lower rows.

Proof sketch: the nonzero reconstructed cell supplies a nonzero sparse source entry. Its checked
address decodes to this exact local slot and region. This uses no assembled restriction and fixes
no primary field other than the top law. -/
theorem activeChildRowsCovered (data : PrimaryTables) (htop : data.top = topChunks)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourActiveSlot (reconstructedTopBranchRows data) root region parent) :
    let pair := levelFourPairAtSlot parent slot.1.1 slot.1.2
    ChildRowCovered pair.1 region ∧ ChildRowCovered pair.2 region := by
  let pairIndex := levelFourPairIndexAtSlot parent slot.1.1 slot.1.2
  have hactive := levelFourActiveSlot_numerator_ne
    (reconstructedTopBranchRows data) root region parent slot
  have hcell : topNumeratorFrom (reconstructedTopBranchRows data)
      root.val region.val pairIndex.val ≠ 0 := by
    simpa only [levelFourSlotNumerator, topSplitNumerator,
      q20_pairIndexAt_eq parent slot.1] using hactive
  obtain ⟨entry, hentry, hatom, _hnumerator⟩ :=
    exists_massEntry_of_topNumeratorFrom_reconstructed_ne_zero
      data root region pairIndex hcell
  have hcovered := topAtomRowsCovered_of_mem
    (atom_mem_topSupport_of_massEntry data htop hentry)
  rw [hatom] at hcovered
  have hpositive : topZeroAtomCount ≤ topZeroAtomCount +
      (root.val * regionCount + region.val) * topPairCount + pairIndex.val := by omega
  simp only [TopAtomRowsCovered, if_pos hpositive,
    topAtomPairIndex_exact, topAtomRegion_exact] at hcovered
  simpa only [pairIndex, levelFourPair_indexAtSlot] using hcovered

/-- Every active positive labelled left child has its literal row in the shared A3 field. -/
theorem leftPositiveRow_mem (data : PrimaryTables) (htop : data.top = topChunks)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourActiveSlot (reconstructedTopBranchRows data) root region parent)
    (hpositive : (levelFourPairAtSlot parent slot.1.1 slot.1.2).1.IsPositive) :
    (positiveShapes 8).idxOf (levelFourPairAtSlot parent slot.1.1 slot.1.2).1 *
        regionCount + region.val ∈
      Generated.PairedTotalWeightPrimary.Pos3AData0.data.rowIndices.toList := by
  rw [← positiveChildRowAddresses_eq_pos3ARows]
  exact (activeChildRowsCovered data htop root region parent slot).1.1 hpositive

/-- Every active positive labelled right child has its literal row in the shared A3 field. -/
theorem rightPositiveRow_mem (data : PrimaryTables) (htop : data.top = topChunks)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourActiveSlot (reconstructedTopBranchRows data) root region parent)
    (hpositive : (levelFourPairAtSlot parent slot.1.1 slot.1.2).2.IsPositive) :
    (positiveShapes 8).idxOf (levelFourPairAtSlot parent slot.1.1 slot.1.2).2 *
        regionCount + region.val ∈
      Generated.PairedTotalWeightPrimary.Pos3AData0.data.rowIndices.toList := by
  rw [← positiveChildRowAddresses_eq_pos3ARows]
  exact (activeChildRowsCovered data htop root region parent slot).2.1 hpositive

/-- Every active nonpositive labelled left child has its literal row in the zero-three field. -/
theorem leftBoundaryRow_mem (data : PrimaryTables) (htop : data.top = topChunks)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourActiveSlot (reconstructedTopBranchRows data) root region parent)
    (hnonpositive : ¬(levelFourPairAtSlot parent slot.1.1 slot.1.2).1.IsPositive) :
    shapeEightIndex (levelFourPairAtSlot parent slot.1.1 slot.1.2).1 *
        regionCount + region.val ∈
      Generated.PairedTotalWeightPrimary.Zero3Data0.data.rowIndices.toList := by
  rw [← boundaryChildRowAddresses_eq_zero3Rows]
  exact (activeChildRowsCovered data htop root region parent slot).1.2 hnonpositive

/-- Every active nonpositive labelled right child has its literal row in the zero-three field. -/
theorem rightBoundaryRow_mem (data : PrimaryTables) (htop : data.top = topChunks)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourActiveSlot (reconstructedTopBranchRows data) root region parent)
    (hnonpositive : ¬(levelFourPairAtSlot parent slot.1.1 slot.1.2).2.IsPositive) :
    shapeEightIndex (levelFourPairAtSlot parent slot.1.1 slot.1.2).2 *
        regionCount + region.val ∈
      Generated.PairedTotalWeightPrimary.Zero3Data0.data.rowIndices.toList := by
  rw [← boundaryChildRowAddresses_eq_zero3Rows]
  exact (activeChildRowsCovered data htop root region parent slot).2.2 hnonpositive

end MatrixMultiplication.LegalHybridQ20TopSupportCoverage
