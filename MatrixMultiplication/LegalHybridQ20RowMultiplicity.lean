/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LegalHybridQ20Row44Primary
import MatrixMultiplication.Generated.SimplifiedVolumeRecurrencePairGeometry
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Positive row multiplicities in the exact q20 regional schedule

The regional division in [alman2025more],
`papers/sources/2404.16349/constituent.tex:153-175`, assigns each retained constituent its
own occurrence multiplicity. This module supplies the finite positivity prerequisite for the
225 positive-parent rows of this project's q20 schedule. The integral ordered-count convention is
`better_bound/paper.tex:397-445`, Equation `eq:exact-beta-count` and Remark
`rem:occurrence-parent-law`. The multiplicities are the actual ordered top-row sums,
not rounded scalars, normalized conditional masses, or a separately transcribed table.

Proof sketch: one native sparse entry witnesses each scheduled row. Fifteen address fragments
check at most 32 witnesses each, and eight independent row-address fragments prove that no
schedule row was omitted. Native-block validity supplies numerator positivity. Structural
append lemmas place the entry in the semantic sparse source; its contribution to the
reconstructed top cell is positive, and that cell contributes to the row sum.
Native count certificates supply array sizes, and a generic array/list accessor identity
transports list-read decisions to the native source without evaluating its array accessors.

The native image is this project's q20 certificate with candidate SHA-256
`0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d`.
No unpublished parameter data from [alman2025more] is used. The theorem concerns only the
225 active positive rows: it does not claim positivity for padded rows, identify the sum of
the positive rows with the full top denominator, discard boundary mass, or construct an
assembled tensor restriction.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu,
  Zixuan Xu, and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.LegalHybridQ20RowMultiplicity

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule
open MatrixMultiplication.Generated.LegalHybridQ20Primary
open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.LegalHybridQ20Row44Primary
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SparseTopBranchSupport

/-- The exact ordered top-row multiplicity at one of the 225 active q20 schedule positions. -/
def rowSamples (row : Fin 225) : ℕ :=
  levelFourSamples (reconstructedTopBranchRows semanticPrimaryTables)
    (rowKey row).1 (rowKey row).1 (rowKey row).2

/-- Native blocks retain the source image's order without a dense scatter. -/
private def nativeBlocks : List SparseMassChunk :=
  [TopData0.DataBlock0.data, TopData0.DataBlock1.data, TopData0.DataBlock2.data,
    TopData0.DataBlock3.data, TopData0.DataBlock4.data, TopData0.DataBlock5.data,
    TopData0.DataBlock6.data, TopData0.DataBlock7.data, TopData1.DataBlock0.data,
    TopData1.DataBlock1.data, TopData1.DataBlock2.data, TopData1.DataBlock3.data]

/-- The literal semantic top law is the concatenation of the twelve native entry lists. -/
private theorem nativeEntries_eq :
    massEntries semanticPrimaryTables.top = nativeBlocks.flatMap sparseMassEntries := by
  change [MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData0.data,
    MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.data].flatMap
      sparseMassEntries = _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData0.data_eq_rawData,
    MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.data_eq_rawData]
  simp only [MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData0.rawData,
    MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.rawData,
    nativeBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    sparseMassEntries, ArrayCore.appendMassChunk, ArrayCore.concatArrays_toList]
  simp only [List.zip_append, List.length_append, Array.length_toList,
    TopData0.DataBlock0.data_isValid.1, TopData0.DataBlock1.data_isValid.1,
    TopData0.DataBlock2.data_isValid.1, TopData0.DataBlock3.data_isValid.1,
    TopData0.DataBlock4.data_isValid.1, TopData0.DataBlock5.data_isValid.1,
    TopData0.DataBlock6.data_isValid.1,
    TopData1.DataBlock0.data_isValid.1, TopData1.DataBlock1.data_isValid.1,
    TopData1.DataBlock2.data_isValid.1]
  simp only [List.append_assoc]

/-- Membership in any native block transports to membership in the semantic top law. -/
private theorem native_mem_top {data : SparseMassChunk} {entry : ℕ × ℕ}
    (hdata : data ∈ nativeBlocks) (hentry : entry ∈ sparseMassEntries data) :
    entry ∈ massEntries semanticPrimaryTables.top := by
  rw [nativeEntries_eq]
  exact List.mem_flatMap.mpr ⟨data, hdata, hentry⟩

/-- A stored atom of an aligned positive block has a positive sparse entry at that atom. -/
private theorem exists_positive_entry_at (data : SparseMassChunk)
    (hsize : data.atomIndices.size = data.numerators.size)
    (hpositive : All (fun numerator ↦ 0 < numerator) data.numerators.toList)
    (index : ℕ) (hindex : index < data.atomIndices.size) :
    ∃ entry ∈ sparseMassEntries data,
      entry.1 = data.atomIndices[index]?.getD 0 ∧ 0 < entry.2 := by
  have hmap :
      (sparseMassEntries data).map Prod.fst = data.atomIndices.toList := by
    apply List.map_fst_zip
    simpa using Nat.le_of_eq hsize
  have hatom : data.atomIndices[index]?.getD 0 ∈ data.atomIndices.toList := by
    simpa only [Array.getElem?_eq_getElem hindex, Option.getD_some] using
      Array.getElem_mem_toList hindex
  rw [← hmap] at hatom
  obtain ⟨entry, hentry, haddress⟩ := List.mem_map.mp hatom
  exact ⟨entry, hentry, haddress, All.of_mem hpositive (List.of_mem_zip hentry).2⟩

/-- A valid proof-free local lookup equals the typed ordered-pair lookup. -/
private theorem pairAt_valid_eq (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    pairAt parent.val slot.1.val = levelFourPairAtSlot parent slot.1 slot.2 := by
  have hparent : parentShapeAt parent.val = positiveLevelFourShape parent := by
    unfold parentShapeAt positiveLevelFourShape
    rw [List.getElem?_eq_getElem (by
      rw [positiveLevelFourShapes_length]
      exact parent.isLt)]
    rfl
  unfold pairAt levelFourPairAtSlot
  rw [hparent, List.getElem?_eq_getElem slot.2]
  rfl

/-- A valid local slot has the same global index in both lookup conventions. -/
private theorem pairIndexAt_valid_eq (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    pairIndexAt parent.val slot.1.val =
      (levelFourPairIndexAtSlot parent slot.1 slot.2).val := by
  unfold pairIndexAt levelFourPairIndexAtSlot levelFourPairIndexOf
  rw [pairAt_valid_eq parent slot]

/-- A valid local slot has an in-range global pair index, by the committed typed geometry. -/
private theorem pairIndexAt_lt (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    pairIndexAt parent.val slot.1.val < levelFourPairCount := by
  rw [pairIndexAt_valid_eq parent slot]
  exact (levelFourPairIndexAtSlot parent slot.1 slot.2).isLt

/-- The literal thirty-slot bound is nonzero, so witness slot numerals elaborate locally. -/
private instance : NeZero levelFourPairSlotCount := by
  change NeZero (30 : ℕ)
  infer_instance

/-- One witness records a schedule row, a native-block offset, and a valid-slot candidate. -/
private abbrev Witness := Fin 225 × ℕ × Fin levelFourPairSlotCount

/-- An address-only witness check; numerator positivity comes from native-block validity. -/
private def WitnessValid (data : SparseMassChunk) (witness : Witness) : Prop :=
  witness.2.1 < data.atomIndices.size ∧
    levelFourPairSlotValid (rowKey witness.1).2 witness.2.2 ∧
    data.atomIndices[witness.2.1]?.getD 0 =
      topZeroAtomCount +
        ((rowKey witness.1).1.val * regionCount + (rowKey witness.1).1.val) * topPairCount +
        pairIndexAt (rowKey witness.1).2.val witness.2.2.val

/-- Select one checked 119-entry window without evaluating the 1,785-pair constructor. -/
private def witnessPairIndexBlock (block : Fin 15) : List (ℕ × ℕ) :=
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

/-- Each small window is exactly the corresponding committed semantic geometry window. -/
private theorem witnessPairIndexBlock_eq (block : Fin 15) :
    witnessPairIndexBlock block = computedPairShapeIndexRange (119 * block.val) 119 := by
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

/-- Decode a global pair through its small window and local remainder. -/
private def witnessFastPairIndices (pair : Fin levelFourPairCount) : ℕ × ℕ :=
  (witnessPairIndexBlock ⟨pair.val / 119, by
    have hpair := pair.isLt
    simp only [levelFourPairCount] at hpair
    omega⟩)[pair.val % 119]?.getD default

/-- The bounded decoder returns the two actual physical child-shape indices. -/
private theorem witnessFastPairIndices_eq (pair : Fin levelFourPairCount) :
    witnessFastPairIndices pair =
      (shapeEightIndex (levelFourPair pair).1, shapeEightIndex (levelFourPair pair).2) := by
  have hmod : pair.val % 119 < 119 := Nat.mod_lt _ (by decide)
  have hpair : pair.val < levelFourPairs.length := by
    rw [levelFourPairs_length]
    exact pair.isLt
  unfold witnessFastPairIndices
  rw [witnessPairIndexBlock_eq]
  unfold computedPairShapeIndexRange
  rw [List.getElem?_map, List.getElem?_take_of_lt hmod, List.getElem?_drop,
    Nat.div_add_mod, List.getElem?_eq_getElem hpair]
  rfl

/-- Read a shape from the forty-five total-eight shapes only. -/
private def witnessShapeAtIndex (index : ℕ) : Shape := (shapes 8)[index]?.getD default

/-- Shape lookup inverts the certificate's stored shape index. -/
private theorem witnessShapeAtIndex_shapeEightIndex (shape : Shape) (htotal : shape.total = 8) :
    witnessShapeAtIndex (shapeEightIndex shape) = shape := by
  unfold witnessShapeAtIndex shapeEightIndex
  rw [List.getElem?_idxOf (mem_shapes_iff_total.mpr htotal)]
  rfl

/-- Computational ordered pair using only the small certified windows. -/
private def witnessFastPair (pair : Fin levelFourPairCount) : Shape × Shape :=
  let indices := witnessFastPairIndices pair
  (witnessShapeAtIndex indices.1, witnessShapeAtIndex indices.2)

/-- The small-table ordered pair equals the semantic ordered pair. -/
private theorem witnessFastPair_eq (pair : Fin levelFourPairCount) :
    witnessFastPair pair = levelFourPair pair := by
  unfold witnessFastPair
  rw [witnessFastPairIndices_eq]
  change (witnessShapeAtIndex (shapeEightIndex (levelFourPair pair).1),
    witnessShapeAtIndex (shapeEightIndex (levelFourPair pair).2)) = levelFourPair pair
  rw [witnessShapeAtIndex_shapeEightIndex _ (levelFourPair_geometry pair).1,
    witnessShapeAtIndex_shapeEightIndex _ (levelFourPair_geometry pair).2.1]

/-- Decode an address's pair index, independently of its native storage representation. -/
private def witnessPairIndexFromAtom (atom : ℕ) :
    Fin levelFourPairCount :=
  ⟨(atom - topZeroAtomCount) % levelFourPairCount,
    Nat.mod_lt _ (by norm_num [levelFourPairCount])⟩

/-- Decode the pair address of the native entry, without searching the global pair list. -/
private def witnessPairIndex (data : SparseMassChunk) (witness : Witness) :
    Fin levelFourPairCount :=
  witnessPairIndexFromAtom (data.atomIndices[witness.2.1]?.getD 0)

/-- Bounded check with explicit size and reader, so native arrays need not reduce in decisions. -/
private def WitnessValidRead (width : ℕ) (atomAt : ℕ → ℕ) (witness : Witness) : Prop :=
  witness.2.1 < width ∧
    levelFourPairSlotValid (rowKey witness.1).2 witness.2.2 ∧
    atomAt witness.2.1 =
      topZeroAtomCount +
        ((rowKey witness.1).1.val * regionCount + (rowKey witness.1).1.val) * topPairCount +
        (witnessPairIndexFromAtom (atomAt witness.2.1)).val ∧
    witnessFastPair (witnessPairIndexFromAtom (atomAt witness.2.1)) =
      pairAt (rowKey witness.1).2.val witness.2.2.val

/-- The bounded check is decidable for any computable natural-valued address reader. -/
private instance (width : ℕ) (atomAt : ℕ → ℕ) (witness : Witness) :
    Decidable (WitnessValidRead width atomAt witness) := by
  unfold WitnessValidRead
  infer_instance

/-- The bounded predicate interpreted with the original native array size and accessor. -/
private def WitnessValidFast (data : SparseMassChunk) (witness : Witness) : Prop :=
  WitnessValidRead data.atomIndices.size
    (fun index ↦ data.atomIndices[index]?.getD 0) witness

/-- Injectivity of the flat ordered-pair lookup certifies the bounded witness decoder.

Proof sketch: a checked local pair determines its unique global index. Conversely, quotient and
remainder recover the global index from a valid native address. The semantic global search occurs
only in this opaque proof, never in the Boolean computation. -/
private theorem witnessValidFast_iff (data : SparseMassChunk) (witness : Witness) :
    WitnessValidFast data witness ↔ WitnessValid data witness := by
  constructor
  · rintro ⟨hsize, hslot, haddress, hpair⟩
    let slot : LevelFourValidSlot (rowKey witness.1).2 := ⟨witness.2.2, hslot⟩
    have hindex : witnessPairIndex data witness =
        levelFourPairIndexAtSlot (rowKey witness.1).2 slot.1 slot.2 := by
      apply levelFourPair_injective
      rw [levelFourPair_indexAtSlot, ← witnessFastPair_eq]
      exact hpair.trans (pairAt_valid_eq (rowKey witness.1).2 slot)
    refine ⟨hsize, hslot, ?_⟩
    rw [pairIndexAt_valid_eq (rowKey witness.1).2 slot, ← hindex]
    exact haddress
  · rintro ⟨hsize, hslot, haddress⟩
    let slot : LevelFourValidSlot (rowKey witness.1).2 := ⟨witness.2.2, hslot⟩
    have hindexVal : (witnessPairIndex data witness).val =
        pairIndexAt (rowKey witness.1).2.val witness.2.2.val := by
      have hlt : pairIndexAt (rowKey witness.1).2.val witness.2.2.val <
          levelFourPairCount := pairIndexAt_lt (rowKey witness.1).2 slot
      change (data.atomIndices[witness.2.1]?.getD 0 - topZeroAtomCount) %
        levelFourPairCount = _
      rw [haddress]
      simp only [topPairCount, levelFourPairCount] at hlt ⊢
      omega
    have hindex : witnessPairIndex data witness =
        levelFourPairIndexAtSlot (rowKey witness.1).2 slot.1 slot.2 := by
      apply Fin.ext
      exact hindexVal.trans (pairIndexAt_valid_eq (rowKey witness.1).2 slot)
    refine ⟨hsize, hslot, ?_, ?_⟩
    · change data.atomIndices[witness.2.1]?.getD 0 =
        topZeroAtomCount +
          ((rowKey witness.1).1.val * regionCount + (rowKey witness.1).1.val) * topPairCount +
          (witnessPairIndex data witness).val
      rw [hindexVal]
      exact haddress
    · change witnessFastPair (witnessPairIndex data witness) =
        pairAt (rowKey witness.1).2.val witness.2.2.val
      rw [witnessFastPair_eq, hindex, levelFourPair_indexAtSlot]
      exact (pairAt_valid_eq (rowKey witness.1).2 slot).symm

/-- List-read verification implies the original native-array predicate by exact accessor equality.

The width premise is supplied by the native alignment and value-count theorems. No concrete
array lookup or size calculation occurs in the decision transported by this lemma. -/
private theorem witnessValid_of_list (data : SparseMassChunk) (width : ℕ)
    (hwidth : data.atomIndices.size = width) (witness : Witness)
    (h : WitnessValidRead width
      (fun index ↦ data.atomIndices.toList[index]?.getD 0) witness) :
    WitnessValid data witness := by
  apply (witnessValidFast_iff data witness).mp
  simpa only [WitnessValidFast, hwidth, Array.getElem?_toList] using h

/-- Pointwise list-read certificates transport structurally, with no second finite decision. -/
private theorem witnessesValid_of_list (data : SparseMassChunk) (width : ℕ)
    (hwidth : data.atomIndices.size = width) (witnesses : List Witness) :
    All (WitnessValidRead width
      (fun index ↦ data.atomIndices.toList[index]?.getD 0)) witnesses →
      All (WitnessValid data) witnesses := by
  induction witnesses with
  | nil => exact id
  | cons witness witnesses ih =>
      rintro ⟨hhead, htail⟩
      exact ⟨witnessValid_of_list data width hwidth witness hhead, ih htail⟩

/-- One positive native entry forces the corresponding scheduled row sum to be positive. -/
private theorem rowSamples_pos_of_witness (data : SparseMassChunk)
    (hdata : data ∈ nativeBlocks)
    (hsize : data.atomIndices.size = data.numerators.size)
    (hpositive : All (fun numerator ↦ 0 < numerator) data.numerators.toList)
    (witness : Witness) (hvalid : WitnessValid data witness) :
    0 < rowSamples witness.1 := by
  let key := rowKey witness.1
  let slot : LevelFourValidSlot key.2 := ⟨witness.2.2, hvalid.2.1⟩
  let pair : Fin levelFourPairCount :=
    ⟨pairIndexAt key.2.val slot.1.val, pairIndexAt_lt key.2 slot⟩
  obtain ⟨entry, hentry, haddress, hentryPositive⟩ :=
    exists_positive_entry_at data hsize hpositive witness.2.1 hvalid.1
  have haddress' : entry.1 =
      topZeroAtomCount + (key.1.val * regionCount + key.1.val) * topPairCount + pair.val :=
    haddress.trans hvalid.2.2
  have hterm : 0 < topBranchEntryNumerator key.1.val key.1.val pair.val entry := by
    rw [topBranchEntryNumerator, if_pos haddress']
    exact hentryPositive
  have hmember :
      topBranchEntryNumerator key.1.val key.1.val pair.val entry ∈
        (massEntries semanticPrimaryTables.top).map
          (topBranchEntryNumerator key.1.val key.1.val pair.val) :=
    List.mem_map_of_mem (native_mem_top hdata hentry)
  have hcell : 0 < topNumeratorFrom (reconstructedTopBranchRows semanticPrimaryTables)
      key.1.val key.1.val pair.val := by
    rw [topNumeratorFrom_reconstructedTopBranchRows_eq_sum
      semanticPrimaryTables key.1 key.1 pair]
    exact lt_of_lt_of_le hterm (List.le_sum_of_mem hmember)
  have hslot : 0 < levelFourSlotNumerator
      (reconstructedTopBranchRows semanticPrimaryTables) key.1 key.1 key.2 slot := hcell
  unfold rowSamples levelFourSamples
  exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
    ⟨slot, Finset.mem_univ slot, hslot⟩

/-- Pointwise list certificates concatenate without another finite decision. -/
private theorem all_append {α : Type} {predicate : α → Prop} {left right : List α}
    (hleft : All predicate left) (hright : All predicate right) :
    All predicate (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons value values ih => exact ⟨hleft.1, ih hleft.2⟩

/-- Address-valid witnesses certify positivity of their row projections. -/
private theorem witnessRows_pos (data : SparseMassChunk)
    (hdata : data ∈ nativeBlocks)
    (hsize : data.atomIndices.size = data.numerators.size)
    (hpositive : All (fun numerator ↦ 0 < numerator) data.numerators.toList)
    (witnesses : List Witness) :
    All (WitnessValid data) witnesses →
      All (fun row ↦ 0 < rowSamples row) (witnesses.map Prod.fst) := by
  induction witnesses with
  | nil =>
      intro _
      trivial
  | cons witness witnesses ih =>
      intro hvalid
      exact ⟨rowSamples_pos_of_witness data hdata hsize hpositive witness hvalid.1,
        ih hvalid.2⟩

/-! ## At most 32 witnesses per native address fragment -/

/-- 32 row witnesses in native block `TopData0.DataBlock0`. -/
private def w00a : List Witness :=
  [(0, 39, 10), (1, 40, 10), (2, 52, 10), (3, 33, 7),
    (4, 34, 8), (5, 35, 8), (6, 43, 8), (7, 55, 8),
    (8, 65, 9), (9, 36, 7), (10, 37, 7), (11, 46, 7),
    (12, 47, 6), (13, 59, 6), (14, 67, 9), (15, 38, 6),
    (16, 49, 6), (17, 50, 5), (18, 62, 5), (19, 110, 9),
    (20, 79, 9), (21, 80, 9), (22, 81, 8), (23, 98, 8),
    (24, 113, 8), (25, 169, 10), (26, 125, 9), (27, 82, 7),
    (28, 83, 6), (29, 100, 6), (30, 115, 6), (31, 172, 9)]

/-- Exact address and local-slot checks for fragment `w00a`, with no numerator reduction. -/
private theorem w00a_valid : All (WitnessValid TopData0.DataBlock0.data) w00a := by
  apply witnessesValid_of_list TopData0.DataBlock0.data 200
    (TopData0.DataBlock0.data_isValid.1.trans TopData0.DataBlock0.valueCount_eq) w00a
  decide

/-- 4 row witnesses in native block `TopData0.DataBlock0`. -/
private def w00b : List Witness :=
  [(32, 185, 10), (33, 143, 8), (34, 144, 7), (35, 160, 7)]

/-- Exact address and local-slot checks for fragment `w00b`, with no numerator reduction. -/
private theorem w00b_valid : All (WitnessValid TopData0.DataBlock0.data) w00b := by
  apply witnessesValid_of_list TopData0.DataBlock0.data 200
    (TopData0.DataBlock0.data_isValid.1.trans TopData0.DataBlock0.valueCount_eq) w00b
  decide

/-- 32 row witnesses in native block `TopData0.DataBlock1`. -/
private def w01a : List Witness :=
  [(36, 16, 10), (37, 3, 8), (38, 4, 7), (39, 29, 0),
    (40, 30, 0), (41, 31, 0), (42, 48, 1), (43, 49, 1),
    (44, 74, 2), (45, 101, 2), (46, 102, 1), (47, 135, 1),
    (48, 170, 1), (51, 32, 0), (52, 33, 0), (53, 34, 0),
    (54, 35, 0), (55, 53, 1), (56, 54, 1), (57, 79, 1),
    (58, 108, 1), (59, 109, 0), (60, 142, 0), (61, 177, 0),
    (64, 36, 0), (65, 37, 0), (66, 38, 0), (67, 39, 0),
    (68, 59, 1), (69, 60, 0), (70, 85, 0), (71, 115, 0)]

/-- Exact address and local-slot checks for fragment `w01a`, with no numerator reduction. -/
private theorem w01a_valid : All (WitnessValid TopData0.DataBlock1.data) w01a := by
  apply witnessesValid_of_list TopData0.DataBlock1.data 200
    (TopData0.DataBlock1.data_isValid.1.trans TopData0.DataBlock1.valueCount_eq) w01a
  decide

/-- 28 row witnesses in native block `TopData0.DataBlock1`. -/
private def w01b : List Witness :=
  [(72, 148, 0), (73, 183, 0), (76, 40, 0), (77, 41, 0),
    (78, 42, 0), (79, 43, 0), (80, 65, 0), (81, 90, 0),
    (82, 120, 0), (83, 153, 0), (84, 188, 0), (87, 44, 0),
    (88, 45, 0), (89, 68, 1), (90, 69, 0), (91, 94, 0),
    (92, 124, 0), (93, 157, 0), (94, 192, 0), (99, 95, 1),
    (100, 126, 1), (101, 127, 0), (102, 160, 0), (103, 195, 0),
    (109, 128, 0), (110, 162, 0), (111, 196, 0), (117, 163, 0)]

/-- Exact address and local-slot checks for fragment `w01b`, with no numerator reduction. -/
private theorem w01b_valid : All (WitnessValid TopData0.DataBlock1.data) w01b := by
  apply witnessesValid_of_list TopData0.DataBlock1.data 200
    (TopData0.DataBlock1.data_isValid.1.trans TopData0.DataBlock1.valueCount_eq) w01b
  decide

/-- 18 row witnesses in native block `TopData0.DataBlock2`. -/
private def w02 : List Witness :=
  [(49, 25, 2), (50, 47, 2), (62, 30, 1), (63, 52, 1),
    (74, 11, 0), (75, 56, 1), (85, 16, 0), (86, 40, 0),
    (95, 20, 0), (96, 44, 0), (97, 80, 2), (98, 81, 3),
    (106, 113, 3), (107, 114, 3), (108, 115, 2), (115, 157, 2),
    (116, 158, 1), (122, 159, 0)]

/-- Exact address and local-slot checks for fragment `w02`, with no numerator reduction. -/
private theorem w02_valid : All (WitnessValid TopData0.DataBlock2.data) w02 := by
  apply witnessesValid_of_list TopData0.DataBlock2.data 200
    (TopData0.DataBlock2.data_isValid.1.trans TopData0.DataBlock2.valueCount_eq) w02
  decide

/-- 9 row witnesses in native block `TopData0.DataBlock3`. -/
private def w03 : List Witness :=
  [(104, 87, 3), (105, 122, 2), (112, 90, 2), (114, 170, 3),
    (118, 48, 1), (119, 92, 1), (123, 4, 0), (124, 49, 0),
    (125, 93, 0)]

/-- Exact address and local-slot checks for fragment `w03`, with no numerator reduction. -/
private theorem w03_valid : All (WitnessValid TopData0.DataBlock3.data) w03 := by
  apply witnessesValid_of_list TopData0.DataBlock3.data 200
    (TopData0.DataBlock3.data_isValid.1.trans TopData0.DataBlock3.valueCount_eq) w03
  decide

/-- 9 row witnesses in native block `TopData0.DataBlock4`. -/
private def w04 : List Witness :=
  [(113, 188, 4), (120, 191, 3), (121, 13, 2), (126, 193, 1),
    (127, 15, 0), (128, 60, 0), (129, 105, 0), (130, 150, 0),
    (131, 194, 0)]

/-- Exact address and local-slot checks for fragment `w04`, with no numerator reduction. -/
private theorem w04_valid : All (WitnessValid TopData0.DataBlock4.data) w04 := by
  apply witnessesValid_of_list TopData0.DataBlock4.data 200
    (TopData0.DataBlock4.data_isValid.1.trans TopData0.DataBlock4.valueCount_eq) w04
  decide

/-- 3 row witnesses in native block `TopData0.DataBlock5`. -/
private def w05 : List Witness :=
  [(132, 98, 0), (133, 143, 0), (134, 188, 0)]

/-- Exact address and local-slot checks for fragment `w05`, with no numerator reduction. -/
private theorem w05_valid : All (WitnessValid TopData0.DataBlock5.data) w05 := by
  apply witnessesValid_of_list TopData0.DataBlock5.data 200
    (TopData0.DataBlock5.data_isValid.1.trans TopData0.DataBlock5.valueCount_eq) w05
  decide

/-- 3 row witnesses in native block `TopData0.DataBlock6`. -/
private def w06 : List Witness :=
  [(135, 33, 0), (136, 146, 0), (137, 191, 0)]

/-- Exact address and local-slot checks for fragment `w06`, with no numerator reduction. -/
private theorem w06_valid : All (WitnessValid TopData0.DataBlock6.data) w06 := by
  apply witnessesValid_of_list TopData0.DataBlock6.data 200
    (TopData0.DataBlock6.data_isValid.1.trans TopData0.DataBlock6.valueCount_eq) w06
  decide

/-- 3 row witnesses in native block `TopData0.DataBlock7`. -/
private def w07 : List Witness :=
  [(138, 36, 0), (139, 152, 0), (140, 196, 0)]

/-- Exact address and local-slot checks for fragment `w07`, with no numerator reduction. -/
private theorem w07_valid : All (WitnessValid TopData0.DataBlock7.data) w07 := by
  apply witnessesValid_of_list TopData0.DataBlock7.data 200
    (TopData0.DataBlock7.data_isValid.1.trans TopData0.DataBlock7.valueCount_eq) w07
  decide

/-- 14 row witnesses in native block `TopData1.DataBlock0`. -/
private def w10 : List Witness :=
  [(141, 183, 8), (142, 184, 9), (143, 180, 3), (144, 196, 9),
    (146, 185, 7), (147, 186, 8), (148, 181, 3), (149, 182, 2),
    (152, 187, 6), (153, 188, 7), (154, 189, 7), (160, 190, 6),
    (161, 191, 6), (162, 192, 5)]

/-- Exact address and local-slot checks for fragment `w10`, with no numerator reduction. -/
private theorem w10_valid : All (WitnessValid TopData1.DataBlock0.data) w10 := by
  apply witnessesValid_of_list TopData1.DataBlock0.data 200
    (TopData1.DataBlock0.data_isValid.1.trans TopData1.DataBlock0.valueCount_eq) w10
  decide

/-- 30 row witnesses in native block `TopData1.DataBlock1`. -/
private def w11 : List Witness :=
  [(145, 14, 8), (150, 1, 7), (151, 19, 6), (155, 4, 7),
    (156, 5, 6), (157, 23, 6), (158, 37, 5), (159, 46, 7),
    (163, 8, 5), (164, 26, 5), (165, 40, 5), (166, 115, 7),
    (167, 50, 7), (168, 64, 9), (169, 9, 5), (170, 10, 4),
    (171, 28, 4), (172, 87, 7), (173, 118, 7), (174, 132, 9),
    (175, 67, 7), (176, 68, 6), (177, 89, 6), (178, 106, 6),
    (179, 176, 8), (180, 135, 7), (181, 136, 7), (182, 157, 7),
    (183, 178, 7), (184, 195, 7)]

/-- Exact address and local-slot checks for fragment `w11`, with no numerator reduction. -/
private theorem w11_valid : All (WitnessValid TopData1.DataBlock1.data) w11 := by
  apply witnessesValid_of_list TopData1.DataBlock1.data 200
    (TopData1.DataBlock1.data_isValid.1.trans TopData1.DataBlock1.valueCount_eq) w11
  decide

/-- 32 row witnesses in native block `TopData1.DataBlock2`. -/
private def w12a : List Witness :=
  [(185, 15, 7), (186, 16, 7), (187, 33, 7), (188, 50, 7),
    (189, 80, 10), (190, 81, 10), (191, 93, 10), (192, 78, 8),
    (193, 83, 9), (194, 84, 8), (195, 96, 8), (196, 79, 7),
    (197, 86, 8), (198, 87, 7), (199, 88, 6), (200, 100, 6),
    (201, 107, 9), (202, 89, 7), (203, 90, 6), (204, 91, 5),
    (205, 103, 5), (206, 146, 9), (207, 157, 10), (208, 117, 9),
    (209, 118, 9), (210, 119, 8), (211, 135, 8), (212, 149, 8),
    (214, 160, 9), (215, 161, 10), (216, 136, 7), (217, 137, 6)]

/-- Exact address and local-slot checks for fragment `w12a`, with no numerator reduction. -/
private theorem w12a_valid : All (WitnessValid TopData1.DataBlock2.data) w12a := by
  apply witnessesValid_of_list TopData1.DataBlock2.data 200
    (TopData1.DataBlock2.data_isValid.1.trans TopData1.DataBlock2.valueCount_eq) w12a
  decide

/-- 4 row witnesses in native block `TopData1.DataBlock2`. -/
private def w12b : List Witness :=
  [(218, 191, 10), (221, 176, 8), (222, 177, 7), (223, 193, 7)]

/-- Exact address and local-slot checks for fragment `w12b`, with no numerator reduction. -/
private theorem w12b_valid : All (WitnessValid TopData1.DataBlock2.data) w12b := by
  apply witnessesValid_of_list TopData1.DataBlock2.data 200
    (TopData1.DataBlock2.data_isValid.1.trans TopData1.DataBlock2.valueCount_eq) w12b
  decide

/-- 4 row witnesses in native block `TopData1.DataBlock3`. -/
private def w13 : List Witness :=
  [(213, 1, 10), (219, 3, 9), (220, 12, 10), (224, 37, 10)]

/-- Exact address and local-slot checks for fragment `w13`, with no numerator reduction. -/
private theorem w13_valid : All (WitnessValid TopData1.DataBlock3.data) w13 := by
  apply witnessesValid_of_list TopData1.DataBlock3.data 44
    (TopData1.DataBlock3.data_isValid.1.trans TopData1.DataBlock3.valueCount_eq) w13
  decide

/-- Row IDs certified by the native address fragments; no tensor object occurs in this list. -/
private def witnessedRows : List (Fin 225) :=
  w00a.map Prod.fst ++
    w00b.map Prod.fst ++
    w01a.map Prod.fst ++
    w01b.map Prod.fst ++
    w02.map Prod.fst ++
    w03.map Prod.fst ++
    w04.map Prod.fst ++
    w05.map Prod.fst ++
    w06.map Prod.fst ++
    w07.map Prod.fst ++
    w10.map Prod.fst ++
    w11.map Prod.fst ++
    w12a.map Prod.fst ++
    w12b.map Prod.fst ++
    w13.map Prod.fst

/-- Every listed row has a positive sample count, by structural composition of the fragments. -/
private theorem witnessedRows_pos : All (fun row ↦ 0 < rowSamples row) witnessedRows := by
  have h_w00a := witnessRows_pos TopData0.DataBlock0.data
    (List.get_mem nativeBlocks ⟨0, by decide⟩)
    TopData0.DataBlock0.data_isValid.1 TopData0.DataBlock0.data_isValid.2.2.2
    w00a w00a_valid
  have h_w00b := witnessRows_pos TopData0.DataBlock0.data
    (List.get_mem nativeBlocks ⟨0, by decide⟩)
    TopData0.DataBlock0.data_isValid.1 TopData0.DataBlock0.data_isValid.2.2.2
    w00b w00b_valid
  have h_w01a := witnessRows_pos TopData0.DataBlock1.data
    (List.get_mem nativeBlocks ⟨1, by decide⟩)
    TopData0.DataBlock1.data_isValid.1 TopData0.DataBlock1.data_isValid.2.2.2
    w01a w01a_valid
  have h_w01b := witnessRows_pos TopData0.DataBlock1.data
    (List.get_mem nativeBlocks ⟨1, by decide⟩)
    TopData0.DataBlock1.data_isValid.1 TopData0.DataBlock1.data_isValid.2.2.2
    w01b w01b_valid
  have h_w02 := witnessRows_pos TopData0.DataBlock2.data
    (List.get_mem nativeBlocks ⟨2, by decide⟩)
    TopData0.DataBlock2.data_isValid.1 TopData0.DataBlock2.data_isValid.2.2.2
    w02 w02_valid
  have h_w03 := witnessRows_pos TopData0.DataBlock3.data
    (List.get_mem nativeBlocks ⟨3, by decide⟩)
    TopData0.DataBlock3.data_isValid.1 TopData0.DataBlock3.data_isValid.2.2.2
    w03 w03_valid
  have h_w04 := witnessRows_pos TopData0.DataBlock4.data
    (List.get_mem nativeBlocks ⟨4, by decide⟩)
    TopData0.DataBlock4.data_isValid.1 TopData0.DataBlock4.data_isValid.2.2.2
    w04 w04_valid
  have h_w05 := witnessRows_pos TopData0.DataBlock5.data
    (List.get_mem nativeBlocks ⟨5, by decide⟩)
    TopData0.DataBlock5.data_isValid.1 TopData0.DataBlock5.data_isValid.2.2.2
    w05 w05_valid
  have h_w06 := witnessRows_pos TopData0.DataBlock6.data
    (List.get_mem nativeBlocks ⟨6, by decide⟩)
    TopData0.DataBlock6.data_isValid.1 TopData0.DataBlock6.data_isValid.2.2.2
    w06 w06_valid
  have h_w07 := witnessRows_pos TopData0.DataBlock7.data
    (List.get_mem nativeBlocks ⟨7, by decide⟩)
    TopData0.DataBlock7.data_isValid.1 TopData0.DataBlock7.data_isValid.2.2.2
    w07 w07_valid
  have h_w10 := witnessRows_pos TopData1.DataBlock0.data
    (List.get_mem nativeBlocks ⟨8, by decide⟩)
    TopData1.DataBlock0.data_isValid.1 TopData1.DataBlock0.data_isValid.2.2.2
    w10 w10_valid
  have h_w11 := witnessRows_pos TopData1.DataBlock1.data
    (List.get_mem nativeBlocks ⟨9, by decide⟩)
    TopData1.DataBlock1.data_isValid.1 TopData1.DataBlock1.data_isValid.2.2.2
    w11 w11_valid
  have h_w12a := witnessRows_pos TopData1.DataBlock2.data
    (List.get_mem nativeBlocks ⟨10, by decide⟩)
    TopData1.DataBlock2.data_isValid.1 TopData1.DataBlock2.data_isValid.2.2.2
    w12a w12a_valid
  have h_w12b := witnessRows_pos TopData1.DataBlock2.data
    (List.get_mem nativeBlocks ⟨10, by decide⟩)
    TopData1.DataBlock2.data_isValid.1 TopData1.DataBlock2.data_isValid.2.2.2
    w12b w12b_valid
  have h_w13 := witnessRows_pos TopData1.DataBlock3.data
    (List.get_mem nativeBlocks ⟨11, by decide⟩)
    TopData1.DataBlock3.data_isValid.1 TopData1.DataBlock3.data_isValid.2.2.2
    w13 w13_valid
  simp only [witnessedRows, List.append_assoc]
  exact all_append h_w00a <| all_append h_w00b <|
    all_append h_w01a <| all_append h_w01b <|
    all_append h_w02 <| all_append h_w03 <|
    all_append h_w04 <| all_append h_w05 <|
    all_append h_w06 <| all_append h_w07 <|
    all_append h_w10 <| all_append h_w11 <|
    all_append h_w12a <| all_append h_w12b h_w13

/-! ## Coverage checks inspect only schedule-row addresses -/

/-- Total row-address conversion used only by the bounded coverage certificates. -/
private def rowOfNat (index : ℕ) : Fin 225 :=
  ⟨index % 225, Nat.mod_lt _ (by decide)⟩

/-- Every schedule address in `[0, 32)` occurs among the witnesses. -/
private theorem coverage0 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 0 32) := by
  decide

/-- Every schedule address in `[32, 64)` occurs among the witnesses. -/
private theorem coverage1 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 32 32) := by
  decide

/-- Every schedule address in `[64, 96)` occurs among the witnesses. -/
private theorem coverage2 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 64 32) := by
  decide

/-- Every schedule address in `[96, 128)` occurs among the witnesses. -/
private theorem coverage3 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 96 32) := by
  decide

/-- Every schedule address in `[128, 160)` occurs among the witnesses. -/
private theorem coverage4 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 128 32) := by
  decide

/-- Every schedule address in `[160, 192)` occurs among the witnesses. -/
private theorem coverage5 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 160 32) := by
  decide

/-- Every schedule address in `[192, 224)` occurs among the witnesses. -/
private theorem coverage6 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 192 32) := by
  decide

/-- Every schedule address in `[224, 225)` occurs among the witnesses. -/
private theorem coverage7 :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 224 1) := by
  decide

/-- Adjacent natural-address ranges concatenate without a new decision. -/
private theorem all_range_append {predicate : ℕ → Prop} {start first second : ℕ}
    (hfirst : All predicate (List.range' start first))
    (hsecond : All predicate (List.range' (start + first) second)) :
    All predicate (List.range' start (first + second)) := by
  rw [← List.range'_append_1]
  exact all_append hfirst hsecond

/-- The eight checked address ranges cover all 225 schedule positions. -/
private theorem coverage_all :
    All (fun index ↦ rowOfNat index ∈ witnessedRows) (List.range' 0 225) := by
  exact all_range_append coverage0 (all_range_append coverage1
    (all_range_append coverage2 (all_range_append coverage3
      (all_range_append coverage4 (all_range_append coverage5
        (all_range_append coverage6 coverage7))))))

/-- Every row in the actual 225-row q20 schedule has strictly positive ordered multiplicity.

Proof sketch: the coverage certificate supplies a native sparse witness for this exact schedule
position. Its positive contribution survives additive top reconstruction and the parent-row sum.
No statement about a global copy count or a tensor restriction is assumed. -/
theorem allActiveRowSamples_pos (row : Fin 225) : 0 < rowSamples row := by
  have hindex : row.val ∈ List.range' 0 225 :=
    List.mem_range'.mpr ⟨row.val, row.isLt, by simp⟩
  have hmem := All.of_mem coverage_all hindex
  have hrow : rowOfNat row.val = row := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt row.isLt
  rw [hrow] at hmem
  exact All.of_mem (predicate := fun row : Fin 225 ↦ 0 < rowSamples row)
    (value := row) witnessedRows_pos hmem

end MatrixMultiplication.LegalHybridQ20RowMultiplicity
