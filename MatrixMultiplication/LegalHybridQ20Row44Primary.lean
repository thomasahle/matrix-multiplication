/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule
import MatrixMultiplication.LegalHybridQ20PrimaryTables
import MatrixMultiplication.SimplifiedLevelFourOccurrenceProfileCore
import MatrixMultiplication.SparseTopBranchSupport

set_option autoImplicit false

/-!
# Semantic q20 primary tables and the first positive parent

This module is the first semantic consumer of the isolated legal-hybrid q20 source image used in
`better_bound/paper.tex:148-159,2057-2075`.  It copies the image's seven primary fields literally
into the established reconstruction record and proves that zero-based schedule row 44 has positive
parent mass.  The proof follows one genuine q20 sparse coordinate: atom `12852` has numerator `7`,
which is global pair 69 and local slot 2 of region-one parent 6.  The generic additive-scatter sum
identity then makes that top slot positive, and the parent sum is positive because it contains the
slot.

Only the 200-entry native source block containing that coordinate is reduced.  The proof does not
reduce the complete 2,244-entry top image or its dense reconstruction.  It also constructs no
beta-three cache: in particular, the total-weight quotient used by `replacementBetaThree` is not
silently substituted for the raw reader required by later identity-row semantics.

The complete-split and recursive-constituent laws are those of [alman2025more,
`papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:41-47`].  Sparse addresses and schedule row numbers are
project-specific exact-certificate representations.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.LegalHybridQ20Row44Primary

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.Generated.LegalHybridQ20Primary
open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SparseTopBranchSupport

/-- Literal conversion of the q20 source image to the established semantic primary-table record. -/
def semanticPrimaryTables :
    MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables :=
  { top := MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables.top
    pos3A := MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables.pos3A
    pos3Alpha := MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables.pos3Alpha
    edgeZero2 := MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables.edgeZero2
    zero3 := MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables.zero3
    zero4 := MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables.zero4
    mu := MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables.mu }

/-- The q20 top field genuinely contains atom `12852` with numerator `7`. -/
theorem row44_sparseEntry_mem :
    (12852, 7) ∈ massEntries semanticPrimaryTables.top := by
  have entries_append (left right : SparseMassChunk)
      (hleft : left.atomIndices.size = left.numerators.size) :
      sparseMassEntries (ArrayCore.appendMassChunk left right) =
        sparseMassEntries left ++ sparseMassEntries right := by
    simp only [sparseMassEntries, ArrayCore.appendMassChunk,
      ArrayCore.concatArrays_toList]
    exact List.zip_append (by simpa using hleft)
  have append_size (left right : SparseMassChunk)
      (hleft : left.atomIndices.size = left.numerators.size)
      (hright : right.atomIndices.size = right.numerators.size) :
      (ArrayCore.appendMassChunk left right).atomIndices.size =
        (ArrayCore.appendMassChunk left right).numerators.size := by
    simp only [ArrayCore.appendMassChunk, ArrayCore.concatArrays_size]
    rw [hleft, hright]
  have hblock :
      (12852, 7) ∈ sparseMassEntries TopData0.DataBlock1.data := by
    decide
  let prefix1 := ArrayCore.appendMassChunk
    TopData0.DataBlock0.data TopData0.DataBlock1.data
  have hprefix1 :
      prefix1.atomIndices.size = prefix1.numerators.size ∧
        (12852, 7) ∈ sparseMassEntries prefix1 := by
    constructor
    · exact append_size _ _ TopData0.DataBlock0.data_isValid.1
        TopData0.DataBlock1.data_isValid.1
    · rw [entries_append _ _ TopData0.DataBlock0.data_isValid.1]
      exact List.mem_append_right _ hblock
  let prefix2 := ArrayCore.appendMassChunk prefix1 TopData0.DataBlock2.data
  have hprefix2 :
      prefix2.atomIndices.size = prefix2.numerators.size ∧
        (12852, 7) ∈ sparseMassEntries prefix2 := by
    constructor
    · exact append_size _ _ hprefix1.1 TopData0.DataBlock2.data_isValid.1
    · rw [entries_append _ _ hprefix1.1]
      exact List.mem_append_left _ hprefix1.2
  let prefix3 := ArrayCore.appendMassChunk prefix2 TopData0.DataBlock3.data
  have hprefix3 :
      prefix3.atomIndices.size = prefix3.numerators.size ∧
        (12852, 7) ∈ sparseMassEntries prefix3 := by
    constructor
    · exact append_size _ _ hprefix2.1 TopData0.DataBlock3.data_isValid.1
    · rw [entries_append _ _ hprefix2.1]
      exact List.mem_append_left _ hprefix2.2
  let prefix4 := ArrayCore.appendMassChunk prefix3 TopData0.DataBlock4.data
  have hprefix4 :
      prefix4.atomIndices.size = prefix4.numerators.size ∧
        (12852, 7) ∈ sparseMassEntries prefix4 := by
    constructor
    · exact append_size _ _ hprefix3.1 TopData0.DataBlock4.data_isValid.1
    · rw [entries_append _ _ hprefix3.1]
      exact List.mem_append_left _ hprefix3.2
  let prefix5 := ArrayCore.appendMassChunk prefix4 TopData0.DataBlock5.data
  have hprefix5 :
      prefix5.atomIndices.size = prefix5.numerators.size ∧
        (12852, 7) ∈ sparseMassEntries prefix5 := by
    constructor
    · exact append_size _ _ hprefix4.1 TopData0.DataBlock5.data_isValid.1
    · rw [entries_append _ _ hprefix4.1]
      exact List.mem_append_left _ hprefix4.2
  let prefix6 := ArrayCore.appendMassChunk prefix5 TopData0.DataBlock6.data
  have hprefix6 :
      prefix6.atomIndices.size = prefix6.numerators.size ∧
        (12852, 7) ∈ sparseMassEntries prefix6 := by
    constructor
    · exact append_size _ _ hprefix5.1 TopData0.DataBlock6.data_isValid.1
    · rw [entries_append _ _ hprefix5.1]
      exact List.mem_append_left _ hprefix5.2
  let prefix7 := ArrayCore.appendMassChunk prefix6 TopData0.DataBlock7.data
  have hprefix7 : (12852, 7) ∈ sparseMassEntries prefix7 := by
    rw [entries_append _ _ hprefix6.1]
    exact List.mem_append_left _ hprefix6.2
  have hraw : prefix7 = MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData0.rawData := by
    rfl
  have htop0 : (12852, 7) ∈
      sparseMassEntries MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData0.data := by
    rw [MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData0.data_eq_rawData, ← hraw]
    exact hprefix7
  change (12852, 7) ∈
    [MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData0.data,
      MatrixMultiplication.Generated.LegalHybridQ20Primary.TopData1.data].flatMap sparseMassEntries
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_append_left _ htop0

/-- Local slot two of region-one parent six has positive q20 top numerator. -/
theorem row44_topSplitNumerator_pos :
    0 < topSplitNumerator
      (reconstructedTopBranchRows semanticPrimaryTables) 1 1 6 2 := by
  have hpair : pairIndexAt 6 2 = 69 := by
    decide
  rw [topSplitNumerator, hpair]
  let root : Fin 6 := ⟨1, by decide⟩
  let region : Fin 6 := ⟨1, by decide⟩
  let pair : Fin levelFourPairCount := ⟨69, by decide⟩
  change 0 < topNumeratorFrom (reconstructedTopBranchRows semanticPrimaryTables)
    root.val region.val pair.val
  rw [topNumeratorFrom_reconstructedTopBranchRows_eq_sum
    semanticPrimaryTables root region pair]
  have hmember :
      topBranchEntryNumerator root.val region.val pair.val (12852, 7) ∈
        (massEntries semanticPrimaryTables.top).map
          (topBranchEntryNumerator root.val region.val pair.val) :=
    List.mem_map_of_mem row44_sparseEntry_mem
  have hterm :
      topBranchEntryNumerator root.val region.val pair.val (12852, 7) = 7 := by
    norm_num [topBranchEntryNumerator, root, region, pair, topZeroAtomCount,
      regionCount, topPairCount]
  have hpositive :
      0 < topBranchEntryNumerator root.val region.val pair.val (12852, 7) := by
    rw [hterm]
    decide
  exact lt_of_lt_of_le hpositive (List.le_sum_of_mem hmember)

/-- Zero-based schedule row 44 is a genuinely positive parent of the reconstructed q20 top law. -/
theorem row44_parentSamples_pos :
    0 < levelFourParentSamples (reconstructedTopBranchRows semanticPrimaryTables)
      (MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule.rowKey 44).1
      (MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule.rowKey 44).1
      (MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule.rowKey 44).2 := by
  rw [MatrixMultiplication.Generated.LegalHybridQ20ModeSchedule.row44_key]
  let parent : Fin positiveLevelFourShapeCount := 6
  let slot : LevelFourValidSlot parent := ⟨⟨2, by decide⟩, by decide⟩
  have hslot :
      0 < levelFourSlotNumerator (reconstructedTopBranchRows semanticPrimaryTables)
        1 1 parent slot := by
    change 0 < topSplitNumerator
      (reconstructedTopBranchRows semanticPrimaryTables) 1 1 6 2
    exact row44_topSplitNumerator_pos
  have hsamples :
      0 < levelFourSamples (reconstructedTopBranchRows semanticPrimaryTables)
        1 1 parent := by
    unfold levelFourSamples
    exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
      ⟨slot, Finset.mem_univ slot, hslot⟩
  unfold levelFourParentSamples
  exact Nat.mul_pos hsamples (by
    norm_num [levelFourChildProductScale, childBits])

end MatrixMultiplication.LegalHybridQ20Row44Primary
