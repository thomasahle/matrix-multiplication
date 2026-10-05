/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.NestedArrayScatterSupport
import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option autoImplicit false

/-!
# Sparse support of a reconstructed level-four top law

The mathematical complete-split laws and recursive constituent split are defined in
[alman2025more, `papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:41-47`].  This project's evaluator stores its top law
sparsely and reconstructs a chunked dense table by adding each sparse entry to one cell.  This
module identifies that reconstruction with the generic additive-scatter interface and proves that
every nonzero dense top cell has a genuine nonzero sparse source entry at its exact atom address.

The sparse addresses, chunking, and additive-scatter encoding are project-specific implementation
invariants, not statements of [alman2025more].

The proof is pointwise: it never reduces the full dense table or enumerates all top slots.
-/

namespace MatrixMultiplication.SparseTopBranchSupport

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.NestedArrayScatterSupport
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

/-- Contribution of one sparse mass entry to one valid dense top cell. -/
def topBranchEntryNumerator (root region pair : ℕ) (entry : ℕ × ℕ) : ℕ :=
  if entry.1 = topZeroAtomCount +
      (root * regionCount + region) * topPairCount + pair then entry.2 else 0

/-- The three-level cache address selected by one sparse top entry.

Zero-atom entries use the first out-of-range row.  Every intermediate cache has exactly
`topBranchRowCount` rows, so such entries act as the identity under `addCell3`. -/
private def topBranchEntryAddress (entry : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if topZeroAtomCount ≤ entry.1 then
    let flat := entry.1 - topZeroAtomCount
    let pair := flat % topPairCount
    (flat / topPairCount, pair / topBranchChunkSize, pair % topBranchChunkSize)
  else
    (topBranchRowCount, 0, 0)

/-- Chunked cache address of one valid `(root, region, pair)` top cell. -/
private def topCellAddress (root region pair : ℕ) : ℕ × ℕ × ℕ :=
  (root * regionCount + region, pair / topBranchChunkSize, pair % topBranchChunkSize)

/-- Zero-filled cache used at the start of top-law reconstruction. -/
private def emptyTopBranchRows : TopBranchRows :=
  Array.replicate topBranchRowCount
    (Array.replicate topBranchChunkCount (Array.replicate topBranchChunkSize 0))

private theorem addTopBranchEntry_eq_addCell3 (rows : TopBranchRows) (entry : ℕ × ℕ)
    (hrows : rows.size = topBranchRowCount) :
    addTopBranchEntry rows entry = addCell3 rows (topBranchEntryAddress entry) entry.2 := by
  by_cases hpositive : topZeroAtomCount ≤ entry.1
  · simp [addTopBranchEntry, topBranchEntryAddress, addCell3, hpositive]
  · simp [addTopBranchEntry, topBranchEntryAddress, addCell3, hpositive, hrows]

private theorem foldl_addTopBranchEntry_eq_addCell3 (entries : List (ℕ × ℕ))
    (rows : TopBranchRows) (hrows : rows.size = topBranchRowCount) :
    entries.foldl addTopBranchEntry rows =
      entries.foldl (fun current entry ↦
        addCell3 current (topBranchEntryAddress entry) entry.2) rows := by
  induction entries generalizing rows with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      rw [addTopBranchEntry_eq_addCell3 rows entry hrows]
      apply ih
      unfold addCell3
      split <;> simpa using hrows

private theorem topBranchEntryAddress_eq_topCellAddress_iff
    (root region : Fin 6) (pair : Fin levelFourPairCount) (entry : ℕ × ℕ) :
    topBranchEntryAddress entry = topCellAddress root.val region.val pair.val ↔
      entry.1 = topZeroAtomCount +
        (root.val * regionCount + region.val) * topPairCount + pair.val := by
  have hroot := root.isLt
  have hregion := region.isLt
  have hpair := pair.isLt
  by_cases hpositive : topZeroAtomCount ≤ entry.1
  · simp only [topBranchEntryAddress, hpositive, ↓reduceIte, topCellAddress, Prod.mk.injEq]
    simp only [topZeroAtomCount, topPairCount, topBranchChunkSize, regionCount,
      levelFourPairCount] at hpositive hpair ⊢
    omega
  · simp only [topBranchEntryAddress, hpositive, ↓reduceIte, topCellAddress, Prod.mk.injEq]
    simp only [topZeroAtomCount, topPairCount, topBranchChunkSize, topBranchRowCount,
      regionCount, levelFourPairCount] at hpositive hpair ⊢
    omega

private theorem topCellAddress_inBounds (root region : Fin 6)
    (pair : Fin levelFourPairCount) :
    Cell3InBounds emptyTopBranchRows (topCellAddress root.val region.val pair.val) := by
  have hroot := root.isLt
  have hregion := region.isLt
  have hpair := pair.isLt
  have hrow : root.val * regionCount + region.val < topBranchRowCount := by
    simp only [regionCount, topBranchRowCount]
    omega
  have hchunk : pair.val / topBranchChunkSize < topBranchChunkCount := by
    simp only [topBranchChunkSize, topBranchChunkCount, topPairCount,
      levelFourPairCount] at hpair ⊢
    omega
  have hoffset : pair.val % topBranchChunkSize < topBranchChunkSize :=
    Nat.mod_lt _ (by norm_num [topBranchChunkSize])
  constructor
  · simpa [emptyTopBranchRows, topCellAddress] using hrow
  · simpa [emptyTopBranchRows, topCellAddress, Array.getElem?_replicate, hrow] using hchunk
  · simpa [emptyTopBranchRows, topCellAddress, Array.getElem?_replicate, hrow,
      hchunk] using hoffset

private theorem readCell3_emptyTopBranchRows (root region : Fin 6)
    (pair : Fin levelFourPairCount) :
    readCell3 emptyTopBranchRows (topCellAddress root.val region.val pair.val) = 0 := by
  have hbounds := topCellAddress_inBounds root region pair
  have hrow : root.val * regionCount + region.val < topBranchRowCount := by
    simpa [emptyTopBranchRows, topCellAddress] using hbounds.row
  have hchunk : pair.val / topBranchChunkSize < topBranchChunkCount := by
    simpa [emptyTopBranchRows, topCellAddress, Array.getElem?_replicate, hrow]
      using hbounds.chunk
  have hoffset : pair.val % topBranchChunkSize < topBranchChunkSize := by
    simpa [emptyTopBranchRows, topCellAddress, Array.getElem?_replicate, hrow, hchunk]
      using hbounds.offset
  simp [readCell3, emptyTopBranchRows, topCellAddress, hrow, hchunk, hoffset]

private theorem topNumeratorFrom_eq_readCell3 (rows : TopBranchRows)
    (root region pair : ℕ) :
    topNumeratorFrom rows root region pair = readCell3 rows (topCellAddress root region pair) := by
  rfl

/-- A valid reconstructed top cell equals the sum of precisely its sparse source entries. -/
theorem topNumeratorFrom_reconstructedTopBranchRows_eq_sum
    (data : PrimaryTables) (root region : Fin 6) (pair : Fin levelFourPairCount) :
    topNumeratorFrom (reconstructedTopBranchRows data) root.val region.val pair.val =
      ((massEntries data.top).map
        (topBranchEntryNumerator root.val region.val pair.val)).sum := by
  rw [reconstructedTopBranchRows, foldl_addTopBranchEntry_eq_addCell3]
  · change readCell3
      ((massEntries data.top).foldl (fun current entry ↦
        addCell3 current (topBranchEntryAddress entry) entry.2) emptyTopBranchRows)
      (topCellAddress root.val region.val pair.val) = _
    rw [foldl_readCell3 (massEntries data.top) topBranchEntryAddress Prod.snd
        emptyTopBranchRows (topCellAddress root.val region.val pair.val)
        (topCellAddress_inBounds root region pair),
      readCell3_emptyTopBranchRows, Nat.zero_add]
    simp only [topBranchEntryAddress_eq_topCellAddress_iff]
    rfl
  · simp

/-- Every nonzero valid reconstructed cell is backed by a nonzero sparse entry at its exact atom
address. -/
theorem exists_massEntry_of_topNumeratorFrom_reconstructed_ne_zero
    (data : PrimaryTables) (root region : Fin 6) (pair : Fin levelFourPairCount)
    (hcell :
      topNumeratorFrom (reconstructedTopBranchRows data) root.val region.val pair.val ≠ 0) :
    ∃ entry ∈ massEntries data.top,
      entry.1 = topZeroAtomCount +
          (root.val * regionCount + region.val) * topPairCount + pair.val ∧
        entry.2 ≠ 0 := by
  rw [reconstructedTopBranchRows, foldl_addTopBranchEntry_eq_addCell3,
    topNumeratorFrom_eq_readCell3] at hcell
  · obtain ⟨entry, hmem, haddress, hnumerator⟩ :=
      exists_entry_of_readCell3_foldl_ne_zero
        (massEntries data.top) topBranchEntryAddress Prod.snd emptyTopBranchRows
        (topCellAddress root.val region.val pair.val)
        (topCellAddress_inBounds root region pair)
        (readCell3_emptyTopBranchRows root region pair) hcell
    exact ⟨entry, hmem,
      (topBranchEntryAddress_eq_topCellAddress_iff root region pair entry).mp haddress,
      hnumerator⟩
  · simp

end MatrixMultiplication.SparseTopBranchSupport
