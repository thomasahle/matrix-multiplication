/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SparseTopBranchSupport
import MatrixMultiplication.LegalHybridQ20Row44SplitType

set_option autoImplicit false

/-!
# The reconstructed top law agrees with the literal row-44 split type

This is a finite certificate correspondence for the ordered alpha input of Total-Weight's
`cor:recursive-common-input-box`, `better_bound/paper.tex:1085-1124`. The ordered-left-child
law is defined in [alman2025more], `papers/sources/2404.16349/constituent.tex:41-47`.
The exact q20 numerators are this project's certificate data, not data from that source.

The dense reconstruction is never evaluated. Its existing pointwise scatter theorem turns a
queried cell into a sparse sum; selecting the sixteen row-44 addresses leaves that sum unchanged.
The already-proved selected-entry identity then reduces the query to eight scalar entries.
Only `PrimaryTables.top` is fixed, so unrelated child tables need not be instantiated here.

This identifies the evaluator's ordered slot numerators with `row44SlotCount`. It does not prove
parent/child beta consistency, supported fine words, cleanup, repair, or an extraction rate.
The older full recurrence and newer lightweight occurrence modules currently overlap in names;
this file uses only the former through `SparseTopBranchSupport`.
-/

open scoped BigOperators

namespace MatrixMultiplication.LegalHybridQ20Row44TopCorrespondence

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.Generated.LegalHybridQ20Row44Top
open MatrixMultiplication.LegalHybridQ20Row44SlotProfile
open MatrixMultiplication.LegalHybridQ20Row44SplitType
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SparseTopBranchSupport

/-- The sparse atom at one of the sixteen genuine row-44 slot addresses. -/
def row44Atom (i : Fin 16) : ℕ := row44Atoms[i.val]?.getD 0

/-- Every indexed atom belongs to the selected row-44 address list. -/
theorem row44Atom_mem (i : Fin 16) : row44Atom i ∈ row44Atoms := by
  have hi : i.val < row44Atoms.length := i.isLt
  rw [row44Atom, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

/-- The evaluator's proof-free pair lookup is the genuine typed pair at this small slot. -/
theorem row44_pairAt_eq (i : Fin 16) :
    pairAt 6 i.val =
      levelFourPairAtSlot ⟨6, by decide⟩ (row44SlotEquiv i).val
        (row44SlotEquiv i).property := by
  have hp : parentShapeAt 6 = positiveLevelFourShape ⟨6, by decide⟩ := by
    unfold parentShapeAt positiveLevelFourShape
    rw [List.getElem?_eq_getElem (by rw [positiveLevelFourShapes_length]; decide)]
    rfl
  unfold pairAt levelFourPairAtSlot
  have hi : i.val < (levelFourPairsForParent (positiveLevelFourShape ⟨6, by decide⟩)).length :=
    (row44SlotEquiv i).property
  rw [hp, List.getElem?_eq_getElem hi]
  rfl

/-- Every row-44 pair index is within the actual flat pair table. -/
theorem row44_pairIndex_lt (i : Fin 16) : pairIndexAt 6 i.val < levelFourPairCount := by
  rw [pairIndexAt, row44_pairAt_eq, ← levelFourPairs_length]
  exact List.idxOf_lt_length_of_mem
    (levelFourPairAtSlot_geometry _ _ (row44SlotEquiv i).property).1

/-- The evaluator's flat cell address equals the already-certified sparse atom.

Proof sketch: read one element of the proved sixteen-entry address-map identity. This reuses
the geometric lookup proof without evaluating any of the 1785 flat pairs again. -/
theorem row44_pairAtom_eq (i : Fin 16) :
    topZeroAtomCount + (1 * regionCount + 1) * topPairCount + pairIndexAt 6 i.val =
      row44Atom i := by
  have hi : i.val < row44Pairs.length := by rw [row44Pairs_length]; exact i.isLt
  have h := congrArg (fun entries : List ℕ ↦ entries[i.val]?.getD 0) row44Pairs_atoms
  rw [List.getElem?_map, List.getElem?_eq_getElem hi] at h
  rw [pairIndexAt, row44_pairAt_eq]
  change 288 + (1 * 6 + 1) * 1785 + levelFourPairs.idxOf row44Pairs[i.val] = row44Atom i
  exact h

/-- Selecting row 44 from a primary record with the actual q20 top field recovers its
already-proved sparse entry list; no other primary field is used. -/
theorem row44_selected_massEntries (data : PrimaryTables)
    (htop : data.top = Generated.LegalHybridQ20Primary.topChunks) :
    (massEntries data.top).filter (fun entry ↦ decide (entry.1 ∈ row44Atoms)) =
      row44TopEntries := by
  rw [htop]
  change ((sparseMassEntries Generated.LegalHybridQ20Primary.TopData0.data ++
      (sparseMassEntries Generated.LegalHybridQ20Primary.TopData1.data ++ [])).filter
        (fun entry : ℕ × ℕ ↦ decide (entry.1 ∈ row44Atoms))) = _
  rw [List.append_nil, List.filter_append]
  rfl

/-- Querying the eight nonzero scalar entries at a valid small address returns its slot count.
This closed check has only sixteen scalar cases and imports no reduction of the top table. -/
theorem row44Entries_lookup (i : Fin 16) :
    (row44Entries.map (fun entry ↦ if entry.1 = row44Atom i then entry.2 else 0)).sum =
      row44Numerator i := by
  decide +revert

/-- Each reconstructed row-44 cell is exactly the numerator in the literal split profile.

Proof sketch: expand a single dense cell by the existing sparse-scatter theorem. Its atom lies
in the row-44 address set, so removing all other atoms preserves its sum. The proved sparse
selection and eight-entry lookup finish the correspondence without reducing the dense array. -/
theorem row44_topSplitNumerator_eq (data : PrimaryTables)
    (htop : data.top = Generated.LegalHybridQ20Primary.topChunks)
    (slot : LevelFourValidSlot ⟨6, by decide⟩) :
    topSplitNumerator (reconstructedTopBranchRows data) 1 1 6 slot.val.val =
      row44SlotCount slot := by
  obtain ⟨i, rfl⟩ := row44SlotEquiv.surjective slot
  change topNumeratorFrom (reconstructedTopBranchRows data) 1 1 (pairIndexAt 6 i.val) = _
  rw [topNumeratorFrom_reconstructedTopBranchRows_eq_sum data ⟨1, by decide⟩
    ⟨1, by decide⟩ ⟨pairIndexAt 6 i.val, row44_pairIndex_lt i⟩]
  change ((massEntries data.top).map (fun entry ↦
    if entry.1 = topZeroAtomCount + (1 * regionCount + 1) * topPairCount +
      pairIndexAt 6 i.val then entry.2 else 0)).sum = _
  rw [row44_pairAtom_eq]
  have hfilter (entries : List (ℕ × ℕ)) :
      (entries.map (fun entry ↦ if entry.1 = row44Atom i then entry.2 else 0)).sum =
        ((entries.filter (fun entry ↦ decide (entry.1 ∈ row44Atoms))).map
          (fun entry ↦ if entry.1 = row44Atom i then entry.2 else 0)).sum := by
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
      by_cases hmem : entry.1 ∈ row44Atoms
      · simp [hmem, ih]
      · have hne : entry.1 ≠ row44Atom i := by
          intro heq
          exact hmem (heq.symm ▸ row44Atom_mem i)
        simp [hmem, hne, ih]
  rw [hfilter, row44_selected_massEntries data htop, row44TopEntries_eq,
    row44Entries_lookup]
  simp [row44SlotCount]

/-- The dense reconstructed ordered row has raw mass 1696, before child-product scaling. -/
theorem row44_topSplitNumerator_sum (data : PrimaryTables)
    (htop : data.top = Generated.LegalHybridQ20Primary.topChunks) :
    (∑ slot : LevelFourValidSlot ⟨6, by decide⟩,
      topSplitNumerator (reconstructedTopBranchRows data) 1 1 6 slot.val.val) = 1696 := by
  simp only [row44_topSplitNumerator_eq data htop]
  exact row44SlotCount_sum

end MatrixMultiplication.LegalHybridQ20Row44TopCorrespondence
