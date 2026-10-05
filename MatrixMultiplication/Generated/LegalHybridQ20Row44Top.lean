/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.LegalHybridQ20PrimaryData

set_option autoImplicit false

/-!
# Exact sparse top entries for legal-hybrid row 44

This module reconstructs the eight nonzero entries of the project's q20 top law at sixteen
explicit sparse addresses and proves that their numerators sum to 1696. These are the local source
data for the candidate described in `better_bound/paper.tex:148-159`. The recursive distribution
they are intended to instantiate is the ordered-child law of [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`, with complete-split types defined in
`papers/sources/2404.16349/prelim.tex:249-278`.

The sixteen addresses are not consecutive: the flat pair table is left-major across all parents.
Only the three native 200-entry blocks intersecting their enclosing interval are evaluated. All
other blocks are excluded by proved address bounds; append identities assemble the result without
evaluating the full top array or importing lower-level tables. The atoms and numerators are our
own certificate data, not unpublished data of the cited authors.

This module proves a literal sparse-table identity, not the separate interpretation of its
addresses as recursive split slots, existence of a child reference, tensor extraction, or an
exponent bound.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20Row44Top

open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.Generated.LegalHybridQ20Primary

/-- Retain sparse mass entries at the prescribed addresses, in their original order. -/
def entriesAtAddresses (addresses : List Nat) (chunk : SparseMassChunk) : List (Nat × Nat) :=
  (chunk.atomIndices.toList.zip chunk.numerators.toList).filter
    (fun entry => decide (entry.1 ∈ addresses))

/-- A matched sparse append preserves address selection, including the order of entries. -/
theorem entriesAtAddresses_append (addresses : List Nat) (left right : SparseMassChunk)
    (hleft : left.atomIndices.size = left.numerators.size) :
    entriesAtAddresses addresses (ArrayCore.appendMassChunk left right) =
      entriesAtAddresses addresses left ++ entriesAtAddresses addresses right := by
  unfold entriesAtAddresses ArrayCore.appendMassChunk
  simp only [ArrayCore.concatArrays_toList]
  rw [List.zip_append (by simpa using hleft), List.filter_append]

/-- Certified disjoint address bounds exclude a whole sparse chunk without evaluating it.

Proof sketch: any retained entry would lie both in the address interval and in the disjoint
chunk interval. Either ordering of the two intervals contradicts one of their strict bounds.
-/
theorem entriesAtAddresses_eq_nil_of_disjoint
    (addresses : List Nat) (lower upper : Nat) (chunk : SparseMassChunk)
    {ambient chunkLower chunkUpper : Nat}
    (haddresses : ∀ address ∈ addresses, lower ≤ address ∧ address < upper)
    (hvalid : chunk.IsValid ambient chunkLower chunkUpper)
    (hdisjoint : chunkUpper ≤ lower ∨ upper ≤ chunkLower) :
    entriesAtAddresses addresses chunk = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry hentry hselected
  have hbounds := All.of_mem hvalid.2.2.1 (List.of_mem_zip hentry).1
  have hinside := haddresses entry.1 (of_decide_eq_true hselected)
  rcases hdisjoint with hbefore | hafter
  · exact (Nat.not_lt_of_ge (Nat.le_trans hbefore hinside.1)) hbounds.2.1
  · exact (Nat.not_lt_of_ge (Nat.le_trans hafter hbounds.1)) hinside.2

/-- Two matched chunks with known selected images compose by list append. -/
theorem entriesAtAddresses_append_image
    (addresses : List Nat) (left right : SparseMassChunk)
    (leftImage rightImage : List (Nat × Nat))
    (hleft : left.atomIndices.size = left.numerators.size ∧
      entriesAtAddresses addresses left = leftImage)
    (hright : right.atomIndices.size = right.numerators.size ∧
      entriesAtAddresses addresses right = rightImage) :
    (ArrayCore.appendMassChunk left right).atomIndices.size =
        (ArrayCore.appendMassChunk left right).numerators.size ∧
      entriesAtAddresses addresses (ArrayCore.appendMassChunk left right) =
        leftImage ++ rightImage := by
  constructor
  · simp only [ArrayCore.appendMassChunk, ArrayCore.concatArrays_size]
    rw [hleft.1, hright.1]
  · rw [entriesAtAddresses_append addresses left right hleft.1, hleft.2, hright.2]

/-- The sixteen flat addresses of the ordered splits; eight have zero mass and are absent. -/
def row44Atoms : List Nat :=
  [12789, 12817, 12852, 12887, 12922, 12957, 12992, 13027,
   13097, 13133, 13177, 13221, 13265, 13309, 13353, 13397]

/-- The small explicit address set lies in its enclosing half-open interval. -/
theorem row44Atoms_bounds :
    ∀ address ∈ row44Atoms, 12789 ≤ address ∧ address < 13398 := by
  decide

/-- The eight exact nonzero q20 atoms, with their original source numerators. -/
def row44Entries : List (Nat × Nat) :=
  [(12852, 7), (12887, 175), (12922, 596), (12957, 71),
   (13177, 69), (13221, 596), (13265, 173), (13309, 9)]

/-- Four selected atoms occur in the first intersecting native source block. -/
theorem row44_block1_eq :
    entriesAtAddresses row44Atoms TopData0.DataBlock1.data =
      [(12852, 7), (12887, 175), (12922, 596), (12957, 71)] := by
  decide

/-- Two selected atoms occur in the second intersecting native source block. -/
theorem row44_block2_eq :
    entriesAtAddresses row44Atoms TopData0.DataBlock2.data =
      [(13177, 69), (13221, 596)] := by
  decide

/-- The final two selected atoms occur in the third intersecting native source block. -/
theorem row44_block3_eq :
    entriesAtAddresses row44Atoms TopData0.DataBlock3.data =
      [(13265, 173), (13309, 9)] := by
  decide

/-- Symbolic composition of the native blocks reconstructs the first top chunk's selected image.

Proof sketch: three small block computations supply the eight retained entries. Interval bounds
exclude every other block, and the append identity combines the checked pieces in source order.
-/
theorem row44_top0_eq :
    entriesAtAddresses row44Atoms TopData0.data = row44Entries := by
  have hbefore : entriesAtAddresses row44Atoms TopData0.DataBlock0.data = [] :=
    entriesAtAddresses_eq_nil_of_disjoint _ 12789 13398 _ row44Atoms_bounds
      TopData0.DataBlock0.data_isValid (Or.inl (by decide))
  let prefix1 := ArrayCore.appendMassChunk TopData0.DataBlock0.data TopData0.DataBlock1.data
  have hprefix1 : prefix1.atomIndices.size = prefix1.numerators.size ∧
      entriesAtAddresses row44Atoms prefix1 =
        [(12852, 7), (12887, 175), (12922, 596), (12957, 71)] := by
    simpa only [List.nil_append] using
      entriesAtAddresses_append_image row44Atoms _ _ _ _
        ⟨TopData0.DataBlock0.data_isValid.1, hbefore⟩
        ⟨TopData0.DataBlock1.data_isValid.1, row44_block1_eq⟩
  let prefix2 := ArrayCore.appendMassChunk prefix1 TopData0.DataBlock2.data
  have hprefix2 : prefix2.atomIndices.size = prefix2.numerators.size ∧
      entriesAtAddresses row44Atoms prefix2 =
        [(12852, 7), (12887, 175), (12922, 596), (12957, 71),
         (13177, 69), (13221, 596)] :=
    entriesAtAddresses_append_image row44Atoms _ _ _ _ hprefix1
      ⟨TopData0.DataBlock2.data_isValid.1, row44_block2_eq⟩
  let prefix3 := ArrayCore.appendMassChunk prefix2 TopData0.DataBlock3.data
  have hprefix3 : prefix3.atomIndices.size = prefix3.numerators.size ∧
      entriesAtAddresses row44Atoms prefix3 = row44Entries :=
    entriesAtAddresses_append_image row44Atoms _ _ _ _ hprefix2
      ⟨TopData0.DataBlock3.data_isValid.1, row44_block3_eq⟩
  let prefix4 := ArrayCore.appendMassChunk prefix3 TopData0.DataBlock4.data
  have hprefix4 : prefix4.atomIndices.size = prefix4.numerators.size ∧
      entriesAtAddresses row44Atoms prefix4 = row44Entries := by
    simpa only [List.append_nil] using
      entriesAtAddresses_append_image row44Atoms _ _ _ _ hprefix3
        ⟨TopData0.DataBlock4.data_isValid.1,
          entriesAtAddresses_eq_nil_of_disjoint _ 12789 13398 _ row44Atoms_bounds
            TopData0.DataBlock4.data_isValid (Or.inr (by decide))⟩
  let prefix5 := ArrayCore.appendMassChunk prefix4 TopData0.DataBlock5.data
  have hprefix5 : prefix5.atomIndices.size = prefix5.numerators.size ∧
      entriesAtAddresses row44Atoms prefix5 = row44Entries := by
    simpa only [List.append_nil] using
      entriesAtAddresses_append_image row44Atoms _ _ _ _ hprefix4
        ⟨TopData0.DataBlock5.data_isValid.1,
          entriesAtAddresses_eq_nil_of_disjoint _ 12789 13398 _ row44Atoms_bounds
            TopData0.DataBlock5.data_isValid (Or.inr (by decide))⟩
  let prefix6 := ArrayCore.appendMassChunk prefix5 TopData0.DataBlock6.data
  have hprefix6 : prefix6.atomIndices.size = prefix6.numerators.size ∧
      entriesAtAddresses row44Atoms prefix6 = row44Entries := by
    simpa only [List.append_nil] using
      entriesAtAddresses_append_image row44Atoms _ _ _ _ hprefix5
        ⟨TopData0.DataBlock6.data_isValid.1,
          entriesAtAddresses_eq_nil_of_disjoint _ 12789 13398 _ row44Atoms_bounds
            TopData0.DataBlock6.data_isValid (Or.inr (by decide))⟩
  let prefix7 := ArrayCore.appendMassChunk prefix6 TopData0.DataBlock7.data
  have hprefix7 : prefix7.atomIndices.size = prefix7.numerators.size ∧
      entriesAtAddresses row44Atoms prefix7 = row44Entries := by
    simpa only [List.append_nil] using
      entriesAtAddresses_append_image row44Atoms _ _ _ _ hprefix6
        ⟨TopData0.DataBlock7.data_isValid.1,
          entriesAtAddresses_eq_nil_of_disjoint _ 12789 13398 _ row44Atoms_bounds
            TopData0.DataBlock7.data_isValid (Or.inr (by decide))⟩
  rw [TopData0.data_eq_rawData]
  exact hprefix7.2

/-- The entire second top chunk lies after all selected addresses and contributes no entries. -/
theorem row44_top1_eq :
    entriesAtAddresses row44Atoms TopData1.data = [] :=
  entriesAtAddresses_eq_nil_of_disjoint _ 12789 13398 _ row44Atoms_bounds
    TopData1.data_isValid (Or.inr (by decide))

/-- The entries selected from both actual q20 top chunks, without consulting lower tables. -/
def row44TopEntries : List (Nat × Nat) :=
  entriesAtAddresses row44Atoms TopData0.data ++ entriesAtAddresses row44Atoms TopData1.data

/-- The actual two-chunk selection consists of exactly the eight explicit nonzero atoms. -/
theorem row44TopEntries_eq : row44TopEntries = row44Entries := by
  rw [row44TopEntries, row44_top0_eq, row44_top1_eq, List.append_nil]

/-- The exact top-law mass numerator of the selected source entries is 1696. -/
theorem row44TopEntries_total : (row44TopEntries.map Prod.snd).sum = 1696 := by
  rw [row44TopEntries_eq]
  rfl

end MatrixMultiplication.Generated.LegalHybridQ20Row44Top
