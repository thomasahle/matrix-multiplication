/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Init

set_option autoImplicit false

/-!
# Support of additive scatters into three-level arrays

Sparse certificate evaluators often reconstruct a chunked dense table by folding additive updates
into a three-level array.  This module proves the reusable pointwise law for that operation.  A
fixed cell after the fold is its initial value plus exactly the contributions addressed to it;
consequently a nonzero cell above a zero initial value has a genuine sparse source entry.

The result is independent of tensors, entropy, and Coppersmith--Winograd geometry.  Its intended
first client is the sparse level-four top law of [alman2025more].
-/

namespace MatrixMultiplication.NestedArrayScatterSupport

local notation "ℕ" => Nat

/-- Total lookup of one cell in a three-level array. -/
def readCell3 (rows : Array (Array (Array ℕ))) (address : ℕ × ℕ × ℕ) : ℕ :=
  (((rows[address.1]?.getD #[])[address.2.1]?.getD #[])[address.2.2]?.getD 0)

/-- Add an amount at one address when all three array indices are in range. -/
def addCell3 (rows : Array (Array (Array ℕ))) (address : ℕ × ℕ × ℕ)
    (amount : ℕ) : Array (Array (Array ℕ)) :=
  if address.1 < rows.size then
    rows.modify address.1 fun chunks ↦
      if address.2.1 < chunks.size then
        chunks.modify address.2.1 fun values ↦
          if address.2.2 < values.size then
            values.modify address.2.2 (· + amount)
          else values
      else chunks
  else rows

/-- The three indices of an address lie inside a supplied chunked array. -/
structure Cell3InBounds (rows : Array (Array (Array ℕ)))
    (address : ℕ × ℕ × ℕ) : Prop where
  row : address.1 < rows.size
  chunk : address.2.1 < (rows[address.1]?.getD #[]).size
  offset : address.2.2 <
    ((rows[address.1]?.getD #[])[address.2.1]?.getD #[]).size

private theorem size_addCell3 (rows : Array (Array (Array ℕ)))
    (address : ℕ × ℕ × ℕ) (amount : ℕ) :
    (addCell3 rows address amount).size = rows.size := by
  unfold addCell3
  split <;> simp

private theorem rowSize_addCell3 (rows : Array (Array (Array ℕ)))
    (target address : ℕ × ℕ × ℕ) (amount : ℕ) (haddress : address.1 < rows.size) :
    ((addCell3 rows target amount)[address.1]?.getD #[]).size =
      (rows[address.1]?.getD #[]).size := by
  unfold addCell3
  split
  · rename_i htarget
    by_cases hrow : target.1 = address.1
    · simp only [Array.getElem?_modify, hrow, ↓reduceIte,
        Array.getElem?_eq_getElem haddress, Option.map_some, Option.getD_some]
      split <;> simp
    · simp [Array.getElem?_modify, hrow]
  · rfl

private theorem cellSize_addCell3 (rows : Array (Array (Array ℕ)))
    (target address : ℕ × ℕ × ℕ) (amount : ℕ)
    (haddress : Cell3InBounds rows address) :
    (((addCell3 rows target amount)[address.1]?.getD #[])[address.2.1]?.getD
      #[]).size =
      ((rows[address.1]?.getD #[])[address.2.1]?.getD #[]).size := by
  have haddressChunk : address.2.1 < (rows[address.1]'haddress.row).size := by
    simpa [Array.getElem?_eq_getElem haddress.row] using haddress.chunk
  unfold addCell3
  split
  · rename_i htargetRow
    by_cases hrow : target.1 = address.1
    · simp only [Array.getElem?_modify, hrow, ↓reduceIte,
        Array.getElem?_eq_getElem haddress.row, Option.map_some, Option.getD_some]
      split
      · rename_i htargetChunk
        by_cases hchunk : target.2.1 = address.2.1
        · simp only [Array.getElem?_modify, hchunk, ↓reduceIte,
            Array.getElem?_eq_getElem haddressChunk, Option.map_some, Option.getD_some]
          split <;> simp
        · simp [Array.getElem?_modify, hchunk]
      · rfl
    · simp [Array.getElem?_modify, hrow]
  · rfl

private theorem inBounds_addCell3 (rows : Array (Array (Array ℕ)))
    (target address : ℕ × ℕ × ℕ) (amount : ℕ)
    (haddress : Cell3InBounds rows address) :
    Cell3InBounds (addCell3 rows target amount) address := by
  constructor
  · rw [size_addCell3]
    exact haddress.row
  · rw [rowSize_addCell3 rows target address amount haddress.row]
    exact haddress.chunk
  · rw [cellSize_addCell3 rows target address amount haddress]
    exact haddress.offset

/-- Reading a valid cell after one additive scatter changes it exactly when the addresses agree. -/
theorem readCell3_addCell3 (rows : Array (Array (Array ℕ)))
    (target address : ℕ × ℕ × ℕ) (amount : ℕ)
    (haddress : Cell3InBounds rows address) :
    readCell3 (addCell3 rows target amount) address =
      readCell3 rows address + if target = address then amount else 0 := by
  have haddressChunk : address.2.1 < (rows[address.1]'haddress.row).size := by
    simpa [Array.getElem?_eq_getElem haddress.row] using haddress.chunk
  have haddressOffset : address.2.2 <
      ((rows[address.1]'haddress.row)[address.2.1]'haddressChunk).size := by
    simpa [Array.getElem?_eq_getElem haddress.row,
      Array.getElem?_eq_getElem haddressChunk] using haddress.offset
  unfold addCell3 readCell3
  split
  · rename_i htargetRow
    by_cases hrow : target.1 = address.1
    · simp only [Array.getElem?_modify, hrow, ↓reduceIte,
        Array.getElem?_eq_getElem haddress.row, Option.map_some, Option.getD_some]
      split
      · rename_i htargetChunk
        by_cases hchunk : target.2.1 = address.2.1
        · simp only [Array.getElem?_modify, hchunk, ↓reduceIte,
            Array.getElem?_eq_getElem haddressChunk, Option.map_some, Option.getD_some]
          split
          · rename_i htargetOffset
            by_cases hoffset : target.2.2 = address.2.2
            · have htarget : target = address :=
                Prod.ext hrow (Prod.ext hchunk hoffset)
              simp [Array.getElem?_modify,
                Array.getElem?_eq_getElem haddressOffset, htarget]
            · have hne : target ≠ address := by
                intro heq
                exact hoffset (congrArg (fun value ↦ value.2.2) heq)
              simp [Array.getElem?_modify, hoffset, hne]
          · rename_i htargetOffset
            have hne : target ≠ address := by
              intro heq
              exact htargetOffset (heq ▸ haddressOffset)
            simp [hne]
        · have hne : target ≠ address := by
            intro heq
            exact hchunk (congrArg (fun value ↦ value.2.1) heq)
          simp [Array.getElem?_modify, hchunk, hne]
      · rename_i htargetChunk
        have hne : target ≠ address := by
          intro heq
          exact htargetChunk (heq ▸ haddressChunk)
        simp [hne]
    · have hne : target ≠ address := by
        intro heq
        exact hrow (congrArg Prod.fst heq)
      simp [Array.getElem?_modify, hrow, hne]
  · rename_i htargetRow
    have hne : target ≠ address := by
      intro heq
      subst target
      exact htargetRow haddress.row
    simp [hne]

/-- Pointwise evaluation commutes with a fold of additive three-level scatters. -/
theorem foldl_readCell3 {A : Type*} (entries : List A)
    (entryAddress : A → ℕ × ℕ × ℕ) (entryAmount : A → ℕ)
    (rows : Array (Array (Array ℕ))) (address : ℕ × ℕ × ℕ)
    (haddress : Cell3InBounds rows address) :
    readCell3 (entries.foldl
        (fun current entry ↦ addCell3 current (entryAddress entry) (entryAmount entry)) rows)
        address =
      readCell3 rows address +
        (entries.map fun entry ↦
          if entryAddress entry = address then entryAmount entry else 0).foldr Nat.add 0 := by
  induction entries generalizing rows with
  | nil => simp
  | cons entry entries ih =>
      simp only [List.foldl_cons, List.map_cons, List.foldr_cons]
      rw [ih (addCell3 rows (entryAddress entry) (entryAmount entry))
        (inBounds_addCell3 rows (entryAddress entry) address (entryAmount entry) haddress)]
      rw [readCell3_addCell3 rows (entryAddress entry) address (entryAmount entry) haddress]
      exact Nat.add_assoc _ _ _

private theorem exists_mem_of_sum_map_ne_zero {A : Type*}
    (entries : List A) (f : A → ℕ)
    (hsum : (entries.map f).foldr Nat.add 0 ≠ 0) :
    ∃ entry ∈ entries, f entry ≠ 0 := by
  induction entries with
  | nil => simp at hsum
  | cons entry entries ih =>
      simp only [List.map_cons, List.foldr_cons] at hsum
      by_cases hentry : f entry = 0
      · obtain ⟨witness, hmem, hwitness⟩ := ih (by simpa [hentry] using hsum)
        exact ⟨witness, by simp [hmem], hwitness⟩
      · exact ⟨entry, by simp, hentry⟩

/-- A nonzero reconstructed cell with zero initial value has a nonzero source entry addressed to
that cell. -/
theorem exists_entry_of_readCell3_foldl_ne_zero {A : Type*} (entries : List A)
    (entryAddress : A → ℕ × ℕ × ℕ) (entryAmount : A → ℕ)
    (rows : Array (Array (Array ℕ))) (address : ℕ × ℕ × ℕ)
    (haddress : Cell3InBounds rows address) (hzero : readCell3 rows address = 0)
    (hcell : readCell3 (entries.foldl
      (fun current entry ↦ addCell3 current (entryAddress entry) (entryAmount entry)) rows)
        address ≠ 0) :
    ∃ entry ∈ entries, entryAddress entry = address ∧ entryAmount entry ≠ 0 := by
  rw [foldl_readCell3 entries entryAddress entryAmount rows address haddress, hzero,
    Nat.zero_add] at hcell
  obtain ⟨entry, hmem, hentry⟩ := exists_mem_of_sum_map_ne_zero entries
    (fun entry ↦ if entryAddress entry = address then entryAmount entry else 0) hcell
  have htarget : entryAddress entry = address := by
    by_cases heq : entryAddress entry = address
    · exact heq
    · exact (hentry (by simp [heq])).elim
  exact ⟨entry, hmem, htarget, by simpa [htarget] using hentry⟩

end MatrixMultiplication.NestedArrayScatterSupport
