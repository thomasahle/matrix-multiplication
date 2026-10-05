/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.DyadicTable

/-!
# Dictionary-compressed dyadic probability tables

Large numerical certificates often repeat the same probability row many times.  This module
stores each distinct row once and expands it through a row-index function.  Its validation theorem
checks only three exact facts: every index is in bounds, every selected row has the prescribed
width, and every dictionary entry has the dyadic checksum.

The construction is deliberately independent of any matrix-multiplication recurrence.  A
generated certificate may therefore compress positive constituents, zero constituents, and
hashing distributions through the same interface.
-/

open scoped BigOperators

namespace AlgebraicComplexity

/-- A ragged dictionary of exact numerator rows together with a semantic row-to-entry map. -/
structure DyadicRowDictionary (Row : Type*) (width : Row → ℕ) where
  rows : Array (Array ℕ)
  rowIndex : Row → ℕ

namespace DyadicRowDictionary

variable {Row : Type*} {width : Row → ℕ}

/-- The serialized row selected for a semantic row, with an empty fallback for malformed data. -/
def rowData (data : DyadicRowDictionary Row width) (row : Row) : Array ℕ :=
  data.rows[data.rowIndex row]?.getD #[]

/-- Read one numerator from the selected dictionary row. -/
def numerator (data : DyadicRowDictionary Row width)
    (row : Row) (symbol : Fin (width row)) : ℕ :=
  (data.rowData row)[symbol.val]?.getD 0

/-- Every semantic row selects an actual dictionary entry. -/
def HasValidIndices (data : DyadicRowDictionary Row width) : Prop :=
  ∀ row, data.rowIndex row < data.rows.size

/-- Every selected dictionary row has the width prescribed by its semantic row. -/
def HasShape (data : DyadicRowDictionary Row width) : Prop :=
  ∀ row, (data.rowData row).size = width row

/-- Every stored dictionary entry has the common dyadic checksum. -/
def RowsNormalized (bits : ℕ) (data : DyadicRowDictionary Row width) : Prop :=
  ∀ entry : Fin data.rows.size,
    (data.rows[entry.val]?.getD #[]).toList.sum = dyadicDenominator bits

/-- Exact validity of a dictionary-compressed table. -/
def IsValid (bits : ℕ) (data : DyadicRowDictionary Row width) : Prop :=
  data.HasValidIndices ∧ data.HasShape ∧ data.RowsNormalized bits

/-- Expand the dictionary to the ordinary semantic dyadic-table interface. -/
def toDyadicTable (data : DyadicRowDictionary Row width) : DyadicTable Row width where
  numerator := data.numerator

theorem rowData_eq_getElem (data : DyadicRowDictionary Row width) (row : Row)
    (hindex : data.rowIndex row < data.rows.size) :
    data.rowData row = data.rows[data.rowIndex row] := by
  simp [rowData, hindex]

/-- A valid compressed table expands to exactly normalized dyadic rows. -/
theorem toDyadicTable_isProbability {bits : ℕ} {data : DyadicRowDictionary Row width}
    (hdata : data.IsValid bits) :
    data.toDyadicTable.IsProbability bits := by
  intro row
  have hindex : data.rowIndex row < data.rows.size := hdata.1 row
  have hshape : (data.rowData row).size = width row := hdata.2.1 row
  calc
    (∑ symbol, data.toDyadicTable.numerator row symbol) =
        (data.rowData row).toList.sum :=
      array_getElem?_getD_sum_eq_toList_sum (data.rowData row) (width row) hshape
    _ = (data.rows[data.rowIndex row]).toList.sum := by
      rw [rowData_eq_getElem data row hindex]
    _ = dyadicDenominator bits := by
      simpa [Array.getElem?_eq_getElem, hindex] using
        hdata.2.2 ⟨data.rowIndex row, hindex⟩

/-- A valid compressed row therefore has an exact rational probability interpretation. -/
theorem rowToRational_isProbability {bits : ℕ} {data : DyadicRowDictionary Row width}
    (hdata : data.IsValid bits) (row : Row) :
    (data.toDyadicTable.rowToRational bits row).IsProbability :=
  DyadicTable.rowToRational_isProbability (toDyadicTable_isProbability hdata) row

end DyadicRowDictionary

end AlgebraicComplexity
