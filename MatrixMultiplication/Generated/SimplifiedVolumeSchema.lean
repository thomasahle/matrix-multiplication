/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.DyadicDictionary
import MatrixMultiplication.Generated.SimplifiedVolumeSchemaDefs

/-!
# Semantic adapters for the simplified-volume certificate schema

`SimplifiedVolumeSchemaDefs.lean` owns the executable sparse structures and validity predicates.
This module adds their bridge to the reusable dyadic probability API.  Generated files which only
seal exact arrays should import the definition leaf; semantic consumers import this module.
-/

namespace MatrixMultiplication.Generated.SimplifiedVolume

open AlgebraicComplexity

namespace SparseDyadicChunk

/-- Dictionary view used by the reusable dyadic probability API. -/
def certificate (data : SparseDyadicChunk) :
    DyadicRowDictionary (Fin data.rowIndices.size) data.width where
  rows := data.numeratorRows
  rowIndex row := row.val

/-- Read one exact numerator through the reusable dictionary interface. -/
def numerator (data : SparseDyadicChunk) (row : Fin data.rowIndices.size)
    (symbol : Fin (data.width row)) : ℕ :=
  data.certificate.numerator row symbol

/-- Expand the locally compressed rows to the ordinary dyadic-table interface. -/
def toDyadicTable (data : SparseDyadicChunk) :
    DyadicTable (Fin data.rowIndices.size) data.width :=
  data.certificate.toDyadicTable

/-- Every valid sparse chunk supplies genuine dyadic probability rows. -/
theorem certificate_isValid {bits ambientRows ambientSymbols lower upper : ℕ}
    {data : SparseDyadicChunk}
    (hdata : data.IsValid bits ambientRows ambientSymbols lower upper) :
    data.certificate.IsValid bits := by
  have hnumSize : data.numeratorRows.size = data.rowIndices.size := hdata.2.1
  have hsupportSize : data.supportRows.size = data.rowIndices.size := hdata.1
  have hrowShape := hdata.2.2.2.2.2.1
  have hnormalized := hdata.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro row
    simpa [certificate] using (show row.val < data.numeratorRows.size by
      rw [hnumSize]
      exact row.isLt)
  · intro row
    have hindex : row.val < data.numeratorRows.size := by
      rw [hnumSize]
      exact row.isLt
    have hsupportIndex : row.val < data.supportRows.size := by
      rw [hsupportSize]
      exact row.isLt
    have hshape := hrowShape.get row.val hindex hsupportIndex
    simpa [DyadicRowDictionary.HasShape, certificate, DyadicRowDictionary.rowData,
      numeratorRow, supportRow, width, natRow, hindex, hsupportIndex] using hshape.1
  · intro entry
    have hentryNum : entry.val < data.numeratorRows.size := by
      simpa [certificate] using entry.isLt
    have hentry : entry.val < data.rowIndices.size := by
      simpa [hnumSize] using hentryNum
    let row : Fin data.rowIndices.size := ⟨entry.val, hentry⟩
    have hrowMem : data.numeratorRows[entry.val] ∈ data.numeratorRows.toList := by
      simp
    simpa [DyadicRowDictionary.RowsNormalized, certificate, numeratorRow, natRow,
      dyadicDenominator,
      row, hentry, entry.isLt, hentryNum] using
      All.of_mem hnormalized hrowMem

/-- A valid sparse chunk expands to a family of probability distributions. -/
theorem toDyadicTable_isProbability {bits ambientRows ambientSymbols lower upper : ℕ}
    {data : SparseDyadicChunk}
    (hdata : data.IsValid bits ambientRows ambientSymbols lower upper) :
    data.toDyadicTable.IsProbability bits :=
  DyadicRowDictionary.toDyadicTable_isProbability (certificate_isValid hdata)

end SparseDyadicChunk

end MatrixMultiplication.Generated.SimplifiedVolume
