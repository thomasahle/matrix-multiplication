import MatrixMultiplication.DyadicEntropy
import MatrixMultiplication.Generated.SimplifiedVolumeSchema

/-!
# Entropy adapter for the sparse volume-only certificate

The simplified level-four certificate stores only positive coordinates of each active probability
row.  `SparseDyadicChunk` kernel-checks the support map and exact dyadic checksum.  This module
connects those generated rows to the analytic interval evaluator in `DyadicEntropy`.

No result-specific numeral occurs here.  The generated `SimplifiedVolume*Data` modules instantiate
these theorems for the 20-bit top law and 12-bit local laws.
-/

namespace MatrixMultiplication.Generated.SimplifiedVolume

open AlgebraicComplexity
open MatrixMultiplication.DyadicEntropy

noncomputable section

namespace SparseDyadicChunk

/-- The exact real probability vector represented by one valid sparse row. -/
def rowProbability {bits ambientRows ambientSymbols lower upper : ℕ}
  (data : SparseDyadicChunk)
    (hdata : data.IsValid bits ambientRows ambientSymbols lower upper)
    (row : Fin data.rowIndices.size) : ProbabilityVector (Fin (data.width row)) :=
  (data.toDyadicTable.rowToRational bits row).toReal
    (DyadicTable.rowToRational_isProbability (data.toDyadicTable_isProbability hdata) row)

/-- Sparse-row Shannon entropy is exactly the sum of its dyadic entropy terms. -/
theorem rowProbability_entropyBits_eq
    {bits ambientRows ambientSymbols lower upper : ℕ}
    (data : SparseDyadicChunk)
    (hdata : data.IsValid bits ambientRows ambientSymbols lower upper)
    (row : Fin data.rowIndices.size) :
    (data.rowProbability hdata row).entropyBits =
      ∑ symbol, entropyTerm bits (data.numerator row symbol) := by
  exact rowToRational_entropyBits_eq_sum_entropyTerm data.toDyadicTable
    (data.toDyadicTable_isProbability hdata) row

/-- The canonical rational series endpoint is a lower bound for a generated sparse row's exact
Shannon entropy. -/
theorem certifiedEntropyLower_le_rowProbability_entropyBits
    {bits ambientRows ambientSymbols lower upper : ℕ}
    (data : SparseDyadicChunk)
    (hdata : data.IsValid bits ambientRows ambientSymbols lower upper)
    (steps : ℕ) (row : Fin data.rowIndices.size) :
    certifiedEntropyLower bits steps (data.numerator row) ≤
      (data.rowProbability hdata row).entropyBits := by
  rw [rowProbability_entropyBits_eq data hdata row]
  exact certifiedEntropyLower_le bits steps (data.numerator row)

/-- The canonical rational series endpoint is an upper bound for a generated sparse row's exact
Shannon entropy. -/
theorem rowProbability_entropyBits_le_certifiedEntropyUpper
    {bits ambientRows ambientSymbols lower upper : ℕ}
    (data : SparseDyadicChunk)
    (hdata : data.IsValid bits ambientRows ambientSymbols lower upper)
    (steps : ℕ) (row : Fin data.rowIndices.size) :
    (data.rowProbability hdata row).entropyBits ≤
      certifiedEntropyUpper bits steps (data.numerator row) := by
  rw [rowProbability_entropyBits_eq data hdata row]
  exact le_certifiedEntropyUpper bits steps (data.numerator row)

end SparseDyadicChunk

end

end MatrixMultiplication.Generated.SimplifiedVolume
