import AlgebraicComplexity.Probability.RationalCore
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Exact dyadic probability tables

Optimizer certificates commonly store probability numerators with one shared power-of-two
denominator.  This module gives that representation a small, reusable Lean interface.  It is
independent of any tensor construction, recursion depth, or certificate layout.

`DyadicMassData` represents one finite distribution.  `DyadicTable` represents a family of rows
whose alphabet widths may depend on the row.  Exact numerator-sum hypotheses convert both forms
to the existing `RationalProbabilityData` API; no floating-point computation enters the bridge.
-/

open scoped BigOperators

namespace AlgebraicComplexity

/-- Summing safe array lookups over an exactly matching finite index type is the ordinary list
sum of the array.  This adapter is useful for kernel-checking large generated tables: the list
sum reduces in linear time, whereas repeatedly indexing a literal array can make a direct finite
sum needlessly expensive. -/
theorem array_getElem?_getD_sum_eq_toList_sum (data : Array ℕ) (width : ℕ)
    (hsize : data.size = width) :
    (∑ index : Fin width, data[index.val]?.getD 0) = data.toList.sum := by
  subst width
  simpa [Array.getElem?_eq_getElem] using (Fin.sum_univ_fun_getElem data.toList id)

/-- A finite array bundled with kernel-checked size and additive checksum facts.  Generated
certificate modules can seal a large literal behind an `opaque` value of this type after checking
it once; downstream proofs then reuse the exact facts without repeatedly normalizing the literal. -/
structure ExactNatArray (width total : ℕ) where
  data : Array ℕ
  size_eq : data.size = width
  sum_eq : data.toList.sum = total

/-- Power-of-two denominator used by a `bits`-bit dyadic certificate. -/
def dyadicDenominator (bits : ℕ) : ℕ := 2 ^ bits

/-- Exact dyadic mass on one finite alphabet. -/
structure DyadicMassData (ι : Type*) where
  numerator : ι → ℕ

namespace DyadicMassData

variable {ι : Type*} [Fintype ι]

/-- The numerators sum to the common dyadic denominator. -/
def IsProbability (bits : ℕ) (data : DyadicMassData ι) : Prop :=
  ∑ i, data.numerator i = dyadicDenominator bits

/-- Interpret dyadic numerators as exact rational weights. -/
def toRational (bits : ℕ) (data : DyadicMassData ι) : RationalProbabilityData ι where
  weight i := data.numerator i / dyadicDenominator bits

/-- An exactly normalized dyadic mass is a rational probability vector. -/
theorem toRational_isProbability {bits : ℕ} {data : DyadicMassData ι}
    (hdata : data.IsProbability bits) :
    (data.toRational bits).IsProbability := by
  constructor
  · intro i
    exact div_nonneg (by positivity) (by positivity)
  · simp only [toRational]
    rw [← Finset.sum_div]
    have hsum : (∑ i, (data.numerator i : ℚ)) = (dyadicDenominator bits : ℚ) := by
      exact_mod_cast hdata
    rw [hsum]
    simp [dyadicDenominator]

end DyadicMassData

/-- A family of dyadic rows with a row-dependent finite alphabet width. -/
structure DyadicTable (Row : Type*) (width : Row → ℕ) where
  numerator : ∀ row, Fin (width row) → ℕ

namespace DyadicTable

variable {Row : Type*} {width : Row → ℕ}

/-- Every row sums to the same dyadic denominator. -/
def IsProbability (bits : ℕ) (table : DyadicTable Row width) : Prop :=
  ∀ row, ∑ symbol, table.numerator row symbol = dyadicDenominator bits

/-- Interpret one table row as exact rational weights. -/
def rowToRational (bits : ℕ) (table : DyadicTable Row width) (row : Row) :
    RationalProbabilityData (Fin (width row)) where
  weight symbol := table.numerator row symbol / dyadicDenominator bits

/-- Every valid dyadic row is a rational probability vector. -/
theorem rowToRational_isProbability
    {bits : ℕ} {table : DyadicTable Row width}
    (htable : table.IsProbability bits) (row : Row) :
    (table.rowToRational bits row).IsProbability := by
  constructor
  · intro symbol
    exact div_nonneg (by positivity) (by positivity)
  · simp only [rowToRational]
    rw [← Finset.sum_div]
    have hsum : (∑ symbol, (table.numerator row symbol : ℚ)) =
        (dyadicDenominator bits : ℚ) := by
      exact_mod_cast htable row
    rw [hsum]
    simp [dyadicDenominator]

end DyadicTable

end AlgebraicComplexity
