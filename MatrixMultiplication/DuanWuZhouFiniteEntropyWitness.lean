/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.AsymmetricLaserLogWitness
import MatrixMultiplication.AsymmetricLaserEntropyWitness
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteData

/-!
# The literal DWZ 022 profile instantiates the shared entropy witness

The law is the published `a`-profile of [duan2023faster], section 6.3,
`global_value.tex:332-378`, already decoded by `dwz63Row022Profile`. Its denominator
is `200000000`, not a dyadic denominator. Three small logarithm atoms instantiate
the shared arithmetic adapter from `better_bound/paper.tex:2496-2512,3537-3546`.

The positive and zero-law examples actually apply both entropy bounds. They do not prove
the full numeric certificate, source extraction, an asymptotic rate or an exponent bound.
Each atom is checked separately against eight atanh terms; no aggregate generated-table
reduction, raised heartbeat option or floating-point comparison is used.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AsymmetricLaserData

private def denominatorAtom : LogAtom :=
  ⟨200000000, 27, 8, 27575424759 / 1000000000, 27575424760 / 1000000000⟩

private def endpointAtom : LogAtom :=
  ⟨6954806, 22, 8, 22729578841 / 1000000000, 22729578842 / 1000000000⟩

private def middleAtom : LogAtom :=
  ⟨186090388, 27, 8, 27471428297 / 1000000000, 27471428298 / 1000000000⟩

private theorem denominatorAtom_valid : denominatorAtom.Valid := by
  norm_num [denominatorAtom, LogAtom.Valid,
    MatrixMultiplication.RationalDyadicLog.numeratorLogLower,
    MatrixMultiplication.RationalDyadicLog.numeratorLogUpper,
    MatrixMultiplication.RationalDyadicLog.logRatioLower,
    MatrixMultiplication.RationalDyadicLog.logRatioUpper,
    MatrixMultiplication.RationalDyadicLog.reducedArgument,
    MatrixMultiplication.RationalDyadicLog.atanhPartial,
    MatrixMultiplication.RationalDyadicLog.atanhRemainder,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoLower,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoUpper, Finset.sum_range_succ]

private theorem endpointAtom_valid : endpointAtom.Valid := by
  norm_num [endpointAtom, LogAtom.Valid,
    MatrixMultiplication.RationalDyadicLog.numeratorLogLower,
    MatrixMultiplication.RationalDyadicLog.numeratorLogUpper,
    MatrixMultiplication.RationalDyadicLog.logRatioLower,
    MatrixMultiplication.RationalDyadicLog.logRatioUpper,
    MatrixMultiplication.RationalDyadicLog.reducedArgument,
    MatrixMultiplication.RationalDyadicLog.atanhPartial,
    MatrixMultiplication.RationalDyadicLog.atanhRemainder,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoLower,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoUpper, Finset.sum_range_succ]

private theorem middleAtom_valid : middleAtom.Valid := by
  norm_num [middleAtom, LogAtom.Valid,
    MatrixMultiplication.RationalDyadicLog.numeratorLogLower,
    MatrixMultiplication.RationalDyadicLog.numeratorLogUpper,
    MatrixMultiplication.RationalDyadicLog.logRatioLower,
    MatrixMultiplication.RationalDyadicLog.logRatioUpper,
    MatrixMultiplication.RationalDyadicLog.reducedArgument,
    MatrixMultiplication.RationalDyadicLog.atanhPartial,
    MatrixMultiplication.RationalDyadicLog.atanhRemainder,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoLower,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoUpper, Finset.sum_range_succ]

private def rowLaw : FiniteLaw := ⟨200000000, [6954806, 186090388, 6954806]⟩

private theorem rowLaw_valid : rowLaw.Valid := by norm_num [rowLaw, FiniteLaw.Valid]

private def rowNumeratorAtom : Fin 3 → LogAtom
  | 0 => endpointAtom
  | 1 => middleAtom
  | _ => endpointAtom

private theorem rowNumeratorAtom_valid (i : Fin 3) : (rowNumeratorAtom i).Valid := by
  fin_cases i
  · exact endpointAtom_valid
  · exact middleAtom_valid
  · exact endpointAtom_valid

private theorem rowNumeratorAtom_argument (i : Fin 3) :
    (rowNumeratorAtom i).argument = rowLaw.profile i := by
  fin_cases i <;> rfl

private theorem row_lower :
    (433782891 : ℝ) / 1000000000 ≤
      (rowLaw.toRational.toReal (rowLaw.toRational_isProbability rowLaw_valid)).entropyBits := by
  have hbound := rowLaw.entropyLower_le rowLaw_valid denominatorAtom.lower
    (fun i => (rowNumeratorAtom i).upper) (denominatorAtom.lower_le denominatorAtom_valid)
    (fun i _ => by
      rw [← rowNumeratorAtom_argument i]
      exact (rowNumeratorAtom i).le_upper (rowNumeratorAtom_valid i))
  have harith : (433782891 : ℚ) / 1000000000 ≤
      rowLaw.entropyLower denominatorAtom.lower (fun i => (rowNumeratorAtom i).upper) := by
    change (433782891 : ℚ) / 1000000000 ≤ denominatorAtom.lower -
      ∑ i : Fin 3, ((rowLaw.profile i : ℚ) / rowLaw.denominator) *
        (rowNumeratorAtom i).upper
    rw [Fin.sum_univ_three, show rowNumeratorAtom 2 = endpointAtom from rfl]
    norm_num [FiniteLaw.profile, rowLaw, rowNumeratorAtom,
      denominatorAtom, endpointAtom, middleAtom]
  calc
    (433782891 : ℝ) / 1000000000 ≤
        (rowLaw.entropyLower denominatorAtom.lower
          (fun i => (rowNumeratorAtom i).upper) : ℝ) := by
      have hc : (((433782891 : ℚ) / 1000000000 : ℚ) : ℝ) ≤
          (rowLaw.entropyLower denominatorAtom.lower
            (fun i => (rowNumeratorAtom i).upper) : ℝ) := Rat.cast_le.mpr harith
      simp only [Rat.cast_div, Rat.cast_ofNat] at hc
      exact hc
    _ ≤ _ := hbound

private theorem row_upper :
    (rowLaw.toRational.toReal (rowLaw.toRational_isProbability rowLaw_valid)).entropyBits ≤
      (433782894 : ℝ) / 1000000000 := by
  have hbound := rowLaw.le_entropyUpper rowLaw_valid denominatorAtom.upper
    (fun i => (rowNumeratorAtom i).lower) (denominatorAtom.le_upper denominatorAtom_valid)
    (fun i _ => by
      rw [← rowNumeratorAtom_argument i]
      exact (rowNumeratorAtom i).lower_le (rowNumeratorAtom_valid i))
  have harith :
      rowLaw.entropyUpper denominatorAtom.upper (fun i => (rowNumeratorAtom i).lower) ≤
        (433782894 : ℚ) / 1000000000 := by
    change denominatorAtom.upper -
      (∑ i : Fin 3, ((rowLaw.profile i : ℚ) / rowLaw.denominator) *
        (rowNumeratorAtom i).lower) ≤ (433782894 : ℚ) / 1000000000
    rw [Fin.sum_univ_three, show rowNumeratorAtom 2 = endpointAtom from rfl]
    norm_num [FiniteLaw.profile, rowLaw, rowNumeratorAtom,
      denominatorAtom, endpointAtom, middleAtom]
  have hc : (rowLaw.entropyUpper denominatorAtom.upper
        (fun i => (rowNumeratorAtom i).lower) : ℝ) ≤
      (((433782894 : ℚ) / 1000000000 : ℚ) : ℝ) := Rat.cast_le.mpr harith
  simp only [Rat.cast_div, Rat.cast_ofNat] at hc
  exact hbound.trans hc

/-- Both shared entropy bounds apply to the actual published 022 law, not a substituted law. -/
theorem dwz63Row022EntropyWitness_bounds :
    (433782891 : ℝ) / 1000000000 ≤
        (dwz63Row022Profile.law.toRational.toReal dwz63Row022Profile_isProbability).entropyBits ∧
      (dwz63Row022Profile.law.toRational.toReal dwz63Row022Profile_isProbability).entropyBits ≤
        (433782894 : ℝ) / 1000000000 := by
  exact ⟨row_lower, row_upper⟩

private theorem zeroLaw_bounds :
    (dwz63Row022ZeroProfile.law.toRational.toReal
      (dwz63Row022ZeroProfile.law.toRational_isProbability
        dwz63Row022ZeroProfile_valid.1.2.2.2)).entropyBits = 0 := by
  have h := dwz63Row022ZeroProfile_valid.1.2.2.2
  have hlower := dwz63Row022ZeroProfile.law.entropyLower_le h 0 (fun _ => 0)
    (by norm_num [dwz63Row022ZeroProfile]) (by
      intro i hi
      fin_cases i <;> simp_all [dwz63Row022ZeroProfile, FiniteLaw.profile])
  have hupper := dwz63Row022ZeroProfile.law.le_entropyUpper h 0 (fun _ => 0)
    (by norm_num [dwz63Row022ZeroProfile]) (by
      intro i hi
      fin_cases i <;> simp_all [dwz63Row022ZeroProfile, FiniteLaw.profile])
  simp only [FiniteLaw.entropyLower, FiniteLaw.entropyUpper, mul_zero,
    Finset.sum_const_zero, sub_zero, Rat.cast_zero] at hlower hupper
  exact le_antisymm hupper hlower

end AlgebraicComplexity.Examples
