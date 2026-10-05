/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.AsymmetricLaserIntegerDualWitness
import MatrixMultiplication.AsymmetricLaserEntropyWitness
import MatrixMultiplication.DuanWuZhouFiniteIntegerDual

/-!
# A finite-atom combination-loss certificate for the full DWZ global law

This transcribes the fixed-marginal maximum in [duan2023faster],
`second_power.tex:536-563` and `global_value.tex:286-309`, for the complete
fifteen-state law of `global_value.tex:350-375`. It uses the existing positive
integer Gibbs factors, with physical Z in the committed coordinate order.

Each positive integer log has its own twelve-term rational-atanh proof. The
upper partition and lower factor endpoints bound the dual; the lower reference
entropy is subtracted. All fifteen states remain in the partition. This finite
gap certificate does not prove native extraction, full DAG Checks or an exponent.
The shared atom endpoints are not identified with a different log evaluator.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open AsymmetricLaserData

-- Local syntax only: every use checks one closed atom, never an aggregate table.
local macro "check_dual_atom" : tactic => `(tactic|
  norm_num [LogAtom.Valid,
    MatrixMultiplication.RationalDyadicLog.numeratorLogLower,
    MatrixMultiplication.RationalDyadicLog.numeratorLogUpper,
    MatrixMultiplication.RationalDyadicLog.logRatioLower,
    MatrixMultiplication.RationalDyadicLog.logRatioUpper,
    MatrixMultiplication.RationalDyadicLog.reducedArgument,
    MatrixMultiplication.RationalDyadicLog.atanhPartial,
    MatrixMultiplication.RationalDyadicLog.atanhRemainder,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoLower,
    MatrixMultiplication.RationalDyadicLog.fastLogTwoUpper, Finset.sum_range_succ])

private def logAtom968 : LogAtom :=
  ⟨968, 9, 12, 9918863237274572 / 1000000000000000, 9918863237275101 / 1000000000000000⟩

private theorem logAtom968_valid : logAtom968.Valid := by
  unfold logAtom968
  check_dual_atom

private def logAtom9210 : LogAtom :=
  ⟨9210, 13, 12, 13168985440978697 / 1000000000000000, 13168985440978698 / 1000000000000000⟩

private theorem logAtom9210_valid : logAtom9210.Valid := by
  unfold logAtom9210
  check_dual_atom

private def logAtom12576 : LogAtom :=
  ⟨12576, 13, 12, 13618385502258605 / 1000000000000000, 13618385502258607 / 1000000000000000⟩

private theorem logAtom12576_valid : logAtom12576.Valid := by
  unfold logAtom12576
  check_dual_atom

private def logAtom20099 : LogAtom :=
  ⟨20099, 14, 12, 14294836103295443 / 1000000000000000, 14294836103295444 / 1000000000000000⟩

private theorem logAtom20099_valid : logAtom20099.Valid := by
  unfold logAtom20099
  check_dual_atom

private def logAtom20860 : LogAtom :=
  ⟨20860, 14, 12, 14348451537407127 / 1000000000000000, 14348451537407129 / 1000000000000000⟩

private theorem logAtom20860_valid : logAtom20860.Valid := by
  unfold logAtom20860
  check_dual_atom

private def logAtom24731 : LogAtom :=
  ⟨24731, 14, 12, 14594032955948255 / 1000000000000000, 14594032955948257 / 1000000000000000⟩

private theorem logAtom24731_valid : logAtom24731.Valid := by
  unfold logAtom24731
  check_dual_atom

private def logAtom41762 : LogAtom :=
  ⟨41762, 15, 12, 15349903184392816 / 1000000000000000, 15349903184392817 / 1000000000000000⟩

private theorem logAtom41762_valid : logAtom41762.Valid := by
  unfold logAtom41762
  check_dual_atom

private def logAtom101843 : LogAtom :=
  ⟨101843, 16, 12, 16635987297034748 / 1000000000000000, 16635987297034750 / 1000000000000000⟩

private theorem logAtom101843_valid : logAtom101843.Valid := by
  unfold logAtom101843
  check_dual_atom

private def logAtom128169 : LogAtom :=
  ⟨128169, 16, 12, 16967687836592829 / 1000000000000000, 16967687836594608 / 1000000000000000⟩

private theorem logAtom128169_valid : logAtom128169.Valid := by
  unfold logAtom128169
  check_dual_atom

private def logAtom219270 : LogAtom :=
  ⟨219270, 17, 12, 17742348913845110 / 1000000000000000, 17742348913845116 / 1000000000000000⟩

private theorem logAtom219270_valid : logAtom219270.Valid := by
  unfold logAtom219270
  check_dual_atom

private def logAtom261024 : LogAtom :=
  ⟨261024, 17, 12, 17993822936745783 / 1000000000000000, 17993822936749101 / 1000000000000000⟩

private theorem logAtom261024_valid : logAtom261024.Valid := by
  unfold logAtom261024
  check_dual_atom

private def logAtom470879 : LogAtom :=
  ⟨470879, 18, 12, 18844996857997111 / 1000000000000000, 18844996857997185 / 1000000000000000⟩

private theorem logAtom470879_valid : logAtom470879.Valid := by
  unfold logAtom470879
  check_dual_atom

private def logAtom542361 : LogAtom :=
  ⟨542361, 19, 12, 19048893915577925 / 1000000000000000, 19048893915577926 / 1000000000000000⟩

private theorem logAtom542361_valid : logAtom542361.Valid := by
  unfold logAtom542361
  check_dual_atom

private def logAtom1211153 : LogAtom :=
  ⟨1211153, 20, 12, 20207949695626904 / 1000000000000000, 20207949695626906 / 1000000000000000⟩

private theorem logAtom1211153_valid : logAtom1211153.Valid := by
  unfold logAtom1211153
  check_dual_atom

private def logAtom1223123 : LogAtom :=
  ⟨1223123, 20, 12, 20222138061143087 / 1000000000000000, 20222138061143088 / 1000000000000000⟩

private theorem logAtom1223123_valid : logAtom1223123.Valid := by
  unfold logAtom1223123
  check_dual_atom

private def logAtom1251758 : LogAtom :=
  ⟨1251758, 20, 12, 20255524245056163 / 1000000000000000, 20255524245056165 / 1000000000000000⟩

private theorem logAtom1251758_valid : logAtom1251758.Valid := by
  unfold logAtom1251758
  check_dual_atom

private def logAtom1322632 : LogAtom :=
  ⟨1322632, 20, 12, 20334980281260633 / 1000000000000000, 20334980281260634 / 1000000000000000⟩

private theorem logAtom1322632_valid : logAtom1322632.Valid := by
  unfold logAtom1322632
  check_dual_atom

private def logAtom1333318 : LogAtom :=
  ⟨1333318, 20, 12, 20346589477514648 / 1000000000000000, 20346589477514649 / 1000000000000000⟩

private theorem logAtom1333318_valid : logAtom1333318.Valid := by
  unfold logAtom1333318
  check_dual_atom

private def logAtom1491349 : LogAtom :=
  ⟨1491349, 20, 12, 20508186480634998 / 1000000000000000, 20508186480635000 / 1000000000000000⟩

private theorem logAtom1491349_valid : logAtom1491349.Valid := by
  unfold logAtom1491349
  check_dual_atom

private def logAtom1664528 : LogAtom :=
  ⟨1664528, 20, 12, 20666681708424389 / 1000000000000000, 20666681708424391 / 1000000000000000⟩

private theorem logAtom1664528_valid : logAtom1664528.Valid := by
  unfold logAtom1664528
  check_dual_atom

private def logAtom10045791 : LogAtom :=
  ⟨10045791, 23, 12, 23260087829760943 / 1000000000000000, 23260087829760945 / 1000000000000000⟩

private theorem logAtom10045791_valid : logAtom10045791.Valid := by
  unfold logAtom10045791
  check_dual_atom

private def logAtom10366945 : LogAtom :=
  ⟨10366945, 23, 12, 23305487478064511 / 1000000000000000, 23305487478064512 / 1000000000000000⟩

private theorem logAtom10366945_valid : logAtom10366945.Valid := by
  unfold logAtom10366945
  check_dual_atom

private def logAtom20088623 : LogAtom :=
  ⟨20088623, 24, 12, 24259875340320747 / 1000000000000000, 24259875340320749 / 1000000000000000⟩

private theorem logAtom20088623_valid : logAtom20088623.Valid := by
  unfold logAtom20088623
  check_dual_atom

private def logAtom20734458 : LogAtom :=
  ⟨20734458, 24, 12, 24305526999811713 / 1000000000000000, 24305526999811714 / 1000000000000000⟩

private theorem logAtom20734458_valid : logAtom20734458.Valid := by
  unfold logAtom20734458
  check_dual_atom

private def logAtom100000000 : LogAtom :=
  ⟨100000000, 26, 12, 26575424759098898 / 1000000000000000,
    26575424759098900 / 1000000000000000⟩

private theorem logAtom100000000_valid : logAtom100000000.Valid := by
  unfold logAtom100000000
  check_dual_atom

private def logAtom999999264240775404 : LogAtom :=
  ⟨999999264240775404, 59, 12, 59794704646495945 / 1000000000000000,
    59794704646495964 / 1000000000000000⟩

private theorem logAtom999999264240775404_valid : logAtom999999264240775404.Valid := by
  unfold logAtom999999264240775404
  check_dual_atom

private abbrev globalLaw : FiniteLaw :=
  ⟨100000000, [20860, 1211153, 10366945, 1333318, 24731,
    1211153, 20088623, 20734458, 1251758, 10366945,
    20734458, 10045791, 1333318, 1251758, 24731]⟩

private theorem globalLaw_valid : globalLaw.Valid := by
  norm_num [globalLaw, FiniteLaw.Valid]

private theorem globalLaw_profile (i : Fin 15) :
    globalLaw.profile i = dwz63Alpha i := by
  fin_cases i <;> rfl

private theorem globalLaw_weight :
    (globalLaw.toRational.toReal
      (globalLaw.toRational_isProbability globalLaw_valid)).weight =
      (fun i : Fin 15 => (dwz63Alpha i : ℝ) / 100000000) := by
  funext i
  simp only [RationalProbabilityData.toReal_weight, FiniteLaw.toRational,
    Rat.cast_div, Rat.cast_natCast, globalLaw_profile]
  rfl

private def xAtom : Fin 5 → LogAtom
  | 0 => logAtom41762
  | 1 => logAtom101843
  | 2 => logAtom128169
  | 3 => logAtom20099
  | 4 => logAtom968

private theorem xAtom_valid (i : Fin 5) : (xAtom i).Valid := by
  fin_cases i
  · exact logAtom41762_valid
  · exact logAtom101843_valid
  · exact logAtom128169_valid
  · exact logAtom20099_valid
  · exact logAtom968_valid

private theorem xAtom_argument (i : Fin 5) :
    (xAtom i).argument = dwz63IntegerGibbsX i := by
  fin_cases i <;> rfl

private def yAtom : Fin 5 → LogAtom
  | 0 => logAtom542361
  | 1 => logAtom1322632
  | 2 => logAtom1664528
  | 3 => logAtom261024
  | 4 => logAtom12576

private theorem yAtom_valid (i : Fin 5) : (yAtom i).Valid := by
  fin_cases i
  · exact logAtom542361_valid
  · exact logAtom1322632_valid
  · exact logAtom1664528_valid
  · exact logAtom261024_valid
  · exact logAtom12576_valid

private theorem yAtom_argument (i : Fin 5) :
    (yAtom i).argument = dwz63IntegerGibbsY i := by
  fin_cases i <;> rfl

private def zAtom : Fin 5 → LogAtom
  | 0 => logAtom470879
  | 1 => logAtom1223123
  | 2 => logAtom1491349
  | 3 => logAtom219270
  | 4 => logAtom9210

private theorem zAtom_valid (i : Fin 5) : (zAtom i).Valid := by
  fin_cases i
  · exact logAtom470879_valid
  · exact logAtom1223123_valid
  · exact logAtom1491349_valid
  · exact logAtom219270_valid
  · exact logAtom9210_valid

private theorem zAtom_argument (i : Fin 5) :
    (zAtom i).argument = dwz63IntegerGibbsZ i := by
  fin_cases i <;> rfl

private def numeratorAtom : Fin 15 → LogAtom
  | 0 => logAtom20860
  | 1 => logAtom1211153
  | 2 => logAtom10366945
  | 3 => logAtom1333318
  | 4 => logAtom24731
  | 5 => logAtom1211153
  | 6 => logAtom20088623
  | 7 => logAtom20734458
  | 8 => logAtom1251758
  | 9 => logAtom10366945
  | 10 => logAtom20734458
  | 11 => logAtom10045791
  | 12 => logAtom1333318
  | 13 => logAtom1251758
  | 14 => logAtom24731

private theorem numeratorAtom_valid (i : Fin 15) : (numeratorAtom i).Valid := by
  fin_cases i
  · exact logAtom20860_valid
  · exact logAtom1211153_valid
  · exact logAtom10366945_valid
  · exact logAtom1333318_valid
  · exact logAtom24731_valid
  · exact logAtom1211153_valid
  · exact logAtom20088623_valid
  · exact logAtom20734458_valid
  · exact logAtom1251758_valid
  · exact logAtom10366945_valid
  · exact logAtom20734458_valid
  · exact logAtom10045791_valid
  · exact logAtom1333318_valid
  · exact logAtom1251758_valid
  · exact logAtom24731_valid

private theorem numeratorAtom_argument (i : Fin 15) :
    (numeratorAtom i).argument = globalLaw.profile i := by
  fin_cases i <;> rfl

private theorem partitionAtom_argument :
    logAtom999999264240775404.argument =
      MatrixMultiplication.IntegerEntropyDual.integerPartitionNumerator
        dwz63XIndex dwz63YIndex dwz63ZIndex (fun x => (xAtom x).argument)
        (fun y => (yAtom y).argument) (fun z => (zAtom z).argument) := by
  simp only [xAtom_argument, yAtom_argument, zAtom_argument, dwz63_integerPartition_eq]
  rfl

private def referenceEntropyLower : ℚ :=
  globalLaw.entropyLower logAtom100000000.lower (fun i => (numeratorAtom i).upper)

private theorem referenceEntropyLower_le :
    (referenceEntropyLower : ℝ) ≤ MaximumEntropyDual.entropyBits
      (globalLaw.toRational.toReal
        (globalLaw.toRational_isProbability globalLaw_valid)).weight := by
  have h := globalLaw.entropyLower_le globalLaw_valid logAtom100000000.lower
    (fun i => (numeratorAtom i).upper) (logAtom100000000.lower_le logAtom100000000_valid)
    (fun i _ => by
      rw [← numeratorAtom_argument i]
      exact (numeratorAtom i).le_upper (numeratorAtom_valid i))
  simpa only [referenceEntropyLower, ProbabilityVector.entropyBits, ProbabilityVector.entropy,
    MaximumEntropyDual.entropyBits, MaximumEntropyDual.entropy] using h

private def dualUpper : ℚ :=
  integerDualUpper dwz63XIndex dwz63YIndex dwz63ZIndex globalLaw.toRational
    logAtom999999264240775404.upper (fun x => (xAtom x).lower)
    (fun y => (yAtom y).lower) (fun z => (zAtom z).lower)

private def gapCostNumerator : Fin 15 → ℕ :=
  ![33219331003542309, 33219282683871653, 33219283895387691,
    33219274704767037, 33219252588700275, 33219280430830877,
    33219278718609630, 33219280066790510, 33219282846721477,
    33219280754741240, 33219279179184835, 33219278573253384,
    33219278602501806, 33219288997497022, 33218721054901351]

-- Each closed case checks three potential endpoints and one entropy endpoint.
private theorem gapCost_eq (i : Fin 15) :
    (xAtom (dwz63XIndex i)).lower + (yAtom (dwz63YIndex i)).lower +
        (zAtom (dwz63ZIndex i)).lower - (numeratorAtom i).upper =
      (gapCostNumerator i : ℚ) / 1000000000000000 := by
  fin_cases i
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom9210, logAtom20860, logAtom41762, logAtom542361]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom41762, logAtom219270, logAtom1211153, logAtom1322632]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom41762, logAtom1491349, logAtom1664528, logAtom10366945]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom41762, logAtom261024, logAtom1223123, logAtom1333318]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom12576, logAtom24731, logAtom41762, logAtom470879]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom101843, logAtom219270, logAtom542361, logAtom1211153]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom101843, logAtom1322632, logAtom1491349, logAtom20088623]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom101843, logAtom1223123, logAtom1664528, logAtom20734458]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom101843, logAtom261024, logAtom470879, logAtom1251758]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom128169, logAtom542361, logAtom1491349, logAtom10366945]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom128169, logAtom1223123, logAtom1322632, logAtom20734458]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom128169, logAtom470879, logAtom1664528, logAtom10045791]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom20099, logAtom542361, logAtom1223123, logAtom1333318]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom20099, logAtom470879, logAtom1251758, logAtom1322632]
  · norm_num [xAtom, yAtom, zAtom, numeratorAtom, gapCostNumerator,
      dwz63XIndex, dwz63YIndex, dwz63ZIndex,
      logAtom968, logAtom24731, logAtom470879, logAtom542361]

private theorem rationalGap_le : dualUpper - referenceEntropyLower ≤ 3 / 100000000000 := by
  have hform : dualUpper - referenceEntropyLower =
      logAtom999999264240775404.upper - logAtom100000000.lower -
        ∑ i : Fin 15, globalLaw.toRational.weight i *
          ((xAtom (dwz63XIndex i)).lower + (yAtom (dwz63YIndex i)).lower +
            (zAtom (dwz63ZIndex i)).lower - (numeratorAtom i).upper) := by
    change _ - (∑ i : Fin 15, _) - (_ - ∑ i : Fin 15, _) = _
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hform]
  simp only [gapCost_eq]
  norm_num [FiniteLaw.toRational, FiniteLaw.profile, globalLaw, gapCostNumerator, Fin.sum_univ_succ,
    logAtom999999264240775404, logAtom100000000]

/-- The complete published global law has combination loss at most `3 * 10^-11` bits.
This is a component certificate, not a bound on the matrix-multiplication exponent. -/
theorem dwz63_integerAtomGap_bound :
    MaximumEntropyDual.combinationLossBits dwz63XIndex dwz63YIndex dwz63ZIndex
        (fun i : Fin 15 => (dwz63Alpha i : ℝ) / 100000000) ≤ 3 / 100000000000 := by
  have hbound := integerDualGapUpper_bounds dwz63XIndex dwz63YIndex dwz63ZIndex
    globalLaw.toRational (globalLaw.toRational_isProbability globalLaw_valid)
    logAtom999999264240775404 xAtom yAtom zAtom logAtom999999264240775404_valid
    xAtom_valid yAtom_valid zAtom_valid partitionAtom_argument
    referenceEntropyLower referenceEntropyLower_le
  rw [globalLaw_weight] at hbound
  have hcast : ((dualUpper - referenceEntropyLower : ℚ) : ℝ) ≤
      (((3 : ℚ) / 100000000000 : ℚ) : ℝ) := Rat.cast_le.mpr rationalGap_le
  simp only [Rat.cast_div, Rat.cast_ofNat] at hcast
  exact hbound.trans hcast

end AlgebraicComplexity.Examples
