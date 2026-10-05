/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineTargets
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibilityContainment

/-!
# Support and coarse mass of the Duan--Wu--Zhou fine targets

The fine target package is defined by finite pushforwards of a thirty-six-entry count table.  This
file records the two normalizations needed by its hashing clients.

First, every raw exact or positive pooled target is supported at the coarse coordinate named by
its cell.  This follows from the actual Coppersmith--Winograd support geometry and does not require
the numerical fine-configuration hypothesis.  Second, `Dwz63FineConfiguration` collapses the fine
table to the committed fifteen-component distribution: after repetition by `k`, the mass over one
component is exactly `proportionalCounts dwz63Alpha (200000000 * k)`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

noncomputable section

/-! ## Coordinate support -/

/-- Total-weight coarsening of a fine split word is its recorded section 6.3 leg coordinate. -/
@[simp] theorem cwSplitWordTotalDigit_dwz63FineSplit
    (c : Leg) (letter : CWDepthOneFineLetter) :
    cwSplitWordTotalDigit 1 (dwz63FineSplit c letter) =
      dwz63LegIndex c (dwz63FineComponent letter) := by
  apply Fin.ext
  exact splitWordWeight_dwz63FineSplit c letter

private theorem dwz63FineExactProfile_weight_eq
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (q : CoarseIndex PUnit) (c : Leg) (word : SplitWord 1)
    (hpositive : 0 < dwz63FineExactProfile fineCount k q c word) :
    splitWordWeight word = q.get c := by
  change 0 < ∑ letter,
    if dwz63FineCoarseIndex letter = q ∧ dwz63FineSplit c letter = word then
      fineCount letter * k
    else 0 at hpositive
  rw [Finset.sum_pos_iff] at hpositive
  obtain ⟨letter, _hletter, hterm⟩ := hpositive
  by_cases hmatch :
      dwz63FineCoarseIndex letter = q ∧ dwz63FineSplit c letter = word
  · calc
      splitWordWeight word = splitWordWeight (dwz63FineSplit c letter) :=
        congrArg splitWordWeight hmatch.2.symm
      _ = (dwz63LegIndex c (dwz63FineComponent letter) : ℕ) :=
        splitWordWeight_dwz63FineSplit c letter
      _ = (dwz63FineCoarseIndex letter).get c := by cases c <;> rfl
      _ = q.get c := congrArg (fun index ↦ index.get c) hmatch.1
  · simp [hmatch] at hterm

private theorem dwz63FineYPooledProfile_weight_eq
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (part : PUnit) (total : ℕ) (word : SplitWord 1)
    (hpositive : 0 < dwz63FineYPooledProfile fineCount k part total word) :
    splitWordWeight word = total := by
  change 0 < ∑ letter,
    if yCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part total ∧
        dwz63FineSplit .Y letter = word then
      fineCount letter * k
    else 0 at hpositive
  rw [Finset.sum_pos_iff] at hpositive
  obtain ⟨letter, _hletter, hterm⟩ := hpositive
  by_cases hmatch :
      yCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part total ∧
        dwz63FineSplit .Y letter = word
  · calc
      splitWordWeight word = splitWordWeight (dwz63FineSplit .Y letter) :=
        congrArg splitWordWeight hmatch.2.symm
      _ = (dwz63FineCoarseIndex letter).y := by
        simpa only [dwz63FineCoarseIndex, dwz63CoarseIndex, dwz63LegIndex] using
          splitWordWeight_dwz63FineSplit .Y letter
      _ = YCompatibilityCell.yValue
          (yCompatibilityCell (dwz63FineCoarseIndex letter)) :=
        (YCompatibilityCell.yValue_yCompatibilityCell _).symm
      _ = YCompatibilityCell.yValue (.pooled part total) :=
        congrArg YCompatibilityCell.yValue hmatch.1
      _ = total := rfl
  · simp [hmatch] at hterm

private theorem dwz63FineZPooledProfile_weight_eq
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (part : PUnit) (total : ℕ) (word : SplitWord 1)
    (hpositive : 0 < dwz63FineZPooledProfile fineCount k part total word) :
    splitWordWeight word = total := by
  change 0 < ∑ letter,
    if zCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part total ∧
        dwz63FineSplit .Z letter = word then
      fineCount letter * k
    else 0 at hpositive
  rw [Finset.sum_pos_iff] at hpositive
  obtain ⟨letter, _hletter, hterm⟩ := hpositive
  by_cases hmatch :
      zCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part total ∧
        dwz63FineSplit .Z letter = word
  · calc
      splitWordWeight word = splitWordWeight (dwz63FineSplit .Z letter) :=
        congrArg splitWordWeight hmatch.2.symm
      _ = (dwz63FineCoarseIndex letter).z := by
        simpa only [dwz63FineCoarseIndex, dwz63CoarseIndex, dwz63LegIndex] using
          splitWordWeight_dwz63FineSplit .Z letter
      _ = ZCompatibilityCell.zValue
          (zCompatibilityCell (dwz63FineCoarseIndex letter)) :=
        (ZCompatibilityCell.zValue_zCompatibilityCell _).symm
      _ = ZCompatibilityCell.zValue (.pooled part total) :=
        congrArg ZCompatibilityCell.zValue hmatch.1
      _ = total := rfl
  · simp [hmatch] at hterm

/-- Every exact and positive pooled row of the fine target package is supported at its recorded
coarse coordinate. -/
theorem dwz63FineCompatibilityTargets_isWeightSupported
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ) :
    (dwz63FineCompatibilityTargets fineCount k).IsWeightSupported := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro q word hpositive
    exact dwz63FineExactProfile_weight_eq fineCount k q .X word hpositive
  · intro q word hpositive
    exact dwz63FineExactProfile_weight_eq fineCount k q .Y word hpositive
  · exact dwz63FineYPooledProfile_weight_eq fineCount k
  · intro q word hpositive
    exact dwz63FineExactProfile_weight_eq fineCount k q .Z word hpositive
  · exact dwz63FineZPooledProfile_weight_eq fineCount k

/-! ## Collapse to the fifteen-component type -/

/-- Total fine-table mass assigned to one coarse section 6.3 component. -/
def dwz63FineComponentMass (fineCount : CWDepthOneFineLetter → ℕ)
    (component : Fin 15) : ℕ :=
  ∑ letter, if dwz63FineComponent letter = component then fineCount letter else 0

private theorem dwz63FineComponentMass_eq_sum_zLeft
    (fineCount : CWDepthOneFineLetter → ℕ) (component : Fin 15) :
    dwz63FineComponentMass fineCount component =
      ∑ left, dwz63FineZLeftCount fineCount component left := by
  classical
  unfold dwz63FineComponentMass dwz63FineZLeftCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro letter _
  by_cases hcomponent : dwz63FineComponent letter = component <;>
    simp [hcomponent]

/-- The named fine-configuration equations recover the committed base component type after the
left `Z` digit is forgotten. -/
theorem dwz63FineComponentMass_eq_proportionalCounts
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount) (component : Fin 15) :
    dwz63FineComponentMass fineCount component =
      WordType.proportionalCounts dwz63Alpha 200000000 component := by
  rw [dwz63FineComponentMass_eq_sum_zLeft]
  calc
    (∑ left, dwz63FineZLeftCount fineCount component left) =
        ∑ left, dwz63SplitCount component left := by
      apply Finset.sum_congr rfl
      intro left _
      exact hconfiguration component left
    _ = WordType.proportionalCounts dwz63Alpha 200000000 component := by
      simpa [dwz63Split, WordType.proportionalCounts] using
        dwz63Split_refinesType 1 component

/-- Component mass commutes with proportional repetition of the fine table. -/
theorem dwz63FineComponentMass_scale
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ) (component : Fin 15) :
    dwz63FineComponentMass (dwz63FineCountScale fineCount k) component =
      dwz63FineComponentMass fineCount component * k := by
  unfold dwz63FineComponentMass dwz63FineCountScale
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro letter _
  by_cases hcomponent : dwz63FineComponent letter = component <;>
    simp [hcomponent]

/-- After repetition by `k`, the fine table has exactly the marked joint type used by the section
6.3 hashing family. -/
theorem dwz63FineComponentMass_scale_eq_proportionalCounts
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k : ℕ) (component : Fin 15) :
    dwz63FineComponentMass (dwz63FineCountScale fineCount k) component =
      WordType.proportionalCounts dwz63Alpha (200000000 * k) component := by
  rw [dwz63FineComponentMass_scale,
    dwz63FineComponentMass_eq_proportionalCounts hconfiguration]
  simp only [WordType.proportionalCounts]
  ring

end

end AlgebraicComplexity.Examples
