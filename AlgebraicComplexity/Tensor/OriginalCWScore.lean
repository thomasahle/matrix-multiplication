import AlgebraicComplexity.Tensor.OriginalCWSupport
import AlgebraicComplexity.Tensor.OriginalCWNumerics
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The tight-support laser score of the original Coppersmith--Winograd certificate

This file reconstructs the two-level logarithmic score from the exact finite support data. The
entropy contribution is the average of the three coordinate marginal entropies, while the local
contribution is the mass-weighted logarithmic value of each constituent. The resulting inner and
outer scores are proved equal to the closed formulas used by the kernel-checked numerical module.
-/

namespace AlgebraicComplexity
namespace OriginalCW

/-- Shannon's `p log₂(1/p)` atom for a positive rational mass. -/
noncomputable def entropyAtom (p : ℚ) : ℝ :=
  if p = 0 then 0 else (p : ℝ) * log2 (1 / (p : ℝ))

@[simp] theorem entropyAtom_zero : entropyAtom 0 = 0 := by
  simp [entropyAtom]

/-- `log₂ 2 = 1`. -/
@[simp] theorem log2_two : log2 2 = 1 := by
  unfold log2
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- Entropy of one coordinate marginal of the four-point inner support. -/
noncomputable def innerMarginalEntropy : Fin 3 → ℝ
  | 0 => entropyAtom (innerMarginal 0 0) + entropyAtom (innerMarginal 0 1) +
      entropyAtom (innerMarginal 0 2)
  | 1 => entropyAtom (innerMarginal 1 0) + entropyAtom (innerMarginal 1 1)
  | 2 => entropyAtom (innerMarginal 2 0) + entropyAtom (innerMarginal 2 1)

/-- Average of the three inner marginal entropies. -/
noncomputable def innerEntropyAverage : ℝ :=
  (innerMarginalEntropy 0 + innerMarginalEntropy 1 + innerMarginalEntropy 2) / 3

/-- Local logarithmic matrix-multiplication value of one inner support point. -/
noncomputable def innerLocalLog : InnerPoint → ℝ
  | .edgeLeft | .edgeRight => ((rho : ℝ) / 3) * log2 6
  | .crossLeft | .crossRight => (2 * (rho : ℝ) / 3) * log2 6

/-- Mass-weighted local value contribution of the inner support. -/
noncomputable def innerLocalAverage : ℝ :=
  innerSum fun point => (innerMass point : ℝ) * innerLocalLog point

/-- Complete tight-support score of the exceptional `(2,1,1)` component. -/
noncomputable def innerLaserScore : ℝ :=
  innerEntropyAverage + innerLocalAverage

/-- The finite-support score is exactly the historical closed inner formula. -/
theorem innerLaserScore_eq_innerLogLower : innerLaserScore = innerLogLower := by
  rw [show innerLaserScore =
      ((entropyAtom b1 + entropyAtom (2 * b2) + entropyAtom b1) +
        (entropyAtom (1 / 2) + entropyAtom (1 / 2)) +
        (entropyAtom (1 / 2) + entropyAtom (1 / 2))) / 3 +
      (2 * (b1 : ℝ)) * (((rho : ℝ) / 3) * log2 6) +
      (2 * (b2 : ℝ)) * ((2 * (rho : ℝ) / 3) * log2 6) by
    simp [innerLaserScore, innerEntropyAverage, innerMarginalEntropy,
      innerLocalAverage, innerSum, innerMass, innerLocalLog]
    ring]
  norm_num [entropyAtom, b1, b2, rho, innerLogLower]
  ring

/-- Entropy of one five-valued outer coordinate marginal. -/
noncomputable def outerMarginalEntropy (coordinate : Fin 3) : ℝ :=
  entropyAtom (outerMarginal coordinate 0) +
  entropyAtom (outerMarginal coordinate 1) +
  entropyAtom (outerMarginal coordinate 2) +
  entropyAtom (outerMarginal coordinate 3) +
  entropyAtom (outerMarginal coordinate 4)

/-- Average of the three outer marginal entropies. -/
noncomputable def outerEntropyAverage : ℝ :=
  (outerMarginalEntropy 0 + outerMarginalEntropy 1 + outerMarginalEntropy 2) / 3

/-- Local logarithmic value of one tensor-square support component. -/
noncomputable def outerLocalLog : OuterPoint → ℝ
  | .p400 | .p040 | .p004 => 0
  | .p310 | .p301 | .p130 | .p031 | .p103 | .p013 =>
      ((rho : ℝ) / 3) * log2 12
  | .p220 | .p202 | .p022 => ((rho : ℝ) / 3) * log2 38
  | .p211 | .p121 | .p112 => innerLaserScore

/-- Mass-weighted local value contribution of the outer support. -/
noncomputable def outerLocalAverage : ℝ :=
  outerSum fun point => (outerMass point : ℝ) * outerLocalLog point

/-- Complete tight-support score of the `CW₆` tensor square. -/
noncomputable def outerLaserScore : ℝ :=
  outerEntropyAverage + outerLocalAverage

/-- The exact finite-support score equals the closed expression checked in `OriginalCWNumerics`. -/
theorem outerLaserScore_eq_squareLogLower : outerLaserScore = squareLogLower := by
  rw [show outerLaserScore =
      (entropyAtom (16 / 125) + entropyAtom (65419 / 150000) +
        entropyAtom (123193 / 300000) + entropyAtom (1 / 40) +
        entropyAtom (23 / 100000)) +
      (6 * (a2 : ℝ)) * (((rho : ℝ) / 3) * log2 12) +
      (3 * (a3 : ℝ)) * (((rho : ℝ) / 3) * log2 38) +
      (3 * (a4 : ℝ)) * innerLaserScore by
    simp [outerLaserScore, outerEntropyAverage, outerMarginalEntropy,
      outerLocalAverage, outerSum, outerMass, outerLocalLog]
    ring]
  rw [innerLaserScore_eq_innerLogLower]
  norm_num [entropyAtom, a1, a2, a3, a4, rho, squareLogLower]
  ring

/-- Consequently the exact finite-support laser score exceeds the border-rank logarithm `6`. -/
theorem outerLaserScore_gt_six : 6 < outerLaserScore := by
  rw [outerLaserScore_eq_squareLogLower]
  exact squareLogLower_gt_six

#print axioms innerLaserScore_eq_innerLogLower
#print axioms outerLaserScore_eq_squareLogLower
#print axioms outerLaserScore_gt_six

end OriginalCW
end AlgebraicComplexity
