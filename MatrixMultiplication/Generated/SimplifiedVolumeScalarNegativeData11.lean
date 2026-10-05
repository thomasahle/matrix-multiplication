import MatrixMultiplication.DyadicLogLinear

/-! Generated scalar-volume logarithm chunk; source certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative11

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    3793, 3796, 3800, 3801, 3802, 3804, 3805, 3807,
    3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815,
    3816, 3817, 3818, 3820, 3824, 3825, 3828, 4096
  ]

def coefficients : Array ℕ := #[
    1304009640648, 236196503712, 103847144800, 31371355848, 52034962816, 1204333451184, 3069566814740, 433526114736,
    1495710543040, 365379052519, 752601987300, 2021217592722, 2205612343424, 1060418688942, 583423621068, 43336240710,
    184781278872, 29546152658, 1208765803528, 832052005020, 102432570240, 118244030400, 30363665376, 244719861706752
  ]

def scales : Array ℕ := #[
    11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 12
  ]

abbrev Term := Fin 24
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem sizes : coefficients.size = arguments.size := by decide
theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 56 argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 4 56 argument coefficient scale
noncomputable def ceiling : ℝ := 43637775343 / 1000000000000

theorem fast_le_ceiling : fastUpper ≤ ceiling := by
  norm_num [ceiling, fastUpper, fastLogSumLowerWithScale, fastLogSumUpperWithScale,
    argument, coefficient, scale, arguments, coefficients, scales,
    MatrixMultiplication.FastDyadicLog.numeratorLogLower,
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper,
    MatrixMultiplication.FastDyadicLog.fastLogTwoLower,
    MatrixMultiplication.FastDyadicLog.fastLogTwoUpper,
    reducedArgument,
    AlgebraicComplexity.Analysis.logRatioLower,
    AlgebraicComplexity.Analysis.logRatioUpper,
    AlgebraicComplexity.Analysis.atanhPartial,
    AlgebraicComplexity.Analysis.atanhRemainder, Fin.sum_univ_succ,
    Finset.sum_range_succ, mass]

theorem exact_bound : exact ≤ ceiling := by
  exact (logSum_le_fastLogSumUpperWithScale 4 56 argument coefficient scale scales_valid).trans fast_le_ceiling

end MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative11
