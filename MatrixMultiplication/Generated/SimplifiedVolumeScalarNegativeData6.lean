import MatrixMultiplication.DyadicLogLinear

/-! Generated scalar-volume logarithm chunk; source certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative6

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045,
    2046, 2047, 2048, 2049, 2050, 2051, 2052, 2053,
    2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061
  ]

def coefficients : Array ℕ := #[
    116735995992, 12484417232172, 32514948000, 160602191153586, 536326310189220, 38547334966824, 886227686038016, 480174552157280,
    690663109824468, 638003914032415, 16307933872746496, 638627269102305, 692013379833900, 481583377249184, 889696287548928, 38736015020504,
    539478080866140, 161703823038030, 32769967200, 12594627879636, 117881589672, 235075349376960, 25136206618880, 37066465723086
  ]

def scales : Array ℕ := #[
    10, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11
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
noncomputable def ceiling : ℝ := 1793951073459 / 500000000000

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

end MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative6
