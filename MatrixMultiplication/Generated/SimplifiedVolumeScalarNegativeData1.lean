import MatrixMultiplication.DyadicLogLinear

/-! Generated scalar-volume logarithm chunk; source certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative1

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    51, 53, 106, 116, 119, 120, 121, 122,
    126, 127, 128, 133, 134, 135, 136, 137,
    138, 139, 140, 141, 142, 143, 144, 145
  ]

def coefficients : Array ℕ := #[
    31583310446592, 64231705673728, 42681237504, 46707769344, 359256163352576, 48318382080, 189240621137920, 49123688448,
    389132090081280, 143304922497024, 633488348807168, 40164655104, 15614655520, 99300133440, 134702105216, 55163486208,
    60116846436, 89089807374, 16232389880, 83951892372, 279124364680, 146053901279, 143332343856, 191871032500
  ]

def scales : Array ℕ := #[
    5, 5, 6, 6, 6, 6, 6, 6,
    6, 6, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7
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
noncomputable def ceiling : ℝ := 17340944007 / 100000000000

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

end MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative1
