import MatrixMultiplication.DyadicLogLinear

/-! Generated scalar-volume logarithm chunk; source certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative4

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    237, 238, 239, 240, 241, 553, 604, 605,
    606, 607, 611, 643, 654, 666, 673, 674,
    722, 764, 773, 777, 890, 891, 892, 896
  ]

def coefficients : Array ℕ := #[
    4472254464, 1442622720, 560483202, 1572619680, 118201824, 20782273003520, 22192230236160, 22228972339200,
    22306382413824, 22343191625728, 43955769049088, 25135457239040, 23744055607296, 48359452704768, 26308184637440, 26347275550720,
    54266911784960, 27481348243456, 28453520801792, 28548614062080, 275579865661440, 275889505959936, 1081031725678592, 573335184343040
  ]

def scales : Array ℕ := #[
    7, 7, 7, 7, 7, 9, 9, 9,
    9, 9, 9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9, 9, 9
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
noncomputable def ceiling : ℝ := 44706424993 / 125000000000

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

end MatrixMultiplication.Generated.SimplifiedVolumeScalar.Negative4
