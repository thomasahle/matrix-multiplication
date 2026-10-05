import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative15

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    7937, 7961, 7965, 7969, 7973, 7975,
    7977, 7985, 7989, 7993, 7997, 8001,
    8005, 8009, 8013, 8017, 8021, 8025,
    8029, 8033, 8037, 8041, 8053, 8057,
    8065, 8097, 8113, 8123, 8125, 8129,
    8137, 8145, 8149, 8165, 8173, 8177,
    8181, 8185, 8189
  ]

def coefficients : Array ℕ := #[
    111230976, 3907820503040, 4396760023040, 1310474649600, 8798695314843648, 547969107492864,
    2439258612334592, 299750785024, 20821928033626112, 549774562684928, 89408247592960, 1375976448000,
    313082671104, 371493298176, 30209484693504, 2488273108992, 996091699200, 2351584051200,
    1109001535488, 1717084815360, 528836173824, 233700802560, 255272878080, 324199219200,
    308109312, 1443463147225088, 267890688, 343597383680, 22723016736768, 79589376,
    137438953472, 268947456, 704214294798336, 501596160, 1305427968, 2461433856,
    3894988800, 11715821568, 2697897003008
  ]

def scales : Array ℕ := #[
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12
  ]

abbrev Term := Fin 39
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 55 argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 8 55 argument coefficient scale
noncomputable def ceiling : ℝ := 12764231083087 / 1000000000000

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
  exact (logSum_le_fastLogSumUpperWithScale 8 55 argument coefficient scale scales_valid).trans fast_le_ceiling

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative15
