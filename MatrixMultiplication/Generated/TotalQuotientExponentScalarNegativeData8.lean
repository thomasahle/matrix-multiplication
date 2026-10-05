import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative8

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    5235, 5237, 5239, 5243, 5247, 5249,
    5253, 5257, 5263, 5267, 5271, 5273,
    5275, 5279, 5287, 5289, 5291, 5297,
    5299, 5301, 5313, 5317, 5329, 5337,
    5345, 5347, 5351, 5355, 5361, 5367,
    5369, 5373, 5377, 5385, 5389, 5401,
    5405, 5407, 5413, 5415, 5427, 5429,
    5435, 5441, 5449, 5451, 5455, 5457,
    5463, 5467, 5475, 5477, 5481, 5485,
    5489, 5491, 5493, 5497, 5503, 5505,
    5511, 5513, 5521, 5537
  ]

def coefficients : Array ℕ := #[
    355149594624, 89689915392, 60760129536, 1825001041920, 360536734695424, 99278739898368,
    4731111849984, 2421964800, 1890276089856, 4076642304, 2104627200, 2573835086315520,
    1036910592, 834889874337792, 6170664960, 276702003200, 3575193600, 3872096256,
    911425536, 511769568460800, 3217117184, 1306460160, 562411938963456, 3337995582930944,
    527768993792, 3481657344, 558796800, 1421567166038016, 1317273600, 34359738368,
    1154334720, 1238567854080, 2385895948288, 99237888, 463454208, 99532800,
    68719476736, 1328578560, 731529216, 186057983262720, 186435940384768, 186539019599872,
    481036337152, 111515299840, 100417536, 187294933843968, 670187520, 167608320,
    687194767360, 2336462209024, 189356518146048, 618475290624, 404029440, 68719476736,
    188600873648128, 188669795606528, 188738042855424, 340849246191616, 189082045890560, 459809257848832,
    481036337152, 755914244096, 271319040, 1139441664
  ]

def scales : Array ℕ := #[
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12,
    12, 12, 12, 12
  ]

abbrev Term := Fin 64
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 55 argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 8 55 argument coefficient scale
noncomputable def ceiling : ℝ := 4197761240033 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative8
