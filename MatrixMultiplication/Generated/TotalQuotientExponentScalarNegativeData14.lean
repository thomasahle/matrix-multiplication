import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative14

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    7701, 7705, 7707, 7709, 7713, 7717,
    7721, 7723, 7725, 7729, 7731, 7733,
    7737, 7739, 7741, 7745, 7749, 7753,
    7757, 7759, 7761, 7765, 7767, 7769,
    7773, 7777, 7781, 7785, 7789, 7797,
    7799, 7803, 7805, 7809, 7813, 7817,
    7821, 7823, 7825, 7827, 7835, 7837,
    7845, 7849, 7857, 7861, 7865, 7869,
    7871, 7873, 7877, 7885, 7887, 7889,
    7893, 7897, 7899, 7901, 7905, 7913,
    7917, 7921, 7925, 7931
  ]

def coefficients : Array ℕ := #[
    1230028800, 264710311723008, 264776143863808, 2178465792, 1374093312, 1042956288,
    521748480, 27522150432768, 1360412672, 3355312128, 2748779069440, 2929500160,
    1742766080, 327242148216832, 1497968640, 3717615616, 266254977253376, 1500291072,
    3669270528, 533160060256256, 1978613760, 266773969698816, 266837728165888, 5249925120,
    27217592401920, 17786782089216, 9552097280, 2654281728, 5430915072, 1676451840,
    185511051264, 68719476736, 345275555840, 3263619072, 1079930880, 70112100352,
    1321267200, 412316860416, 1321943040, 2151709895819264, 538382740488192, 1685053440,
    4385611776, 1253670912, 8993800192, 1255587840, 10629611520, 1812787200,
    1081816362516480, 101265408, 1814630400, 1619261079552, 22055257939968, 2814781685760,
    542649867173888, 5287919616, 15152644620288, 2232729600, 3059417088, 12668825042944,
    5009498112, 547481854402560, 3222159575040, 545014169993216
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
noncomputable def ceiling : ℝ := 111015621887 / 40000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative14
