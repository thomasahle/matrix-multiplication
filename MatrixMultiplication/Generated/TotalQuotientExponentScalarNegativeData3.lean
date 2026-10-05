import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative3

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    947, 961, 977, 983, 985, 993,
    1003, 1005, 1007, 1011, 1019, 1045,
    1055, 1061, 1065, 1067, 1069, 1075,
    1105, 1137, 1153, 1159, 1161, 1165,
    1167, 1223, 1235, 1259, 1265, 1269,
    1283, 1321, 1359, 1361, 1365, 1385,
    1407, 1411, 1413, 1437, 1445, 1447,
    1497, 1517, 1519, 1543, 1575, 1579,
    1585, 1591, 1597, 1599, 1603, 1613,
    1623, 1629, 1641, 1643, 1651, 1657,
    1661, 1703, 1777, 1835
  ]

def coefficients : Array ℕ := #[
    65077344468992, 132078834286592, 33569464385536, 5378731313458584, 2726063001944200, 10721058341744,
    2257398346423904, 31095563223040, 34462817583104, 138950781960192, 70025146793984, 23272280293376,
    34288871407616, 4367981740032, 36558761623552, 36593121361920, 33225867001856, 16919486791680,
    37634650931200, 32057635897344, 79078937853952, 39822936768512, 23212150751232, 120087285596160,
    154584462917632, 45904610459648, 30477087932416, 43258910605312, 43465069035520, 87205015977984,
    87187836108800, 45389214384128, 46694884442112, 45664092291072, 140703128616960, 47588237639680,
    96688303767552, 48481590837248, 11184094838784, 49374944034816, 49546742726656, 49718541418496,
    51299089383424, 52123723104256, 156577327742976, 52467320487936, 54116587929600, 54221814628352,
    54322746359808, 54666343743488, 54803782696960, 109470126440448, 55078660603904, 36221606690816,
    55765855371264, 55972013801472, 154713311936512, 56298431315968, 38001870635008, 113868172951552,
    171214576287744, 117029268881408, 121908351729664, 2144902108805
  ]

def scales : Array ℕ := #[
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10
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
noncomputable def ceiling : ℝ := 4958714927 / 1250000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative3
