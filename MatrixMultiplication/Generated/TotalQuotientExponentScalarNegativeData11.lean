import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative11

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    6239, 6241, 6249, 6257, 6259, 6273,
    6277, 6281, 6285, 6287, 6289, 6305,
    6307, 6315, 6317, 6319, 6321, 6323,
    6327, 6329, 6337, 6339, 6341, 6345,
    6347, 6353, 6361, 6367, 6369, 6375,
    6379, 6385, 6401, 6417, 6423, 6425,
    6427, 6429, 6435, 6449, 6451, 6459,
    6461, 6465, 6483, 6507, 6511, 6513,
    6521, 6523, 6529, 6533, 6545, 6555,
    6561, 6563, 6565, 6589, 6593, 6597,
    6605, 6609, 6611, 6619
  ]

def coefficients : Array ℕ := #[
    1239633420288, 670924800, 403070976, 739909632, 2499194880, 2208587157504,
    82016695484416, 139906744320, 1683627180032, 34359738368, 68719476736, 433310660558848,
    137438953472, 1629315072, 19791209299968, 868408997957632, 855387832320, 217256625700864,
    1088274432, 1360773120, 5280473088, 217806381514752, 1363353600, 686251491328,
    1091715072, 218391589814272, 684374261760, 1642733568, 74373349376, 219318210002944,
    515396075520, 294174720, 1260681371648, 85902540800, 2209579008, 88219918336,
    137438953472, 515396075520, 1374389534720, 206158430208, 2774016000, 1404316866838528,
    2778316800, 139001856, 515396075520, 137438953472, 34359738368, 210051072,
    2804121600, 2404270080, 517724581355520, 2809282560, 211083264, 927506777505792,
    225399883694080, 225468603170816, 137438953472, 226361956368384, 226534260903936, 2634178560,
    137438953472, 227049293234176, 227152230350848, 227427108257792
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
noncomputable def ceiling : ℝ := 1181207712099 / 500000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative11
