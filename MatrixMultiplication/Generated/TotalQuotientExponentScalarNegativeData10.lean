import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative10

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    5877, 5881, 5889, 5897, 5905, 5907,
    5913, 5917, 5921, 5927, 5929, 5933,
    5937, 5945, 5949, 5951, 5953, 5957,
    5961, 5969, 5977, 5985, 5987, 6001,
    6009, 6013, 6015, 6017, 6025, 6035,
    6041, 6047, 6049, 6057, 6065, 6069,
    6071, 6073, 6081, 6083, 6087, 6097,
    6105, 6113, 6121, 6129, 6137, 6145,
    6153, 6155, 6163, 6169, 6177, 6179,
    6181, 6185, 6187, 6193, 6195, 6203,
    6205, 6209, 6223, 6229
  ]

def coefficients : Array ℕ := #[
    755914244096, 2649063997440, 55689683951616, 513571221504, 530990456832, 68719476736,
    855517069312, 1562959872, 1904263004160, 1565601792, 1421101638168576, 309237645312,
    139701338112, 13036850233344, 137438953472, 77996606095360, 6605139214336, 1610121216,
    1298867281920, 938141335552, 2386575360, 2325430272, 137438953472, 107372544000,
    258392064, 6837587935232, 80745385164800, 237077950464, 724110630912, 687194767360,
    9383682150400, 138367619072, 735718588416, 2454741559296, 191311136141312, 208529252155392,
    20100446945280, 81677871187968, 1780104566231040, 209011073216512, 687194767360, 280903680,
    499961150330880, 35973373952, 122909184000, 123069849600, 466136506368, 28569612791808,
    41275293696, 137438953472, 846898831294464, 255982460928, 96583548928, 1328517120,
    424720725966848, 772554752, 80746183307264, 323371008, 1712517120, 137438953472,
    687194767360, 29798400, 855145168502784, 1147944960
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
noncomputable def ceiling : ℝ := 482602016483 / 200000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative10
