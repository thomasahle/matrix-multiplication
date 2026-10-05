import MatrixMultiplication.DyadicLogLinear

/-! Generated scalar-volume logarithm chunk; source certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientVolumeScalar.Negative6

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    780, 781, 807, 811, 841, 966, 976, 978,
    1018, 1024, 1025, 1028, 1070, 1072, 1082, 1147,
    1163, 1248, 1398, 1451, 1542, 2007, 2008, 2009
  ]

def coefficients : Array ℕ := #[
    17470115020800, 34985025208320, 33983425413120, 50942070226944, 17707596513280, 5964098961408, 7434051518464, 6924225478656,
    3569554030592, 27968827031552, 7188198195200, 3604618412032, 7575584112640, 8165269700608, 6680284758016, 336452772691968,
    392501424816128, 389655539220480, 631443340394496, 647592182546432, 674391335632896, 100295875224, 7397180840, 308077337400
  ]

def scales : Array ℕ := #[
    9, 9, 9, 9, 9, 9, 9, 9,
    9, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10
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
  fastLogSumUpperWithScale 6 56 argument coefficient scale
noncomputable def ceiling : ℝ := 476259723451 / 1000000000000

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
  exact (logSum_le_fastLogSumUpperWithScale 6 56 argument coefficient scale scales_valid).trans fast_le_ceiling

end MatrixMultiplication.Generated.TotalQuotientVolumeScalar.Negative6
