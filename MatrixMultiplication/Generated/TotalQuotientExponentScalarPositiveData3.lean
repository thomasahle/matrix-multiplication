import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive3

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    753, 757, 759, 761, 771, 773,
    783, 785, 789, 791, 799, 807,
    817, 831, 833, 837, 839, 841,
    845, 847, 849, 853, 855, 861,
    865, 871, 873, 875, 877, 885,
    887, 897, 905, 911, 915, 919,
    921, 923, 929, 931, 933, 939,
    941, 943, 945, 951, 953, 955,
    957, 959, 965, 967, 969, 971,
    973, 975, 979, 987, 989, 991,
    995, 999, 1001, 1009
  ]

def coefficients : Array ℕ := #[
    206158430208, 26628797235200, 206158430208, 68719476736, 877891315302400, 2645699854336,
    61469571940352, 59648505806848, 277111289937920, 28643136897024, 223338299392, 652835028992,
    365707875319808, 348854423650304, 409533721608192, 206158430208, 6648609374208, 577995223859200,
    261993005056, 1397032602304512, 4681514352640, 820617926410240, 58884001628160, 292057776128,
    309237645312, 7284264534016, 1340029796352, 1571958030336, 274877906944, 68719476736,
    60936995995648, 246737281220608, 618475290624, 343597383680, 343597383680, 549755813888,
    7078106103808, 7499012898816, 2662879723520, 3745211482112, 862893289504768, 427022828437504,
    2783138807808, 22305912651776, 434822489047040, 1271310319616, 9665823899648, 481036337152,
    7069516169216, 7425998454784, 68719476736, 103113574842368, 216141007945728, 206158430208,
    68663642161152, 137438953472, 44324062494720, 188394445471744, 146819162046464, 317896299380736,
    575983551889584, 317037305921536, 5188320493568, 7627861917696
  ]

def scales : Array ℕ := #[
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9
  ]

abbrev Term := Fin 64
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 55 argument coefficient
noncomputable def fastLower : ℝ :=
  fastLogSumLowerWithScale 8 55 argument coefficient scale
noncomputable def floor : ℝ := 2561663048183 / 1000000000000

theorem floor_le_fast : floor ≤ fastLower := by
  norm_num [floor, fastLower, fastLogSumLowerWithScale, fastLogSumUpperWithScale,
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

theorem exact_bound : floor ≤ exact := by
  exact floor_le_fast.trans (fastLogSumLowerWithScale_le_logSum 8 55 argument coefficient scale scales_valid)

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive3
