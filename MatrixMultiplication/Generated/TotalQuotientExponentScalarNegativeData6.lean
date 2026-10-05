import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative6

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    4535, 4541, 4545, 4561, 4569, 4571,
    4577, 4579, 4581, 4591, 4609, 4613,
    4615, 4619, 4637, 4639, 4641, 4649,
    4657, 4671, 4673, 4677, 4689, 4705,
    4707, 4727, 4737, 4753, 4769, 4773,
    4775, 4781, 4785, 4799, 4801, 4819,
    4825, 4833, 4841, 4849, 4865, 4879,
    4881, 4909, 4917, 4923, 4927, 4929,
    4937, 4939, 4943, 4945, 4959, 4961,
    4965, 4977, 4983, 4985, 4989, 4991,
    4993, 5001, 5007, 5009
  ]

def coefficients : Array ℕ := #[
    1305670057984, 127234111176704, 482410844758016, 45695139840, 337034673651712, 285907382960128,
    46032363520, 10376640987136, 157264522510336, 34359738368, 19403661312, 68719476736,
    317071665659904, 317415263043584, 318583494148096, 637510585679872, 32071680, 639125493383168,
    412316860416, 412316860416, 82526208, 919981994803200, 476294693257216, 19869696,
    638300859662336, 206158430208, 227782656, 653212986114048, 53217898496, 68719476736,
    328857055920128, 328513458536448, 229447069696, 164892384428032, 12023193600, 341501439639552,
    493680720871424, 1432938528899072, 312238080, 104251392, 167732493238272, 167641163497472,
    2256199680, 168637595910144, 580920096587776, 584115552256, 406853662015488, 479709231030272,
    1868482572451840, 481757891657728, 824633720832, 44652625920, 5453508954292224, 381057777664,
    170561741258752, 261334106112, 2397115785216, 171283295764480, 481036337152, 482376366948352,
    10299654144, 962072674304, 922705920, 555070373888
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
noncomputable def ceiling : ℝ := 1659977594 / 244140625

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative6
