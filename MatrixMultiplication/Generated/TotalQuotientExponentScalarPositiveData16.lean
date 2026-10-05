import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive16

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    3837, 3845, 3851, 3855, 3861, 3869,
    3873, 3875, 3877, 3879, 3885, 3887,
    3889, 3891, 3901, 3903, 3907, 3915,
    3917, 3919, 3921, 3927, 3931, 3933,
    3935, 3947, 3961, 3965, 3969, 3979,
    3981, 3983, 3991, 3997, 4003, 4005,
    4013, 4023, 4051, 4053, 4065, 4069,
    4077, 4083, 4089, 4093, 4095
  ]

def coefficients : Array ℕ := #[
    867583393792, 137438953472, 281789583065088, 49718541418496, 6760278523904, 46812996042752,
    159223027597312, 270461606821888, 23089744183296, 17179869184, 71227737636864, 12472585027584,
    68719476736, 114095806218240, 171798691840, 17179869184, 2756007499399168, 40218073759744,
    463856467968, 38311108280320, 140465831673856, 257698037760, 35055523069952, 2164663517184,
    145857089372160, 10720238370816, 502476813893632, 1752346656768, 2723009265664, 27560805138432,
    20126216749056, 26916560044032, 125211181580288, 566935683072, 98852967284736, 20306605375488,
    1933121830256640, 51539607552, 463856467968, 39359080300544, 248309239250944, 68719476736,
    68719476736, 154618822656, 36814670538997760, 305784491606016, 1102294766583808
  ]

def scales : Array ℕ := #[
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11
  ]

abbrev Term := Fin 47
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 55 argument coefficient
noncomputable def fastLower : ℝ :=
  fastLogSumLowerWithScale 8 55 argument coefficient scale
noncomputable def floor : ℝ := 7566741692701 / 500000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive16
