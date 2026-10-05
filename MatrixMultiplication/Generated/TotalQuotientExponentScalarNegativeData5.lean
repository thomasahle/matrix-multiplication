import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative5

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    4121, 4127, 4129, 4145, 4147, 4149,
    4155, 4161, 4163, 4173, 4179, 4193,
    4197, 4199, 4203, 4205, 4213, 4221,
    4225, 4235, 4243, 4249, 4263, 4269,
    4273, 4277, 4279, 4283, 4289, 4291,
    4297, 4305, 4321, 4335, 4347, 4353,
    4361, 4365, 4369, 4371, 4379, 4383,
    4385, 4391, 4409, 4413, 4417, 4423,
    4425, 4427, 4435, 4449, 4453, 4455,
    4457, 4461, 4465, 4473, 4481, 4483,
    4513, 4517, 4519, 4533
  ]

def coefficients : Array ℕ := #[
    57896159150080, 567141841502208, 123592184979456, 142421115535360, 142489835012096, 157711199109120,
    142730353180672, 124897743216640, 206158430208, 343597383680, 58755152609280, 120729600,
    576934366937088, 576968726675456, 577724640919552, 343597383680, 1516810650255360, 68719476736,
    180043776, 145513491988480, 145754010157056, 584081192517632, 1862710136406016, 586829971587072,
    68719476736, 1271310319616, 146990960738304, 147162759430144, 109048436736, 294943994150912,
    283742208, 284270592, 296971453169664, 595763503562752, 15599321219072, 312819810304,
    599371276091392, 149945898237952, 150083337191424, 300338473074688, 300956948365312, 137438953472,
    21884928, 377957122048, 15152644620288, 303293410574336, 947920896, 68719476736,
    448487424, 304152404033536, 35971519335104512, 136073216, 306007829905408, 206158430208,
    153106994167808, 153244433121280, 452542464, 206158430208, 453691392000, 481036337152,
    115507200, 206158430208, 128711579926528, 129467494170624
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
noncomputable def ceiling : ℝ := 16309071267247 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative5
