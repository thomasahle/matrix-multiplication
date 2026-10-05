import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive14

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    3245, 3251, 3269, 3275, 3277, 3281,
    3283, 3285, 3287, 3291, 3295, 3297,
    3299, 3301, 3305, 3313, 3319, 3325,
    3329, 3333, 3337, 3343, 3345, 3347,
    3357, 3359, 3365, 3377, 3379, 3389,
    3391, 3397, 3399, 3411, 3419, 3423,
    3425, 3431, 3439, 3443, 3445, 3449,
    3453, 3455, 3457, 3459, 3463, 3465,
    3467, 3471, 3479, 3485, 3487, 3489,
    3497, 3501, 3505, 3507, 3509, 3513,
    3519, 3527, 3529, 3535
  ]

def coefficients : Array ℕ := #[
    2645699854336, 1357209665536, 16784732192768, 15865609191424, 146028888064, 8375186227200,
    10977936408576, 257698037760, 19226421100544, 10307921510400, 68719476736, 1443109011456,
    261993005056, 18339510353920, 6837587935232, 25769803776, 12541304504320, 457053239771136,
    12644383719424, 446676598784, 927712935936, 309237645312, 4327179550720, 805052964929536,
    154618822656, 751619276800, 346797134315520, 171798691840, 348253128228864, 465677534101504,
    116496692936704, 816043786240, 1502787582033920, 117231132344320, 283467841536, 10692321083392,
    117699283779584, 19600083255296, 14869176778752, 558905167970304, 1546188226560, 236961935654912,
    77446850281472, 962072674304, 119232587104256, 99127845191680, 700325019254784, 238147346628608,
    171798691840, 188978561024, 56035364569088, 239571128287232, 360734303191040, 11785390260224,
    253403070464, 455266533376, 373241247956992, 270582939648, 120594091737088, 110375290798080,
    33328946216960, 33432025432064, 447696653516800, 32117765439488
  ]

def scales : Array ℕ := #[
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11
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
noncomputable def floor : ℝ := 2711719079281 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive14
