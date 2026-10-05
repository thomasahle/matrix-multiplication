import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive13

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    2917, 2925, 2931, 2939, 2941, 2949,
    2951, 2957, 2959, 2963, 2967, 2969,
    2971, 2977, 2979, 2989, 2993, 2999,
    3003, 3005, 3013, 3025, 3031, 3041,
    3043, 3045, 3047, 3051, 3053, 3055,
    3059, 3063, 3079, 3083, 3087, 3091,
    3095, 3099, 3101, 3111, 3113, 3121,
    3123, 3139, 3141, 3145, 3153, 3155,
    3159, 3165, 3177, 3187, 3193, 3197,
    3199, 3207, 3209, 3213, 3215, 3225,
    3227, 3229, 3239, 3243
  ]

def coefficients : Array ℕ := #[
    206158430208, 34359738368, 25769803776, 2701534429184, 57702885621760, 19327352832,
    272507084996608, 214748364800, 463856467968, 40226663694336, 687194767360, 442321501945856,
    309237645312, 257530534035456, 28969554411520, 592705486848, 206158430208, 483183820800,
    412316860416, 68719476736, 343597383680, 1391569403904, 515396075520, 273327423750144,
    31434865639424, 55301998903296, 440122478690304, 157024004341760, 286835095896064, 529735897579520,
    962072674304, 157401961463808, 343597383680, 152969555214336, 319073120419840, 137438953472,
    2680059592704, 236223201280, 240518168576, 68719476736, 652835028992, 309237645312,
    266837728165888, 51539607552, 154618822656, 270819162849280, 1653562408960, 19376744955904,
    2147483648, 665719930880, 191614597201920, 171798691840, 264707424387072, 154618822656,
    687194767360, 59212566626304, 161061273600, 154618822656, 17317308137472, 17547088887808,
    704374636544, 2362232012800, 12292196401152, 549755813888
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
noncomputable def floor : ℝ := 93285206761 / 62500000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive13
