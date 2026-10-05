import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive15

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    3541, 3543, 3547, 3551, 3553, 3561,
    3563, 3565, 3567, 3569, 3575, 3579,
    3589, 3593, 3597, 3601, 3607, 3615,
    3617, 3623, 3627, 3631, 3633, 3635,
    3639, 3655, 3665, 3669, 3673, 3693,
    3701, 3703, 3709, 3715, 3717, 3721,
    3731, 3733, 3739, 3743, 3745, 3747,
    3749, 3751, 3753, 3757, 3769, 3771,
    3773, 3779, 3781, 3783, 3793, 3797,
    3805, 3811, 3813, 3817, 3819, 3823,
    3827, 3831, 3833, 3835
  ]

def coefficients : Array ℕ := #[
    539435007475712, 8884139851776, 121891171860480, 94107028422656, 122453812576256, 283467841536,
    132254927945728, 2494210452226048, 1348619730944, 201657304481792, 605590388736, 137438953472,
    246599842267136, 171798691840, 123798137339904, 315587754459136, 100040525742080, 236223201280,
    1133871366144, 206158430208, 85899345920, 290442868424704, 1245540515840, 124897648967680,
    9788230467584, 69346541961216, 88725434400768, 406406985416704, 1221952555450368, 1537598291968,
    1065151889408, 127234111176704, 10101763080192, 154618822656, 2662879723520, 22967337615360,
    73581379715072, 257698037760, 4014371713843200, 211020333187072, 569890620571648, 106102872080384,
    17179869184, 128883378618368, 9389872250880, 68719476736, 68719476736, 5147518304256,
    137438953472, 147931558576128, 51539607552, 18154826760192, 2743745367769088, 16443282292736,
    18245021073408, 8658654068736, 326381007273984, 171798691840, 36215164239872, 318383778168832,
    47081431498752, 150323855360, 4813584596992, 477329780375552
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
noncomputable def floor : ℝ := 5317916940869 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive15
