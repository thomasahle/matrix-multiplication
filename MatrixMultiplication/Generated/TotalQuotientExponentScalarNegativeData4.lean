import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative4

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    1845, 1859, 1867, 1871, 1875, 1877,
    1879, 1891, 1923, 1933, 1955, 1965,
    1969, 1971, 1977, 1981, 1985, 1989,
    1991, 1993, 1999, 2019, 2043, 2083,
    2283, 2285, 2317, 2373, 2503, 2511,
    2539, 2567, 2573, 2619, 2733, 2937,
    2973, 2975, 3073, 3149, 3237, 3307,
    3323, 3361, 3401, 3405, 3413, 3447,
    3713, 3759, 3973, 3977, 4007, 4011,
    4035, 4037, 4047, 4097, 4099, 4101,
    4103, 4105, 4107, 4111
  ]

def coefficients : Array ℕ := #[
    2906747564287, 123695058124800, 64149631533056, 61418032332800, 128849018880000, 111060338081792,
    129123896786944, 34561601830912, 66073776881664, 66417374265344, 143208739810488, 2993200024235430,
    67654324846592, 799625836369626, 452865370809392, 1067034856298176, 31294962751380, 425783027967526,
    157132154962906, 1366061135226216, 3051798530047656, 69372311764992, 140393890971648, 21964462751744,
    78391743086592, 60988535603200, 79611513798656, 163011188752384, 86002425135104, 86277303042048,
    87239375716352, 88081189306368, 88362509664256, 89524298317824, 93905164959744, 96082713378816,
    102151502168064, 204440443289600, 105587476004864, 108198816120832, 111222473097216, 113627654782976,
    114177410596864, 115483080654848, 116857470189568, 116994909143040, 117269787049984, 118438018154496,
    93729071300608, 129158256525312, 136219182759936, 136648679489536, 137679471640576, 137816910594048,
    133728101728256, 138710263791616, 139053861175296, 4849977448857600, 2700532955136, 11738726400,
    3906416640, 141015108390912, 1311817728, 505036800
  ]

def scales : Array ℕ := #[
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 12, 12, 12,
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
noncomputable def ceiling : ℝ := 1596240616173 / 250000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative4
