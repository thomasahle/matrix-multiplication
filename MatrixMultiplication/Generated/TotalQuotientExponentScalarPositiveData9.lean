import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive9

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    2125, 2127, 2129, 2131, 2135, 2139,
    2141, 2145, 2147, 2149, 2151, 2153,
    2155, 2157, 2159, 2163, 2165, 2167,
    2169, 2173, 2175, 2177, 2179, 2181,
    2183, 2187, 2189, 2191, 2195, 2197,
    2199, 2201, 2205, 2207, 2209, 2211,
    2213, 2215, 2217, 2219, 2221, 2223,
    2225, 2227, 2229, 2231, 2233, 2235,
    2237, 2239, 2241, 2243, 2245, 2247,
    2253, 2255, 2257, 2263, 2265, 2267,
    2269, 2271, 2273, 2275
  ]

def coefficients : Array ℕ := #[
    108812996444160, 139927887020032, 407579511488512, 54374285967360, 6425271074816, 248764505784320,
    433660163522560, 298929723801600, 515396075520, 28535762714624, 13638131777536, 481036337152,
    83442624626688, 2011806704861184, 353969729699840, 1337560190156800, 259518030151680, 618475290624,
    137438953472, 180302727086080, 22157736280064, 274877906944, 108555298406400, 5247560440610816,
    34359738368, 154618822656, 35669703393280, 13368085708800, 37417755082752, 50038516482048,
    108544560988160, 153819958738944, 3614214979584, 6120328396800, 5336496865280, 1408749273088,
    1140297710960640, 2710124363776, 1086626725888, 5877662744576, 37881611550720, 566935683072,
    146378927898624, 3173172841021440, 50560355008512, 154618822656, 183188945108992, 214748364800,
    6261325193805824, 76931454205952, 137438953472, 90063316713472, 4207959848517632, 81670950617088,
    355784353382400, 72696616452096, 274877906944, 539735655186432, 652196152606720, 51539607552,
    1060856922112, 137438953472, 2336462209024, 34875134443520
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
noncomputable def floor : ℝ := 2226389792473 / 250000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive9
