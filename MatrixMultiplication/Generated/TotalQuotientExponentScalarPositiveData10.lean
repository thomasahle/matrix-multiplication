import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive10

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    2277, 2279, 2291, 2293, 2295, 2297,
    2299, 2301, 2303, 2305, 2307, 2309,
    2311, 2313, 2315, 2319, 2321, 2323,
    2325, 2327, 2329, 2333, 2335, 2337,
    2341, 2343, 2345, 2347, 2349, 2357,
    2359, 2361, 2363, 2365, 2367, 2369,
    2371, 2377, 2379, 2383, 2387, 2389,
    2395, 2397, 2399, 2401, 2403, 2407,
    2409, 2411, 2413, 2415, 2417, 2421,
    2425, 2427, 2429, 2431, 2435, 2437,
    2439, 2443, 2445, 2449
  ]

def coefficients : Array ℕ := #[
    104977590648832, 847479725621248, 137438953472, 400610927050752, 2894807957504, 253299991248896,
    27958089613312, 309237645312, 27934467293184, 68719476736, 49903225012224, 41274635714560,
    684851325829120, 97092030693376, 1028481458634752, 2473901162496, 223623914717184, 56985626083328,
    330712481792, 105527346462720, 5703716569088, 10617159155712, 97684736180224, 111274012704768,
    3340114461720576, 68719476736, 206158430208, 578686713593856, 197568495616, 170102179758080,
    3210488053760, 1057635696640, 412316860416, 63758789509120, 67581310402560, 6493990551552,
    463856467968, 14740327759872, 1309965025280, 103079215104, 1922295828316160, 6614249635840,
    103079215104, 3895535337472, 44620415238144, 41077067218944, 34359738368, 27032524161024,
    68719476736, 21299816562688, 8194797600768, 2714419331072, 7499012898816, 18038862643200,
    24657407246336, 8237747273728, 254390912942080, 2405181685760, 37211596652544, 57234734186496,
    38104949850112, 412316860416, 148176371712, 309237645312
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
noncomputable def floor : ℝ := 1701852813917 / 500000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive10
