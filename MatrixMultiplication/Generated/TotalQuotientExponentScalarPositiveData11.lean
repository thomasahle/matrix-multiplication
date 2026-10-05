import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive11

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    2451, 2453, 2455, 2459, 2463, 2465,
    2467, 2471, 2473, 2475, 2479, 2483,
    2485, 2491, 2501, 2505, 2507, 2509,
    2515, 2521, 2523, 2525, 2529, 2533,
    2545, 2547, 2549, 2551, 2553, 2555,
    2557, 2559, 2561, 2563, 2565, 2569,
    2571, 2579, 2581, 2583, 2585, 2591,
    2597, 2599, 2601, 2605, 2607, 2609,
    2613, 2617, 2621, 2623, 2625, 2635,
    2637, 2641, 2645, 2649, 2651, 2653,
    2655, 2657, 2659, 2663
  ]

def coefficients : Array ℕ := #[
    40716289966080, 87132001533952, 5170984931819520, 68255620268032, 5892695130112, 4380866641920,
    137438953472, 295969417592832, 154618822656, 68719476736, 6287832121344, 6330781794304,
    256297878421504, 36249523978240, 68719476736, 214748364800, 505174053355520, 133861245714432,
    154618822656, 692898483929088, 499289948160, 16544214024192, 401579442176, 43774306680832,
    377957122048, 240518168576, 214748364800, 171798691840, 613972017414144, 614388629241856,
    34359738368, 44186623541248, 17179869184, 154618822656, 257698037760, 528280977408,
    463856467968, 85899345920, 1320702443520, 1305670057984, 266543522906112, 665719930880,
    979252543488, 240518168576, 773094113280, 358382808596480, 154618822656, 35424890257408,
    69814693396480, 8796093022208, 2740189134848, 5989331894272, 812038729236480, 9174050144256,
    206158430208, 154618822656, 80955838562304, 171798691840, 309237645312, 47966194761728,
    6992206757888, 68719476736, 549755813888, 34359738368
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
noncomputable def floor : ℝ := 202871486721 / 62500000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive11
