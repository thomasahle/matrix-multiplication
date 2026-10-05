import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive12

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    2667, 2669, 2673, 2677, 2679, 2681,
    2685, 2687, 2689, 2691, 2693, 2695,
    2697, 2703, 2705, 2707, 2713, 2715,
    2721, 2729, 2739, 2743, 2745, 2747,
    2751, 2761, 2763, 2777, 2787, 2791,
    2795, 2797, 2811, 2815, 2817, 2827,
    2831, 2833, 2835, 2837, 2839, 2841,
    2845, 2847, 2851, 2853, 2855, 2857,
    2861, 2865, 2867, 2869, 2875, 2877,
    2879, 2881, 2883, 2885, 2887, 2891,
    2899, 2901, 2907, 2913
  ]

def coefficients : Array ℕ := #[
    352187318272, 171798691840, 46407121633280, 154618822656, 24275155156992, 206158430208,
    34359738368, 118472377892864, 618475290624, 1192401032970240, 515396075520, 515396075520,
    463856467968, 14431090114560, 68719476736, 77309411328, 223338299392, 481036337152,
    171798691840, 131597797949440, 206673826283520, 42949672960, 77309411328, 65189013618688,
    790273982464, 68719476736, 215744797212672, 309237645312, 68719476736, 6146098200576,
    412316860416, 309237645312, 26527865503744, 492220431990784, 618475290624, 261357349896192,
    103079215104, 19327352832, 107624364244992, 2987149754368, 54183159922688, 1357209665536,
    471226631847936, 2989297238016, 266653044572160, 128849018880, 85899345920, 457809154015232,
    68719476736, 33346126086144, 51582557224960, 21610127949824, 463504280649728, 257698037760,
    274517129691136, 68719476736, 318549134409728, 555579789541376, 137438953472, 309237645312,
    68719476736, 26186415603712, 697932185600, 41038412513280
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
noncomputable def floor : ℝ := 1895046897027 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive12
