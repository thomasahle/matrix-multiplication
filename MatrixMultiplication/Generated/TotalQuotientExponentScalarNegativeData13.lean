import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative13

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    7031, 7039, 7041, 7043, 7059, 7093,
    7105, 7113, 7159, 7169, 7175, 7179,
    7185, 7201, 7205, 7215, 7233, 7285,
    7291, 7297, 7323, 7333, 7361, 7379,
    7401, 7411, 7417, 7421, 7425, 7435,
    7445, 7453, 7487, 7489, 7521, 7553,
    7589, 7593, 7597, 7601, 7605, 7613,
    7617, 7621, 7625, 7629, 7631, 7633,
    7637, 7641, 7645, 7649, 7653, 7657,
    7661, 7663, 7665, 7669, 7673, 7677,
    7681, 7685, 7693, 7697
  ]

def coefficients : Array ℕ := #[
    241548960727040, 483716396744704, 900508026880, 59751585021952, 26388279066624, 206158430208,
    363270144, 68719476736, 29618094473216, 54282633216, 68719476736, 26869315403776,
    386211840, 6631910580224, 495055110406144, 495811024650240, 47210496, 27247272525824,
    250516852441088, 126037057536, 251582004330496, 343597383680, 184647680, 137438953472,
    1031788583452672, 14705968021504, 1916345687998464, 6528350289920, 60209307815936, 2748779069440,
    2337974037512192, 2432635116716032, 58926951301120, 192651264, 121282560, 161431552,
    256413696, 1374855987200, 256684032, 402739200, 261306067243008, 1512169472,
    1646518272, 2013143040, 2185953280, 3475927040, 2377762614542336, 2039758848,
    2658549760, 4482785280, 2105585664, 344443191296, 2444722176, 752615424,
    1098137600, 8426588395798528, 847577088, 1012912128, 2380406784, 3230552064,
    3580231680, 3729629184, 1748606976, 874758144
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
noncomputable def ceiling : ℝ := 7621510287777 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative13
