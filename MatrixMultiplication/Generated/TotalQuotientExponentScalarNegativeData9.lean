import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative9

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    5539, 5543, 5545, 5549, 5557, 5561,
    5565, 5569, 5577, 5579, 5581, 5585,
    5587, 5593, 5595, 5603, 5609, 5615,
    5625, 5633, 5641, 5649, 5657, 5663,
    5669, 5673, 5679, 5681, 5689, 5697,
    5701, 5703, 5705, 5707, 5713, 5725,
    5729, 5733, 5739, 5747, 5753, 5757,
    5761, 5769, 5779, 5785, 5791, 5793,
    5799, 5801, 5805, 5807, 5809, 5813,
    5817, 5825, 5833, 5841, 5843, 5849,
    5857, 5863, 5865, 5873
  ]

def coefficients : Array ℕ := #[
    19344532701184, 137438953472, 613122048, 6425271074816, 6425271074816, 382080632258560,
    1236950581248, 382664406204416, 191589901139968, 191692980355072, 68719476736, 531775488,
    137438953472, 192139656953856, 192242736168960, 687194767360, 1683627180032, 34359738368,
    515396075520, 4150755254272, 346521600, 1684659544064, 388780439633920, 68719476736,
    389605073354752, 453033984, 6243164461465600, 601989120, 1424093184, 520372456554496,
    195885638893568, 1541455872, 196778221633536, 274877906944, 1786603332993024, 2321104896,
    3149722856456192, 962072674304, 197156178755584, 34359738368, 706805760, 197774654046208,
    677180252160, 396408301551616, 198564928028672, 279252820058112, 206158430208, 2495471616,
    446676598784, 783974400, 755914244096, 343597383680, 154725863424, 1535483904,
    2090409984, 230314706399232, 230631288864768, 1425569288601600, 274877906944, 1131798528,
    526985281536, 1462590983110656, 526381162496, 1749762048
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
noncomputable def ceiling : ℝ := 6606054624393 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative9
