import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative12

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    6625, 6635, 6643, 6645, 6657, 6663,
    6665, 6669, 6679, 6683, 6685, 6689,
    6691, 6693, 6705, 6717, 6721, 6723,
    6725, 6739, 6743, 6753, 6757, 6761,
    6769, 6773, 6775, 6779, 6785, 6789,
    6793, 6795, 6809, 6825, 6831, 6841,
    6845, 6849, 6853, 6857, 6873, 6875,
    6877, 6881, 6885, 6899, 6901, 6905,
    6913, 6919, 6927, 6929, 6933, 6951,
    6957, 6961, 6969, 6977, 6979, 6985,
    6993, 7005, 7023, 7027
  ]

def coefficients : Array ℕ := #[
    227599405498368, 206158430208, 913110047129600, 206158430208, 963195723776, 915618308030464,
    4585684992, 1236950581248, 928778087825408, 688912754278400, 229729210728448, 631775232,
    459733299363840, 474995376128, 725962752, 947847742619648, 707051520, 116796309504,
    101834711040, 463066193985536, 463341071892480, 1175135797248, 2468189265027072, 464646741950464,
    1237168889856, 465402656194560, 2748779069440, 3539742720, 309350400, 605883195392,
    550335873024, 30972813312, 2275013168070656, 914106479542272, 4115368050688, 446676598784,
    991883739136, 273481728, 2891151563046912, 942659422126080, 1855569527865344, 257415352320,
    12716089344, 369868800, 59270548684800, 249202114560, 3131582299238400, 2415799959552,
    69381379325952, 239537278349312, 475951095873536, 159621120, 238181706366976, 343597383680,
    2329707225088, 10637107200, 2611340115968, 263860224, 26010321944576, 206158430208,
    161095680, 561489051648, 446676598784, 241411521773568
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
noncomputable def ceiling : ℝ := 8134832905757 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative12
