import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative2

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    521, 527, 533, 539, 541, 573,
    579, 581, 583, 591, 593, 599,
    601, 607, 609, 635, 647, 651,
    653, 655, 659, 661, 663, 683,
    691, 695, 699, 713, 717, 729,
    735, 739, 747, 751, 763, 767,
    769, 775, 779, 781, 787, 793,
    801, 803, 813, 821, 825, 827,
    835, 843, 857, 863, 867, 881,
    889, 891, 893, 901, 907, 913,
    925, 927, 935, 937
  ]

def coefficients : Array ℕ := #[
    28827820490752, 33305323896832, 18227841204224, 27986006900736, 85899345920000, 39376260169728,
    57312043597824, 38912403701760, 40029095198720, 2357937045504, 18717467475968, 20164871454720,
    20650202759168, 19576460935168, 20237885898752, 21749714386944, 22024592293888, 22275847880704,
    12090332938240, 107142254166016, 22574348107776, 22711787061248, 22677427322880, 46797963657216,
    59030030516224, 119400090828800, 47966194761728, 32070520799232, 32100585570304, 50096498540544,
    1374389534720, 25391846653952, 50989851738112, 25804163514368, 6081673691136, 26285199851520,
    105553116266496, 26040386715648, 26766236188672, 53360673685504, 26972394618880, 54494545051648,
    26079041421312, 27590869909504, 26577257627648, 107047764885504, 54198192308224, 27281632264192,
    53738630807552, 26800595927040, 29446295781376, 43808666419200, 21715354648576, 174135154049024,
    61091614818304, 60610578481152, 61366492725248, 61572651155456, 22539988369408, 31370441129984,
    63565515980800, 46042049413120, 26353919328256, 128075924766720
  ]

def scales : Array ℕ := #[
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9
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
noncomputable def ceiling : ℝ := 721699041739 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative2
