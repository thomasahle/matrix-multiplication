import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative7

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    5017, 5023, 5025, 5029, 5033, 5041,
    5051, 5053, 5057, 5065, 5067, 5073,
    5075, 5077, 5079, 5085, 5091, 5093,
    5099, 5103, 5105, 5107, 5109, 5111,
    5117, 5121, 5125, 5129, 5131, 5137,
    5139, 5141, 5143, 5153, 5155, 5157,
    5159, 5161, 5163, 5165, 5169, 5173,
    5175, 5179, 5181, 5183, 5185, 5191,
    5195, 5199, 5201, 5203, 5205, 5207,
    5209, 5211, 5213, 5217, 5221, 5225,
    5227, 5229, 5231, 5233
  ]

def coefficients : Array ℕ := #[
    2158082555904, 1460477952, 449401864192, 584115552256, 1362123915264, 216760320,
    347067717255168, 235623665926144, 347503701049344, 245191092994048, 1307271168, 636589789184,
    1374389534720, 348923143127040, 349026222342144, 232993385873408, 573876350222336, 1443349529624576,
    1064951808, 1135355109376, 2299658240, 313315270656, 679579189248, 244125941104640,
    68649025536, 580990302863360, 778514817024, 352427836440576, 412107264000, 352977592254464,
    120015788032, 841945313669120, 353389909114880, 3193768446754816, 123302811648, 177197954211840,
    354489420742656, 325105671536640, 953579481088, 3709381345280, 1256910520320, 16070332477440,
    2268601036800, 34359738368, 244634419077120, 785926164480, 47274098688, 892846080,
    755914244096, 1443109011456, 1403217355210752, 6967517184, 481707778048, 196159746342912,
    2346516480, 3271254466560, 635455045632, 255030853632, 22897832509440, 245215395840,
    962971713536, 3090983804571648, 1426967592960, 535397430411264
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
noncomputable def ceiling : ℝ := 1125223804629 / 200000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative7
