import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative1

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    213, 215, 219, 221, 229, 233,
    241, 247, 251, 253, 269, 273,
    277, 281, 283, 285, 287, 291,
    293, 307, 317, 321, 325, 327,
    333, 341, 345, 347, 349, 361,
    363, 365, 367, 369, 377, 379,
    389, 393, 395, 399, 401, 403,
    409, 411, 413, 415, 419, 423,
    427, 435, 443, 449, 453, 457,
    465, 467, 475, 479, 481, 491,
    493, 495, 507, 511
  ]

def coefficients : Array ℕ := #[
    29179871994235, 14774687498240, 22574348107776, 47596827574272, 28604482191360, 8005819039744,
    13022340841472, 21096879357952, 25872882991104, 95623151878144, 21869973471232, 37486474559488,
    18829136625664, 28965259444224, 54872502173696, 18966575579136, 97585951932416, 4303557230592,
    140462610448384, 31233002176512, 21784074125312, 9135395438592, 77910706749440, 10342281248768,
    45664092291072, 10685878632448, 21921513078784, 47107201302528, 46346992091136, 36283883716608,
    58274116272128, 37623913512960, 12219181957120, 37417755082752, 25357486915584, 24739011624960,
    50440095924224, 162040526143488, 53669911330816, 68547678044160, 64744484503552, 27281632264192,
    51883204935680, 96226594783232, 37383395344384, 13984413515776, 28793460752384, 22539988369408,
    22196390985728, 6968584437760, 54135915282432, 39341900431360, 25529285607424, 15668040695808,
    40166534152192, 16045997817856, 16320875724800, 5235565133824, 16527034155008, 12421045420032,
    46694884442112, 4578066313963560, 20890720927744, 33672543600640
  ]

def scales : Array ℕ := #[
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8
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
noncomputable def ceiling : ℝ := 336840381817 / 200000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative1
