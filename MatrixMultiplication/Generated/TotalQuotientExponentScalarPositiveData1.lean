import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive1

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    301, 303, 305, 309, 311, 313,
    315, 319, 323, 329, 335, 337,
    339, 343, 351, 353, 355, 357,
    359, 371, 375, 381, 383, 385,
    387, 391, 397, 405, 417, 421,
    425, 431, 433, 437, 439, 441,
    447, 451, 455, 461, 463, 469,
    471, 473, 477, 483, 485, 487,
    489, 497, 499, 501, 503, 513,
    515, 517, 519, 523, 529, 531,
    535, 537, 543, 545
  ]

def coefficients : Array ℕ := #[
    133530533232640, 125254131253248, 7043746365440, 746178626977792, 1958505086976, 197568495616,
    692829764452352, 789928237596672, 3917010173952, 48241072668672, 28913719836672, 652835028992,
    154618822656, 5763846111232, 343597383680, 7730941132800, 405081988005888, 40613210750976,
    135617887338496, 541165879296, 42569568354304, 150246545948672, 205711753609216, 687194767360,
    162315404050432, 26869315403776, 27917287424000, 181213260152832, 893353197568, 13159779794944,
    353767866236928, 829358184857600, 2954937499648, 2907692859392, 265331268386816, 45457933860864,
    2624225017856, 54234699530240, 68719476736, 364625543561216, 268899312467968, 326211356065792,
    100467874988032, 687194767360, 137438953472, 3264175144960, 51539607552, 137913157515016,
    12713103196160, 157436321202176, 97616016703488, 5875515260928, 17420387352576, 475892576944128,
    150134339928064, 880476885614592, 17918603558912, 5703716569088, 328204220891136, 2047745917452288,
    139672336465920, 28535762714624, 572759658725376, 432954178273280
  ]

def scales : Array ℕ := #[
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 9,
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
noncomputable def fastLower : ℝ :=
  fastLogSumLowerWithScale 8 55 argument coefficient scale
noncomputable def floor : ℝ := 737417011489 / 250000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive1
