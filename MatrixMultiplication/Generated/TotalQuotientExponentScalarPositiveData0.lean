import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive0

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    11, 21, 31, 45, 51, 53,
    65, 69, 71, 73, 89, 91,
    95, 97, 99, 105, 121, 125,
    127, 129, 133, 137, 139, 143,
    145, 151, 155, 165, 167, 169,
    173, 175, 183, 185, 187, 191,
    193, 207, 209, 217, 223, 225,
    227, 231, 235, 237, 239, 243,
    245, 249, 255, 257, 259, 261,
    263, 265, 267, 271, 275, 279,
    289, 295, 297, 299
  ]

def coefficients : Array ℕ := #[
    490468085334016, 67163826265696, 161704178221936, 12163347382272, 214026810294272, 334560772489216,
    323230648762368, 407467842338816, 97739390149680, 7748121001984, 16217796509696, 21496311316480,
    152866475999232, 155821413498880, 27212912787456, 330678122053632, 299548199092224, 116720031236096,
    150813481631744, 945402832486400, 861501720100864, 105688407736320, 349449276620800, 167435005067264,
    306875413299200, 15564961480704, 715885148897280, 36404142800896, 102233106546688, 14396730376192,
    114898965102592, 68719476736, 40888088657920, 116737211105280, 171798691840, 114761526149120,
    765423301689344, 8589934592, 346174364057600, 263676632236032, 316590629322752, 897620247576576,
    236635518140416, 712139937415168, 1580547964928, 390721764851712, 629023730302976, 462275920003072,
    20873541058560, 142558554488832, 68719476736, 1458676120420352, 1039878154354688, 477548823707648,
    36202279337984, 411973263032320, 10067403341824, 132044474548224, 1263585820934144, 3229815406592,
    75110388072448, 110863843328000, 81638738362368, 687194767360
  ]

def scales : Array ℕ := #[
    3, 4, 4, 5, 5, 5,
    6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 8, 8, 8,
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
noncomputable def fastLower : ℝ :=
  fastLogSumLowerWithScale 8 55 argument coefficient scale
noncomputable def floor : ℝ := 18034673409 / 5000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive0
