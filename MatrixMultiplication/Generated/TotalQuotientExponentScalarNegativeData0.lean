import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative0

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    3, 5, 7, 9, 13, 15,
    17, 19, 23, 25, 27, 29,
    33, 35, 37, 39, 41, 43,
    47, 49, 55, 57, 59, 61,
    63, 67, 75, 77, 79, 81,
    83, 85, 87, 93, 101, 103,
    107, 109, 111, 113, 115, 117,
    119, 123, 131, 135, 141, 147,
    149, 153, 157, 159, 161, 163,
    171, 179, 181, 189, 195, 197,
    199, 201, 203, 211
  ]

def coefficients : Array ℕ := #[
    71754651788992, 38774964748288, 77992233881792, 15599321219072, 55353538510848, 39616778338304,
    85410371717080, 57312043597824, 36112085024768, 107877511726856, 91396904058880, 272110944432,
    15771119910912, 2199023255552, 115311281963008, 180262738681720, 244403669611112, 19963007991808,
    21096879357952, 119714688237912, 134043332795032, 98805336517478, 81158543854042, 90852284213568,
    42121847457900, 88155115710784, 6597069766656, 40118401882406, 6277094703104, 13915694039040,
    138012907815514, 2714419331072, 41850161332224, 1374797337416, 44976897523712, 53017076301824,
    47663399567360, 48687749267456, 15118284881920, 25937307500544, 9483287789568, 30374008717312,
    36249523978240, 28312424415232, 31387620999168, 9753870729216, 65867618451456, 17626545782784,
    25254407700480, 31542239821824, 32366873542656, 20718922235904, 5531917877248, 42090679500800,
    140084653326336, 66795331387392, 11544872091648, 25357486915584, 26147760898048, 80917183856640,
    34187939676160, 3401614098432, 111065038268161, 22196390985728
  ]

def scales : Array ℕ := #[
    1, 2, 2, 3, 3, 3,
    4, 4, 4, 4, 4, 4,
    5, 5, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5,
    5, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 6, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 7
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
noncomputable def ceiling : ℝ := 538714223289 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Negative0
