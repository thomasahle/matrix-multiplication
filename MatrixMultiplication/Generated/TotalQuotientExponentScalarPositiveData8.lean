import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive8

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    1913, 1917, 1919, 1925, 1927, 1931,
    1935, 1937, 1941, 1943, 1945, 1947,
    1949, 1951, 1953, 1957, 1959, 1961,
    1967, 1983, 1987, 1995, 1997, 2001,
    2003, 2007, 2011, 2017, 2023, 2027,
    2029, 2039, 2041, 2045, 2047, 2049,
    2051, 2053, 2055, 2057, 2059, 2061,
    2063, 2067, 2069, 2071, 2073, 2075,
    2077, 2079, 2087, 2089, 2095, 2097,
    2099, 2101, 2103, 2105, 2107, 2109,
    2111, 2113, 2115, 2123
  ]

def coefficients : Array ℕ := #[
    4329327034368, 662572793593856, 755914244096, 150868242464768, 206158430208, 47356309405696,
    463807075844096, 95863670046720, 206158430208, 23983097380864, 274877906944, 412316860416,
    137438953472, 2353642078208, 395502063452160, 103079215104, 257698037760, 14530948104192,
    5050881540096, 991965646684160, 118025701294080, 73559904878592, 824633720832, 104384885161984,
    66451734003712, 1159873098153984, 17179869184, 81020263071744, 206158430208, 39307540692992,
    7078106103808, 34359738368, 4982162063360, 35128436850688000, 306059369512960, 671999173066752,
    350115533422592, 38929583570944, 227021233848320, 188932926996480, 49358301036544, 66352949755904,
    150157425377280, 36363340611584, 318540544475136, 521076169768960, 621576257011712, 137438953472,
    83515639070720, 450481939808256, 143469087555584, 186412318064640, 4896262717440, 21406117003264,
    42949672960, 1786706395136, 71629317079040, 128849018880, 14559939133440, 740881858560,
    32212254720, 363315578535936, 13722420510720, 438498981052416
  ]

def scales : Array ℕ := #[
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 11,
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
noncomputable def floor : ℝ := 3432071336709 / 250000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive8
