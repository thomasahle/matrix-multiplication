import MatrixMultiplication.DyadicLogLinear
import MatrixMultiplication.SignedDyadicLogForm

/-! Exact level-two branch 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo.Branch0

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bits : ℕ := 56
def constantNumerator : ℤ := 801997362043973632
def arguments : Array ℕ := #[
    66, 67, 68, 69, 70, 75,
    76, 77, 78, 79, 80, 81,
    82, 171, 172, 173, 174, 193,
    194, 195, 215, 216, 217, 218,
    3660, 3662, 3664, 3666, 3706, 3708,
    3710, 3748, 3750, 3752, 3754, 3932,
    3934, 3936, 3938, 3940, 3942, 3944,
    3946, 3956, 3958, 3960, 3962, 3964
  ]
def coefficients : Array ℕ := #[
    564304595184, 2015887024010, 11554521076800, 23554151910360, 69631271223360, 1325690647321200,
    224432129054160, 114857155164752, 206239012872516, 1179337331034, 45637128223680, 83689333563168,
    17158673891496, 339584635944, 25162256336, 6510500696, 122847480, 534915500086,
    9475671592, 2094698580, 131376576460, 4884197184, 4070805424, 93668496,
    786299760, 34348593232, 41425227968, 1120061696052, 19905007532, 90556160472,
    5141286283210, 1323081480, 70561785000, 274444144688, 3727487495128, 411389669154648,
    2032307643441376, 1122673354302528, 29393863351974, 5208857119985340, 2940044841944496, 5823423138089520,
    34874501962196368, 1967580778282944, 675560385950760, 336440466648000, 59604062605430, 16946237994768
  ]
def scales : Array ℕ := #[
    6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    6, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11
  ]

abbrev TermIndex := Fin 48
def argument (term : TermIndex) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : TermIndex) : ℕ := coefficients[term.val]?.getD 0
def scale (term : TermIndex) : ℕ := scales[term.val]?.getD 0

def expectedForm : Form := Form.ofNegativeFamily constantNumerator argument coefficient
noncomputable def exactLogSum : ℝ := Form.natLogSum bits argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 8 bits argument coefficient scale
noncomputable def ceiling : ℝ := 9386594796917 / 1000000000000
noncomputable def branchFloor : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits - ceiling

theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

theorem fast_le_ceiling : fastUpper ≤ ceiling := by
  norm_num [ceiling, fastUpper, bits, fastLogSumLowerWithScale, fastLogSumUpperWithScale,
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

theorem exactLogSum_le_ceiling : exactLogSum ≤ ceiling := by
  apply le_trans (b := fastUpper)
  · change logSum bits argument coefficient ≤
      fastLogSumUpperWithScale 8 bits argument coefficient scale
    exact logSum_le_fastLogSumUpperWithScale 8 bits
      argument coefficient scale scales_valid
  · exact fast_le_ceiling

theorem branchFloor_le_expectedForm_eval :
    branchFloor ≤ Form.eval bits expectedForm := by
  rw [expectedForm, Form.eval_ofNegativeFamily]
  exact sub_le_sub_left exactLogSum_le_ceiling _

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo.Branch0
