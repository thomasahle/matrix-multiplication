import MatrixMultiplication.DyadicLogLinear
import MatrixMultiplication.SignedDyadicLogForm

/-! Exact level-two branch 1; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwo.Branch1

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bits : ℕ := 56
def constantNumerator : ℤ := 795401876816994304
def arguments : Array ℕ := #[
    41, 66, 68, 79, 80, 81,
    82, 170, 171, 177, 178, 3740,
    3742, 3754, 3756, 3932, 3934, 3936,
    3938, 3960, 3964, 4014
  ]
def coefficients : Array ℕ := #[
    137407236618936, 374641544977920, 144819524168304, 872080030089192, 226708483003200, 207113841102060,
    13013392908476, 467717011120, 3283018056, 95031601254, 3399550088, 35714374520,
    1004543084442, 36036402872, 5166897334608, 312004029976388, 5029542289478420, 5577028681878720,
    21735766825893912, 4216803791959440, 11250599123427840, 6726251802297672
  ]
def scales : Array ℕ := #[
    5, 6, 6, 6, 6, 6,
    6, 7, 7, 7, 7, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11
  ]

abbrev TermIndex := Fin 22
def argument (term : TermIndex) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : TermIndex) : ℕ := coefficients[term.val]?.getD 0
def scale (term : TermIndex) : ℕ := scales[term.val]?.getD 0

def expectedForm : Form := Form.ofNegativeFamily constantNumerator argument coefficient
noncomputable def exactLogSum : ℝ := Form.natLogSum bits argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 7 bits argument coefficient scale
noncomputable def ceiling : ℝ := 4632851563419 / 500000000000
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
      fastLogSumUpperWithScale 7 bits argument coefficient scale
    exact logSum_le_fastLogSumUpperWithScale 7 bits
      argument coefficient scale scales_valid
  · exact fast_le_ceiling

theorem branchFloor_le_expectedForm_eval :
    branchFloor ≤ Form.eval bits expectedForm := by
  rw [expectedForm, Form.eval_ofNegativeFamily]
  exact sub_le_sub_left exactLogSum_le_ceiling _

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwo.Branch1
