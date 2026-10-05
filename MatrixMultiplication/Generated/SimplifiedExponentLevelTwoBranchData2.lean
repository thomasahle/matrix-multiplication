import MatrixMultiplication.DyadicLogLinear
import MatrixMultiplication.SignedDyadicLogForm

/-! Exact level-two branch 2; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwo.Branch2

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bits : ℕ := 56
def constantNumerator : ℤ := 785343451672907776
def arguments : Array ℕ := #[
    63, 66, 67, 100, 203, 213,
    224, 3648, 3670, 3690, 3896, 3962,
    3964, 3970
  ]
def coefficients : Array ℕ := #[
    597053100542976, 844133260243680, 255615547853952, 121399574168000, 637560638400, 506018846568,
    274812104000, 2237755704000, 4359364241560, 5794578216000, 2364863704792640, 7557826870129536,
    25349577603075360, 18811911183774720
  ]
def scales : Array ℕ := #[
    5, 6, 6, 6, 7, 7,
    7, 11, 11, 11, 11, 11,
    11, 11
  ]

abbrev TermIndex := Fin 14
def argument (term : TermIndex) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : TermIndex) : ℕ := coefficients[term.val]?.getD 0
def scale (term : TermIndex) : ℕ := scales[term.val]?.getD 0

def expectedForm : Form := Form.ofNegativeFamily constantNumerator argument coefficient
noncomputable def exactLogSum : ℝ := Form.natLogSum bits argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 7 bits argument coefficient scale
noncomputable def ceiling : ℝ := 4563131841861 / 500000000000
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

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwo.Branch2
