import MatrixMultiplication.DyadicLogLinear
import MatrixMultiplication.SignedDyadicLogForm

/-! Exact level-two branch 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo.Branch1

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bits : ℕ := 56
def constantNumerator : ℤ := 764867368517771264
def arguments : Array ℕ := #[
    38, 40, 41, 45, 57, 58,
    61, 62, 64, 66, 67, 68,
    72, 75, 78, 81, 82, 87,
    170, 171, 177, 178, 3740, 3742,
    3754, 3756, 3922, 3932, 3934, 3940,
    3946, 3952, 3960, 3962, 3964, 3968,
    3972, 3974, 3980, 3982, 4006, 4014,
    4016, 4020
  ]
def coefficients : Array ℕ := #[
    91592961006864, 5091571557280, 1521036888044, 17656453866600, 160933241302416, 630965021502240,
    29523460161468, 317078950695936, 19291228552960, 6220156749576, 5602774395480, 28625812735664,
    28026061539840, 69670618593000, 26226820696128, 8032030727256, 4922229477992, 131382553726944,
    457697702760, 3325125096, 94961553150, 3455594456, 36303155240, 1003802632450,
    36498595352, 5056213445784, 2961392963891232, 118013453094296, 195049437537192, 662395343222720,
    1832801739786520, 769159688926720, 833516312009040, 165658150409640, 186793192085752, 598028085141760,
    10156754775518208, 961690415423556, 21648627461887200, 5621369884791408, 785908379884440, 74456610592788,
    255596892175456, 4844785569047280
  ]
def scales : Array ℕ := #[
    5, 5, 5, 5, 5, 5,
    5, 5, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
    7, 7, 7, 7, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11
  ]

abbrev TermIndex := Fin 44
def argument (term : TermIndex) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : TermIndex) : ℕ := coefficients[term.val]?.getD 0
def scale (term : TermIndex) : ℕ := scales[term.val]?.getD 0

def expectedForm : Form := Form.ofNegativeFamily constantNumerator argument coefficient
noncomputable def exactLogSum : ℝ := Form.natLogSum bits argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 8 bits argument coefficient scale
noncomputable def ceiling : ℝ := 8871592865051 / 1000000000000
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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo.Branch1
