import MatrixMultiplication.DyadicLogLinear
import MatrixMultiplication.SignedDyadicLogForm

/-! Exact level-two branch 0; certificate `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

namespace MatrixMultiplication.Generated.SimplifiedExponentLevelTwo.Branch0

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bits : ℕ := 56
def constantNumerator : ℤ := 802969591043772416
def arguments : Array ℕ := #[
    66, 67, 69, 70, 78, 79,
    80, 82, 83, 85, 171, 172,
    173, 174, 193, 194, 195, 215,
    216, 217, 218, 3660, 3662, 3664,
    3666, 3706, 3708, 3710, 3748, 3750,
    3752, 3754, 3926, 3930, 3932, 3936,
    3938, 3940, 3956, 3958, 3962, 3964
  ]
def coefficients : Array ℕ := #[
    574634427180, 240468715522100, 582742067878056, 392803354927200, 2112475526304, 106117278390868,
    131751816468480, 39519861243356, 234200965267428, 348844622130000, 329089910400, 24868256736,
    6472235864, 121663584, 523245809126, 9455786592, 2073193980, 123276612280,
    4867040736, 4032333928, 93668496, 786299760, 34023978904, 41279715872,
    1051004792136, 19700658692, 90366125472, 5029124227610, 1310330784, 70147065000,
    271237497888, 3612291004800, 8056258744014000, 5544637310246940, 947512770785828, 3241094685124608,
    2644872419640748, 53353548548960, 11099500514942880, 16713718149719896, 7109977991780300, 17256445979860
  ]
def scales : Array ℕ := #[
    6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 7, 7,
    7, 7, 7, 7, 7, 7,
    7, 7, 7, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11
  ]

abbrev TermIndex := Fin 42
def argument (term : TermIndex) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : TermIndex) : ℕ := coefficients[term.val]?.getD 0
def scale (term : TermIndex) : ℕ := scales[term.val]?.getD 0

def expectedForm : Form := Form.ofNegativeFamily constantNumerator argument coefficient
noncomputable def exactLogSum : ℝ := Form.natLogSum bits argument coefficient
noncomputable def fastUpper : ℝ :=
  fastLogSumUpperWithScale 7 bits argument coefficient scale
noncomputable def ceiling : ℝ := 585684109507 / 62500000000
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

end MatrixMultiplication.Generated.SimplifiedExponentLevelTwo.Branch0
