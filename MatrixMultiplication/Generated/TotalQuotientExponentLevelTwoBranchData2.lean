import MatrixMultiplication.DyadicLogLinear
import MatrixMultiplication.SignedDyadicLogForm

/-! Exact level-two branch 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo.Branch2

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bits : ℕ := 56
def constantNumerator : ℤ := 785076174686654464
def arguments : Array ℕ := #[
    42, 49, 55, 57, 58, 59,
    62, 63, 67, 68, 71, 77,
    78, 82, 83, 93, 96, 100,
    203, 213, 224, 3648, 3670, 3690,
    3896, 3904, 3910, 3930, 3932, 3940,
    3942, 3954, 3960, 3962, 3970, 3972,
    3978, 3980, 3982, 3986, 3998, 4012
  ]
def coefficients : Array ℕ := #[
    93305614156608, 158890149741232, 75397252822320, 19315567253580, 22732022940000, 25290451096500,
    2717100276000, 1986481262808, 106491243057792, 333144737419184, 32532443510688, 62541538505292,
    215870978834160, 448846963500240, 253829424645300, 13736121018000, 7307300687232, 3274401386000,
    647203016194, 497944576758, 266133479808, 2167086907008, 4289804217610, 5882214605310,
    63785338999280, 148581780640384, 288753941830000, 6009335173831500, 10761379637091120, 5452126003888400,
    1600900940180916, 905868180572256, 9700390883676240, 3148644067126656, 62589925502760, 87034857228000,
    852588258151500, 779943545700000, 674689375471540, 2732122270452432, 6482069578218832, 4456453857098944
  ]
def scales : Array ℕ := #[
    5, 5, 5, 5, 5, 5,
    5, 5, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6,
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
  fastLogSumUpperWithScale 8 bits argument coefficient scale
noncomputable def ceiling : ℝ := 286008945377 / 31250000000
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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo.Branch2
