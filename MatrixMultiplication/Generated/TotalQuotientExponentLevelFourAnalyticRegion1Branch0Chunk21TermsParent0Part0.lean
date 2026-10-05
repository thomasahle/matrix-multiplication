import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 21, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    129, 267, 289, 501, 783, 923,
    927, 993, 2323, 2347, 3751
  ]
def positiveCoefficients : Array ℕ := #[
    30423614405477505635920876929024, 475368975085586025561263702016, 236971434080164633742289955454976, 70671520962723789133441203699712, 141263813762933313929288863449088, 16954826778052568245018405371904,
    17350967590623889932986125123584, 69720783012552617082318676295680, 129062676735736605939883095097344, 130013414685907777991005622501376, 594369675182011060626766715420672
  ]
def positiveScales : Array ℕ := #[
    7, 8, 8, 8, 9, 9,
    9, 9, 11, 11, 11
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 7, 9, 15, 21,
    41, 51, 101, 107, 109, 135,
    219, 225, 231, 541, 813, 1629,
    1641, 9587531153
  ]
def negativeCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 6338253001141147007483516026880, 8873554201597605810476922437632, 1426106925256758076683791106048, 4753689750855860255612637020160, 3327582825599102178928845914112,
    6496709326169675682670603927552, 8081272576454962434541482934272, 64016355311525584775583511871488, 16954826778052568245018405371904, 8635869714054812797696290586624, 42783207757702742300513733181440,
    17350967590623889932986125123584, 17826336565709475958547388825600, 18301705540795061984108652527616, 42862435920217006638107277131776, 64412496124096906463551231623168, 129062676735736605939883095097344,
    130013414685907777991005622501376, 297184837591005530313383357710336
  ]
def negativeScales : Array ℕ := #[
    1, 2, 2, 3, 3, 4,
    5, 5, 6, 6, 6, 7,
    7, 7, 7, 9, 9, 10,
    10, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 8060695931687553, 8174925682500678, 8968666792316714, 9612868497290540, 9850186837538196,
    9856425528504426, 9955649906820795, 11181773438808807, 11196602126523170, 11873059547496154
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 2807354922807594, 3169925001442313, 3906890600547867, 4392317422778766,
    5357552004618085, 5672425342008812, 6658211482778016, 6741466986587556, 6768184325109843, 7076815597050831,
    7774787059984115, 7813781192070436, 7851749043206919, 9079484783826816, 9667111542107763, 10669770888560475,
    10680359523558999, 33158512214393811
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 20
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 5692826757 / 31250000000
noncomputable def negativeCeiling : ℝ := 181926552039 / 1000000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-2852213850513516153367582212096) }, { argument := 5, coefficient := (-6338253001141147007483516026880) }, { argument := 7, coefficient := (-8873554201597605810476922437632) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 15, coefficient := (-4753689750855860255612637020160) }, { argument := 21, coefficient := (-3327582825599102178928845914112) }, { argument := 41, coefficient := (-6496709326169675682670603927552) }, { argument := 51, coefficient := (-8081272576454962434541482934272) }, { argument := 101, coefficient := (-64016355311525584775583511871488) }, { argument := 107, coefficient := (-16954826778052568245018405371904) }, { argument := 109, coefficient := (-8635869714054812797696290586624) }, { argument := 129, coefficient := 30423614405477505635920876929024 }, { argument := 135, coefficient := (-42783207757702742300513733181440) }, { argument := 219, coefficient := (-17350967590623889932986125123584) }, { argument := 225, coefficient := (-17826336565709475958547388825600) }, { argument := 231, coefficient := (-18301705540795061984108652527616) }, { argument := 267, coefficient := 475368975085586025561263702016 }, { argument := 289, coefficient := 236971434080164633742289955454976 }, { argument := 501, coefficient := 70671520962723789133441203699712 }, { argument := 541, coefficient := (-42862435920217006638107277131776) }, { argument := 783, coefficient := 141263813762933313929288863449088 }, { argument := 813, coefficient := (-64412496124096906463551231623168) }, { argument := 923, coefficient := 16954826778052568245018405371904 }, { argument := 927, coefficient := 17350967590623889932986125123584 }, { argument := 993, coefficient := 69720783012552617082318676295680 }, { argument := 1629, coefficient := (-129062676735736605939883095097344) }, { argument := 1641, coefficient := (-130013414685907777991005622501376) }, { argument := 2323, coefficient := 129062676735736605939883095097344 }, { argument := 2347, coefficient := 130013414685907777991005622501376 }, { argument := 3751, coefficient := 594369675182011060626766715420672 }, { argument := 9587531153, coefficient := (-297184837591005530313383357710336) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard0


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk21
