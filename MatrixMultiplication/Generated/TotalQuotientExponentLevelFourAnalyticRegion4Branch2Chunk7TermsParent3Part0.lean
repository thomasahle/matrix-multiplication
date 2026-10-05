import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 689686617142429123727811674112
def positiveArguments : Array ℕ := #[
    5, 1, 75497465, 75497479, 27202745, 96578277,
    13606961, 234225, 8154379, 2038597, 14639
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 158456325028528675187087900672, 713053396515248278166862561280, 713053528741509798516928544768, 256922662460099653977285591040, 912156036556200700680112963584,
    257028226240457722026392551424, 2212192578900285300355891200, 77015932156432189336026349568, 77016017159028880989640196096, 2212183134167319561065463808
  ]
def positiveScales : Array ℕ := #[
    2, 0, 26, 26, 24, 26,
    23, 17, 22, 20, 13
  ]
def negativeArguments : Array ℕ := #[
    234225, 8154379, 2038597, 14639, 228193145191137, 101269653472553,
    228286904785879, 228193145191137, 228193183466783, 234225, 228193183466783, 101269673294551,
    228286942815273, 101269653472553, 101269673294551, 8154379, 228286904785879, 228286942815273,
    2038597, 14639, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1106096289450142650177945600, 38507966078216094668013174784, 38508008579514440494820098048, 1106091567083659780532731904, 64230660228206630276664655872, 228038986821464473535348998144,
    64257051207953035271417626624, 64230660228206630276664655872, 64230671001843196711978139648, 1106096289450142650177945600, 64230671001843196711978139648, 228039031456635876804707483648,
    64257061912275825741778649088, 228038986821464473535348998144, 228039031456635876804707483648, 38507966078216094668013174784, 64257051207953035271417626624, 64257061912275825741778649088,
    38508008579514440494820098048, 1106091567083659780532731904, 158456325028528675187087900672, 1426106925256758076683791106048, 1426106925256758076683791106048, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    17, 22, 20, 13, 47, 46,
    47, 47, 47, 17, 47, 46,
    47, 46, 46, 22, 47, 47,
    20, 13, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 26169924867678021, 26169925135206589, 24697248903847307, 26525195389621746,
    23697841553253680, 17837535544432093, 22959143580675664, 20959145172979387, 13837529384978071
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    17837535545879205, 22959143593580194, 20959145185884260, 13837529386425010, 47697248782925188, 46525195248429577,
    47697841433160384, 47697248782925188, 47697249024913527, 17837535545879205, 47697249024913527, 46525195530815212,
    47697841673493108, 46525195248429577, 46525195530815212, 22959143593580194, 47697841433160384, 47697841673493108,
    20959145185884260, 13837529386425010, 0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 976016137 / 1000000000000
noncomputable def negativeCeiling : ℝ := 956299071 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1106096289450142650177945600, coefficient := (-1106096289450142650177945600) }, { argument := 38507966078216094668013174784, coefficient := (-38507966078216094668013174784) }, { argument := 38508008579514440494820098048, coefficient := (-38508008579514440494820098048) }, { argument := 1106091567083659780532731904, coefficient := (-1106091567083659780532731904) }, { argument := 64230660228206630276664655872, coefficient := (-64230660228206630276664655872) }, { argument := 228038986821464473535348998144, coefficient := (-228038986821464473535348998144) }, { argument := 64257051207953035271417626624, coefficient := (-64257051207953035271417626624) }, { argument := 64230660228206630276664655872, coefficient := (-64230660228206630276664655872) }, { argument := 64230671001843196711978139648, coefficient := (-64230671001843196711978139648) }, { argument := 1106096289450142650177945600, coefficient := (-1106096289450142650177945600) }, { argument := 64230671001843196711978139648, coefficient := (-64230671001843196711978139648) }, { argument := 228039031456635876804707483648, coefficient := (-228039031456635876804707483648) }, { argument := 64257061912275825741778649088, coefficient := (-64257061912275825741778649088) }, { argument := 228038986821464473535348998144, coefficient := (-228038986821464473535348998144) }, { argument := 228039031456635876804707483648, coefficient := (-228039031456635876804707483648) }, { argument := 38507966078216094668013174784, coefficient := (-38507966078216094668013174784) }, { argument := 64257051207953035271417626624, coefficient := (-64257051207953035271417626624) }, { argument := 64257061912275825741778649088, coefficient := (-64257061912275825741778649088) }, { argument := 38508008579514440494820098048, coefficient := (-38508008579514440494820098048) }, { argument := 1106091567083659780532731904, coefficient := (-1106091567083659780532731904) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 713053396515248278166862561280, coefficient := 713053396515248278166862561280 }, { argument := 713053528741509798516928544768, coefficient := 713053528741509798516928544768 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 256922662460099653977285591040, coefficient := 256922662460099653977285591040 }, { argument := 912156036556200700680112963584, coefficient := 912156036556200700680112963584 }, { argument := 257028226240457722026392551424, coefficient := 257028226240457722026392551424 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2212192578900285300355891200, coefficient := 2212192578900285300355891200 }, { argument := 77015932156432189336026349568, coefficient := 77015932156432189336026349568 }, { argument := 77016017159028880989640196096, coefficient := 77016017159028880989640196096 }, { argument := 2212183134167319561065463808, coefficient := 2212183134167319561065463808 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7
