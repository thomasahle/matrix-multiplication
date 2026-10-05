import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-96407518295143170397608615075643392)
def positiveArguments : Array ℕ := #[
    22895, 352583, 398373, 210804885, 113931111, 1975823513,
    11165, 9889, 462869, 126005, 987912057, 462869,
    11165, 11165, 4785, 11165, 126005, 4785,
    56965255, 9889, 75, 1503, 2523, 2421,
    75, 2421, 1617, 39, 1503, 9
  ]
def positiveCoefficients : Array ℕ := #[
    442853706241230959278366392320, 13639894152229913545773684883456, 7705654488597418691443575226368, 995497923349190029263985704960, 538024459942501147372217696256, 9330562733856956727188466434048,
    431925016831914711539022561280, 382562157765410173077419982848, 17906377126374521326946335326208, 4874582332817323173083254620160, 9330565571999212931845239865344, 17906377126374521326946335326208,
    431925016831914711539022561280, 431925016831914711539022561280, 370221442998784038462019338240, 431925016831914711539022561280, 4874582332817323173083254620160, 370221442998784038462019338240,
    538021621800244942715444264960, 382562157765410173077419982848, 2901421967075110019294822400, 58144496220185204786668240896, 97603834972406701049077825536, 93657901097184551422836867072,
    2901421967075110019294822400, 93657901097184551422836867072, 62554657610139372015996370944, 3017478845758114420066615296, 58144496220185204786668240896, 2785365088392105618523029504
  ]
def positiveScales : Array ℕ := #[
    14, 18, 18, 27, 26, 30,
    13, 13, 18, 16, 29, 18,
    13, 13, 12, 13, 16, 12,
    25, 13, 6, 10, 11, 11,
    6, 11, 10, 5, 10, 3
  ]
def negativeArguments : Array ℕ := #[
    12795, 865, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1013724339370012199509394844549120, 68532360574838652018415517040640, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    13, 9, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14482744944560899, 18427603390368446, 18603760345521884, 27651333058158126, 26763586514525671, 30879806940250511,
    13446695630709832, 13271608924151744, 18820244417771497, 16943121456256572, 29879807379085042, 18820244417771497,
    13446695630709832, 13446695630709832, 12224303209373387, 13446695630709832, 16943121456256572, 12224303209373387,
    25763578904119711, 13271608924151744, 6228818690495880, 10553629293916271, 11300924490976300, 11241387363998936,
    6228818690495880, 11241387363998936, 10659103963471994, 5285402218862248, 10553629293916271, 3169925001442312
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13643292526944756, 9756556322783439, 1584962500724866
  ]

abbrev PositiveTerm := Fin 30
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 22998191797 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2727133913 / 15625000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 442853706241230959278366392320, coefficient := 442853706241230959278366392320 }, { argument := 13639894152229913545773684883456, coefficient := 13639894152229913545773684883456 }, { argument := 7705654488597418691443575226368, coefficient := 7705654488597418691443575226368 }, { argument := 995497923349190029263985704960, coefficient := 995497923349190029263985704960 }, { argument := 1013724339370012199509394844549120, coefficient := (-1013724339370012199509394844549120) }, { argument := 538024459942501147372217696256, coefficient := 538024459942501147372217696256 }, { argument := 9330562733856956727188466434048, coefficient := 9330562733856956727188466434048 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 382562157765410173077419982848, coefficient := 382562157765410173077419982848 }, { argument := 17906377126374521326946335326208, coefficient := 17906377126374521326946335326208 }, { argument := 4874582332817323173083254620160, coefficient := 4874582332817323173083254620160 }, { argument := 9330565571999212931845239865344, coefficient := 9330565571999212931845239865344 }, { argument := 17906377126374521326946335326208, coefficient := 17906377126374521326946335326208 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 370221442998784038462019338240, coefficient := 370221442998784038462019338240 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 4874582332817323173083254620160, coefficient := 4874582332817323173083254620160 }, { argument := 370221442998784038462019338240, coefficient := 370221442998784038462019338240 }, { argument := 538021621800244942715444264960, coefficient := 538021621800244942715444264960 }, { argument := 382562157765410173077419982848, coefficient := 382562157765410173077419982848 }, { argument := 68532360574838652018415517040640, coefficient := (-68532360574838652018415517040640) }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 97603834972406701049077825536, coefficient := 97603834972406701049077825536 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 3017478845758114420066615296, coefficient := 3017478845758114420066615296 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end TermShard8


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
