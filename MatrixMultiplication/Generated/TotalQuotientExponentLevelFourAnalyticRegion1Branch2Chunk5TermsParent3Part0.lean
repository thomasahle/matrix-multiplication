import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5

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
def constantNumerator : ℤ := (-2771206149192779081628870770688)
def positiveArguments : Array ℕ := #[
    15, 3, 20977513, 509, 20973719, 257,
    4665005, 63343257, 18660019
  ]
def positiveCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 950737950171172051122527404032, 198127008570324519551391236096, 39381967499766159995228389376, 198091175253452504683509710848, 39768823762042841331134365696,
    176238906035354474160943267840, 598260147545196068539931295744, 176238896590621508421652840448
  ]
def positiveScales : Array ℕ := #[
    3, 1, 24, 8, 24, 8,
    22, 25, 24
  ]
def negativeArguments : Array ℕ := #[
    4665005, 63343257, 18660019, 140838037809425, 509, 140806204233455,
    257, 4665005, 509, 509, 140806204233455, 509,
    140774385051921, 257, 63343257, 18660019, 257, 257,
    3, 3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    88119453017677237080471633920, 299130073772598034269965647872, 88119448295310754210826420224, 39642383412382391046294732800, 9845491874941539998807097344, 39633423057327618397810196480,
    9942205940510710332783591424, 88119453017677237080471633920, 9845491874941539998807097344, 9845491874941539998807097344, 39633423057327618397810196480, 9845491874941539998807097344,
    39624466753946383612353970176, 9942205940510710332783591424, 299130073772598034269965647872, 88119448295310754210826420224, 9942205940510710332783591424, 9942205940510710332783591424,
    950737950171172051122527404032, 475368975085586025561263702016, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    22, 25, 24, 47, 8, 47,
    8, 22, 8, 8, 47, 8,
    47, 8, 25, 24, 8, 8,
    1, 1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3906890595303263, 1584962500720924, 24322340312801365, 8991521844801183, 24322079362896483, 8005624549193878,
    22153447196697314, 25916687713989362, 24153447119382548
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    22153447196697316, 25916687720225281, 24153447119382550, 47001030360890605, 8991521866745102, 47000704232140036,
    8005624549193879, 22153447196697316, 8991521866745102, 8991521866745102, 47000704232140036, 8991521866745102,
    47000378177167879, 8005624549193879, 25916687720225281, 24153447119382550, 8005624549193879, 8005624549193879,
    1584962500724866, 1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 9
abbrev NegativeTerm := Fin 21
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
noncomputable def positiveFloor : ℝ := 96598141 / 200000000000
noncomputable def negativeCeiling : ℝ := 107000097 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 88119453017677237080471633920, coefficient := (-88119453017677237080471633920) }, { argument := 299130073772598034269965647872, coefficient := (-299130073772598034269965647872) }, { argument := 88119448295310754210826420224, coefficient := (-88119448295310754210826420224) }, { argument := 39642383412382391046294732800, coefficient := (-39642383412382391046294732800) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 39633423057327618397810196480, coefficient := (-39633423057327618397810196480) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 88119453017677237080471633920, coefficient := (-88119453017677237080471633920) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 39633423057327618397810196480, coefficient := (-39633423057327618397810196480) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 39624466753946383612353970176, coefficient := (-39624466753946383612353970176) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 299130073772598034269965647872, coefficient := (-299130073772598034269965647872) }, { argument := 88119448295310754210826420224, coefficient := (-88119448295310754210826420224) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 950737950171172051122527404032, coefficient := 950737950171172051122527404032 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 198127008570324519551391236096, coefficient := 198127008570324519551391236096 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 198091175253452504683509710848, coefficient := 198091175253452504683509710848 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 176238906035354474160943267840, coefficient := 176238906035354474160943267840 }, { argument := 598260147545196068539931295744, coefficient := 598260147545196068539931295744 }, { argument := 176238896590621508421652840448, coefficient := 176238896590621508421652840448 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5
