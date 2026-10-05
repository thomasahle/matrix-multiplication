import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk9

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    31, 129, 245, 257, 277, 479,
    559, 561, 959, 1485, 1873, 2437,
    4903
  ]
def positiveCoefficients : Array ℕ := #[
    64967093261696756826706039275520, 32245862143305585400572387786752, 71305346262837903834189555302400, 8318957063997755447322114785280, 475368975085586025561263702016, 15687176177824338843521702166528,
    116227714408425783249728975142912, 116623855220997104937696694894592, 15766404340338603181115246116864, 136747808499620246686456858279936, 593577393556868417250831275917312, 130488783660993364016566886203392,
    131201837123621743054908781756416
  ]
def positiveScales : Array ℕ := #[
    4, 7, 7, 8, 8, 8,
    9, 9, 9, 10, 10, 11,
    12
  ]
def negativeArguments : Array ℕ := #[
    3, 25, 29, 51, 63, 69,
    71, 97, 105, 199, 225, 253,
    259, 269, 271, 395, 863, 913,
    9478194165
  ]
def negativeCoefficients : Array ℕ := #[
    2376844875427930127806318510080, 7922816251426433759354395033600, 2297616712913665790212774559744, 8081272576454962434541482934272, 4991374238398653268393268871168, 5466743213484239293954532573184,
    5625199538512767969141620473856, 7685131763883640746573763182592, 8318957063997755447322114785280, 63065617361354412724460984467456, 71305346262837903834189555302400, 20044725116108877411166619435008,
    20520094091194463436727883137024, 42624751432674213625326645280768, 42941664082731270975700821082112, 62590248386268826698899720765440, 136747808499620246686456858279936, 72335312375523340222905626656768,
    296788696778434208625415637958656
  ]
def negativeScales : Array ℕ := #[
    1, 4, 4, 5, 5, 6,
    6, 6, 6, 7, 7, 7,
    8, 8, 8, 8, 9, 9,
    33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4954196309696329, 7011227255423254, 7936637938489789, 8005624549193878, 8113742166049188, 8903881845446830,
    9126704472843189, 9131856960608792, 9905387004720923, 10536247215688073, 10871135184083522, 11250890535723340,
    12259449046285685
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 4643856189792934, 4857980997143165, 5672425342008812, 5977279939904027, 6108524456778170,
    6149747119504683, 6599912842192769, 6714245517766967, 7636624620558753, 7813781192070436, 7982993592700323,
    8016808287686554, 8071462362556625, 8082149041353872, 8625708843075807, 9753216749420175, 9834471051268172,
    33141965069505562
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 175454463 / 1000000000
noncomputable def negativeCeiling : ℝ := 88938948329 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-2376844875427930127806318510080) }, { argument := 25, coefficient := (-7922816251426433759354395033600) }, { argument := 29, coefficient := (-2297616712913665790212774559744) }, { argument := 31, coefficient := 64967093261696756826706039275520 }, { argument := 51, coefficient := (-8081272576454962434541482934272) }, { argument := 63, coefficient := (-4991374238398653268393268871168) }, { argument := 69, coefficient := (-5466743213484239293954532573184) }, { argument := 71, coefficient := (-5625199538512767969141620473856) }, { argument := 97, coefficient := (-7685131763883640746573763182592) }, { argument := 105, coefficient := (-8318957063997755447322114785280) }, { argument := 129, coefficient := 32245862143305585400572387786752 }, { argument := 199, coefficient := (-63065617361354412724460984467456) }, { argument := 225, coefficient := (-71305346262837903834189555302400) }, { argument := 245, coefficient := 71305346262837903834189555302400 }, { argument := 253, coefficient := (-20044725116108877411166619435008) }, { argument := 257, coefficient := 8318957063997755447322114785280 }, { argument := 259, coefficient := (-20520094091194463436727883137024) }, { argument := 269, coefficient := (-42624751432674213625326645280768) }, { argument := 271, coefficient := (-42941664082731270975700821082112) }, { argument := 277, coefficient := 475368975085586025561263702016 }, { argument := 395, coefficient := (-62590248386268826698899720765440) }, { argument := 479, coefficient := 15687176177824338843521702166528 }, { argument := 559, coefficient := 116227714408425783249728975142912 }, { argument := 561, coefficient := 116623855220997104937696694894592 }, { argument := 863, coefficient := (-136747808499620246686456858279936) }, { argument := 913, coefficient := (-72335312375523340222905626656768) }, { argument := 959, coefficient := 15766404340338603181115246116864 }, { argument := 1485, coefficient := 136747808499620246686456858279936 }, { argument := 1873, coefficient := 593577393556868417250831275917312 }, { argument := 2437, coefficient := 130488783660993364016566886203392 }, { argument := 4903, coefficient := 131201837123621743054908781756416 }, { argument := 9478194165, coefficient := (-296788696778434208625415637958656) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk9
