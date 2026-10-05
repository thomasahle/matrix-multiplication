import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 17, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17

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
    129, 991, 999, 1009, 1521, 1987,
    2017, 2313, 2335, 8005, 8289, 8317,
    12189, 40839, 97757
  ]
def positiveCoefficients : Array ℕ := #[
    89607051803632965818298207830016, 731355168169174100326004205551616, 731038255519117042975630029750272, 6259024838626882669889972076544, 1595259052224712437446007440015360, 260502198346901142007572508704768,
    6179796676112618332296428126208, 223581874615253960688981027848192, 224928753377996454428071275003904, 262562130572272014785004651413504, 1383878314636655184746432180518912, 1384987508911854885472741795823616,
    1353137787581120621760137127788544, 6471197857840082565965482775543808, 1346799534579979474752653611761664
  ]
def positiveScales : Array ℕ := #[
    7, 9, 9, 9, 10, 10,
    10, 11, 11, 12, 13, 13,
    13, 15, 16
  ]
def negativeArguments : Array ℕ := #[
    5, 7, 27, 31, 39, 51,
    53, 55, 71, 79, 411, 461,
    465, 469, 579, 801, 927, 1517,
    1519, 1657, 2307, 2319, 2869, 2883,
    16999, 17079, 1396342518295
  ]
def negativeCoefficients : Array ℕ := #[
    6338253001141147007483516026880, 1109194275199700726309615304704, 8556641551540548460102746636288, 2456073037942194465399862460416, 6179796676112618332296428126208, 64650180611639699476331863474176,
    4199092613256009892457829367808, 4357548938284538567644917268480, 45001596308102143753132963790848, 6259024838626882669889972076544, 260502198346901142007572508704768, 36524182919075859630623761104896,
    36841095569132916980997936906240, 148632032876759897325488450830336, 45873106095759051466661947244544, 63461758173925734412428704219136, 146889013301446081898430483922944, 120189122534139000129406172659712,
    120347578859167528804593260560384, 262562130572272014785004651413504, 731117483681631307313223573700608, 734920435482315995517713683316736, 454611196506848769111755187027968, 456829585057248170564374417637376,
    1346799534579979474752653611761664, 1353137787581120621760137127788544, 3235598928920041282982741387771904
  ]
def negativeScales : Array ℕ := #[
    2, 2, 4, 4, 5, 5,
    5, 5, 6, 6, 8, 8,
    8, 8, 9, 9, 9, 10,
    10, 10, 11, 11, 11, 11,
    14, 14, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 9952741246512609, 9964340866974576, 9978710458070551, 10570804437724342, 10956376156533436,
    10977995367589168, 11175549550636190, 11189206834597024, 12966685686553403, 13016982347533647, 13021847516680606,
    13573292149952078, 15317659919792980, 16576912391470097
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 2807354922807594, 4754887502413606, 4954196321574415, 5285402218862249, 5672425342008812,
    5727920454700926, 5781359713964302, 6149747119504683, 6303780748177104, 8682994583729950, 8848622942116486,
    8861086908132560, 8873444115207229, 9177419537989237, 9645658432427781, 9856425530582692, 10567005370249242,
    10568906154504419, 10694357887284806, 11171802288682983, 11179287104646004, 11486332252768835, 11493355121495124,
    14053162259002147, 14059935885112303, 40344790012025446
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 2640017947557 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1253324842627 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5, coefficient := (-6338253001141147007483516026880) }, { argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 27, coefficient := (-8556641551540548460102746636288) }, { argument := 31, coefficient := (-2456073037942194465399862460416) }, { argument := 39, coefficient := (-6179796676112618332296428126208) }, { argument := 51, coefficient := (-64650180611639699476331863474176) }, { argument := 53, coefficient := (-4199092613256009892457829367808) }, { argument := 55, coefficient := (-4357548938284538567644917268480) }, { argument := 71, coefficient := (-45001596308102143753132963790848) }, { argument := 79, coefficient := (-6259024838626882669889972076544) }, { argument := 129, coefficient := 89607051803632965818298207830016 }, { argument := 411, coefficient := (-260502198346901142007572508704768) }, { argument := 461, coefficient := (-36524182919075859630623761104896) }, { argument := 465, coefficient := (-36841095569132916980997936906240) }, { argument := 469, coefficient := (-148632032876759897325488450830336) }, { argument := 579, coefficient := (-45873106095759051466661947244544) }, { argument := 801, coefficient := (-63461758173925734412428704219136) }, { argument := 927, coefficient := (-146889013301446081898430483922944) }, { argument := 991, coefficient := 731355168169174100326004205551616 }, { argument := 999, coefficient := 731038255519117042975630029750272 }, { argument := 1009, coefficient := 6259024838626882669889972076544 }, { argument := 1517, coefficient := (-120189122534139000129406172659712) }, { argument := 1519, coefficient := (-120347578859167528804593260560384) }, { argument := 1521, coefficient := 1595259052224712437446007440015360 }, { argument := 1657, coefficient := (-262562130572272014785004651413504) }, { argument := 1987, coefficient := 260502198346901142007572508704768 }, { argument := 2017, coefficient := 6179796676112618332296428126208 }, { argument := 2307, coefficient := (-731117483681631307313223573700608) }, { argument := 2313, coefficient := 223581874615253960688981027848192 }, { argument := 2319, coefficient := (-734920435482315995517713683316736) }, { argument := 2335, coefficient := 224928753377996454428071275003904 }, { argument := 2869, coefficient := (-454611196506848769111755187027968) }, { argument := 2883, coefficient := (-456829585057248170564374417637376) }, { argument := 8005, coefficient := 262562130572272014785004651413504 }, { argument := 8289, coefficient := 1383878314636655184746432180518912 }, { argument := 8317, coefficient := 1384987508911854885472741795823616 }, { argument := 12189, coefficient := 1353137787581120621760137127788544 }, { argument := 16999, coefficient := (-1346799534579979474752653611761664) }, { argument := 17079, coefficient := (-1353137787581120621760137127788544) }, { argument := 40839, coefficient := 6471197857840082565965482775543808 }, { argument := 97757, coefficient := 1346799534579979474752653611761664 }, { argument := 1396342518295, coefficient := (-3235598928920041282982741387771904) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17
