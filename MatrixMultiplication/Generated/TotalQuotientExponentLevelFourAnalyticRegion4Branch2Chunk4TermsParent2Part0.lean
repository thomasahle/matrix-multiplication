import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 33993, 1187969, 14333263, 1187997, 16997,
    90845, 8207613, 8206223, 90845
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 321054807704375699498336256, 11220049976576339109738446848, 135373841562711239129191940096, 11220314429099379809870413824, 321064252437341438788763648,
    1716013532545171677752852480, 77518713071130354722638135296, 77505584892307977108944060416, 1716013532545171677752852480
  ]
def positiveScales : Array ℕ := #[
    0, 15, 20, 23, 20, 14,
    16, 22, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    3088094085, 279001388709, 278954138439, 3088094085, 107921043805, 9750389807997,
    9748738531087, 107921043805, 3088094085, 107921043805, 1302105277235, 107923587465,
    1544092465, 1302105277235, 117641875731219, 117621952495649, 1302105277235, 279001388709,
    9750389807997, 117641875731219, 9750619621161, 139504798161, 107923587465, 9750619621161,
    9748968305331, 107923587465, 278954138439, 9748738531087, 117621952495649, 9748968305331,
    139481172331, 1544092465, 139504798161, 139481172331, 1544092465, 3088094085,
    107921043805, 1302105277235, 107923587465, 1544092465, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1738442421311379100139520, 78531909389106456878383104, 78518609620458634670505984, 1738442421311379100139520, 60754146583204121972572160, 2744490744125773202463916032,
    2744025950995988108460163072, 60754146583204121972572160, 1738442421311379100139520, 60754146583204121972572160, 733020105169087798517432320, 60755578536482641627054080,
    1738493562499897659228160, 733020105169087798517432320, 33113244231642755315389169664, 33107636339374688652171935744, 733020105169087798517432320, 78531909389106456878383104,
    2744490744125773202463916032, 33113244231642755315389169664, 2744555430780757904631791616, 78534219626784481955807232, 60755578536482641627054080, 2744555430780757904631791616,
    2744090626695966717049307136, 60755578536482641627054080, 78518609620458634670505984, 2744025950995988108460163072, 33107636339374688652171935744, 2744090626695966717049307136,
    78520919466886442120118272, 1738493562499897659228160, 78534219626784481955807232, 78520919466886442120118272, 1738493562499897659228160, 1738442421311379100139520,
    60754146583204121972572160, 733020105169087798517432320, 60755578536482641627054080, 1738493562499897659228160, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    31, 38, 38, 31, 36, 43,
    43, 36, 31, 36, 40, 36,
    30, 40, 46, 46, 40, 38,
    43, 46, 43, 37, 36, 43,
    43, 36, 38, 43, 46, 43,
    37, 30, 37, 37, 30, 31,
    36, 40, 36, 30, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15052950069882485, 20180065758888953, 23772863743993937, 20180099762288957, 14052992510203163,
    16471119491986694, 22968531275983318, 22968286927729481, 16471119491986694
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31524069561869781, 38021481346742336, 38021236998484972, 31524069561869781, 36651185250897614, 43148597035748805,
    43148352687491441, 36651185250897614, 31524069561869781, 36651185250897614, 40243983236003434, 36651219254297636,
    30524112002190461, 40243983236003434, 46741395021062695, 46741150672804327, 40243983236003434, 38021481346742336,
    43148597035748805, 46741395021062695, 43148631039148809, 37021523787063015, 36651219254297636, 43148631039148809,
    43148386690891445, 36651219254297636, 38021236998484972, 43148352687491441, 46741150672804327, 43148386690891445,
    37021279438805651, 30524112002190461, 37021523787063015, 37021279438805651, 30524112002190461, 31524069561869781,
    36651185250897614, 40243983236003434, 36651219254297636, 30524112002190461, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 87841759 / 1000000000000
noncomputable def negativeCeiling : ℝ := 549011 / 6250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1738442421311379100139520, coefficient := (-1738442421311379100139520) }, { argument := 78531909389106456878383104, coefficient := (-78531909389106456878383104) }, { argument := 78518609620458634670505984, coefficient := (-78518609620458634670505984) }, { argument := 1738442421311379100139520, coefficient := (-1738442421311379100139520) }, { argument := 60754146583204121972572160, coefficient := (-60754146583204121972572160) }, { argument := 2744490744125773202463916032, coefficient := (-2744490744125773202463916032) }, { argument := 2744025950995988108460163072, coefficient := (-2744025950995988108460163072) }, { argument := 60754146583204121972572160, coefficient := (-60754146583204121972572160) }, { argument := 1738442421311379100139520, coefficient := (-1738442421311379100139520) }, { argument := 60754146583204121972572160, coefficient := (-60754146583204121972572160) }, { argument := 733020105169087798517432320, coefficient := (-733020105169087798517432320) }, { argument := 60755578536482641627054080, coefficient := (-60755578536482641627054080) }, { argument := 1738493562499897659228160, coefficient := (-1738493562499897659228160) }, { argument := 733020105169087798517432320, coefficient := (-733020105169087798517432320) }, { argument := 33113244231642755315389169664, coefficient := (-33113244231642755315389169664) }, { argument := 33107636339374688652171935744, coefficient := (-33107636339374688652171935744) }, { argument := 733020105169087798517432320, coefficient := (-733020105169087798517432320) }, { argument := 78531909389106456878383104, coefficient := (-78531909389106456878383104) }, { argument := 2744490744125773202463916032, coefficient := (-2744490744125773202463916032) }, { argument := 33113244231642755315389169664, coefficient := (-33113244231642755315389169664) }, { argument := 2744555430780757904631791616, coefficient := (-2744555430780757904631791616) }, { argument := 78534219626784481955807232, coefficient := (-78534219626784481955807232) }, { argument := 60755578536482641627054080, coefficient := (-60755578536482641627054080) }, { argument := 2744555430780757904631791616, coefficient := (-2744555430780757904631791616) }, { argument := 2744090626695966717049307136, coefficient := (-2744090626695966717049307136) }, { argument := 60755578536482641627054080, coefficient := (-60755578536482641627054080) }, { argument := 78518609620458634670505984, coefficient := (-78518609620458634670505984) }, { argument := 2744025950995988108460163072, coefficient := (-2744025950995988108460163072) }, { argument := 33107636339374688652171935744, coefficient := (-33107636339374688652171935744) }, { argument := 2744090626695966717049307136, coefficient := (-2744090626695966717049307136) }, { argument := 78520919466886442120118272, coefficient := (-78520919466886442120118272) }, { argument := 1738493562499897659228160, coefficient := (-1738493562499897659228160) }, { argument := 78534219626784481955807232, coefficient := (-78534219626784481955807232) }, { argument := 78520919466886442120118272, coefficient := (-78520919466886442120118272) }, { argument := 1738493562499897659228160, coefficient := (-1738493562499897659228160) }, { argument := 1738442421311379100139520, coefficient := (-1738442421311379100139520) }, { argument := 60754146583204121972572160, coefficient := (-60754146583204121972572160) }, { argument := 733020105169087798517432320, coefficient := (-733020105169087798517432320) }, { argument := 60755578536482641627054080, coefficient := (-60755578536482641627054080) }, { argument := 1738493562499897659228160, coefficient := (-1738493562499897659228160) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 321054807704375699498336256, coefficient := 321054807704375699498336256 }, { argument := 11220049976576339109738446848, coefficient := 11220049976576339109738446848 }, { argument := 135373841562711239129191940096, coefficient := 135373841562711239129191940096 }, { argument := 11220314429099379809870413824, coefficient := 11220314429099379809870413824 }, { argument := 321064252437341438788763648, coefficient := 321064252437341438788763648 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 77518713071130354722638135296, coefficient := 77518713071130354722638135296 }, { argument := 77505584892307977108944060416, coefficient := 77505584892307977108944060416 }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4
