import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 20, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20

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
    257, 265, 297, 363, 493, 989,
    1121, 1249, 2245, 2491, 6431, 6451
  ]
def positiveCoefficients : Array ℕ := #[
    46348475070844637492223210946560, 1346878762742493739090247155712, 376492228267784132244520851996672, 95707620317231319813001092005888, 9507379501711720511225274040320, 9824292151768777861599449841664,
    13627243952453466066089559457792, 83823395940091669173969499455488, 13864928439996259078870191308800, 83585711452548876161188867604480, 79861987814378452294292301938688, 80099672301921245307072933789696
  ]
def positiveScales : Array ℕ := #[
    8, 8, 8, 8, 8, 9,
    10, 10, 11, 11, 12, 12
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 7, 9, 15, 31,
    37, 39, 41, 127, 129, 141,
    181, 283, 365, 529, 1055, 50945086185
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 6338253001141147007483516026880, 554597137599850363154807652352, 713053462628379038341895553024, 9507379501711720511225274040320, 9824292151768777861599449841664,
    2931442013027780490961126162432, 3089898338056309166148214063104, 6496709326169675682670603927552, 10061976639311570874380081692672, 10220432964340099549567169593344, 44684683658045086402758787989504,
    28680594830163690208862910021632, 44843139983073615077945875890176, 28918279317706483221643541872640, 83823395940091669173969499455488, 83585711452548876161188867604480, 188246114133892066122260425998336
  ]
def negativeScales : Array ℕ := #[
    1, 2, 2, 3, 3, 4,
    5, 5, 5, 6, 7, 7,
    7, 8, 8, 9, 10, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8005624549193878, 8049848549450561, 8214319120800765, 8503825737995731, 8945443835782120, 9949826710117496,
    10130570562805426, 10286557761607957, 11132499729628509, 11282509306240836, 12650827374137414, 12655307101508963
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 2807354922807594, 3169925001442313, 3906890600547867, 4954196321574415,
    5209453365628950, 5285402218862249, 5357552004618085, 6988684706517367, 7011227255423255, 7139551352398794,
    7499845887083475, 8144658242831883, 8511752653767780, 9047123912114026, 10043027283594548, 35568223949469039
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 25858367921 / 250000000000
noncomputable def negativeCeiling : ℝ := 58695064303 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 5, coefficient := (-6338253001141147007483516026880) }, { argument := 7, coefficient := (-554597137599850363154807652352) }, { argument := 9, coefficient := (-713053462628379038341895553024) }, { argument := 15, coefficient := (-9507379501711720511225274040320) }, { argument := 31, coefficient := (-9824292151768777861599449841664) }, { argument := 37, coefficient := (-2931442013027780490961126162432) }, { argument := 39, coefficient := (-3089898338056309166148214063104) }, { argument := 41, coefficient := (-6496709326169675682670603927552) }, { argument := 127, coefficient := (-10061976639311570874380081692672) }, { argument := 129, coefficient := (-10220432964340099549567169593344) }, { argument := 141, coefficient := (-44684683658045086402758787989504) }, { argument := 181, coefficient := (-28680594830163690208862910021632) }, { argument := 257, coefficient := 46348475070844637492223210946560 }, { argument := 265, coefficient := 1346878762742493739090247155712 }, { argument := 283, coefficient := (-44843139983073615077945875890176) }, { argument := 297, coefficient := 376492228267784132244520851996672 }, { argument := 363, coefficient := 95707620317231319813001092005888 }, { argument := 365, coefficient := (-28918279317706483221643541872640) }, { argument := 493, coefficient := 9507379501711720511225274040320 }, { argument := 529, coefficient := (-83823395940091669173969499455488) }, { argument := 989, coefficient := 9824292151768777861599449841664 }, { argument := 1055, coefficient := (-83585711452548876161188867604480) }, { argument := 1121, coefficient := 13627243952453466066089559457792 }, { argument := 1249, coefficient := 83823395940091669173969499455488 }, { argument := 2245, coefficient := 13864928439996259078870191308800 }, { argument := 2491, coefficient := 83585711452548876161188867604480 }, { argument := 6431, coefficient := 79861987814378452294292301938688 }, { argument := 6451, coefficient := 80099672301921245307072933789696 }, { argument := 50945086185, coefficient := (-188246114133892066122260425998336) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk20
