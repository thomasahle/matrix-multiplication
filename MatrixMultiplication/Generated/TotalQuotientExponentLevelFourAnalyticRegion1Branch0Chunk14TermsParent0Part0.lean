import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 14, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14

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
    155, 299, 359, 453, 907, 1071,
    1241, 1805, 2157, 2239, 7215
  ]
def positiveCoefficients : Array ℕ := #[
    14102612927539052091650823159808, 1584563250285286751870879006720, 85804100002948277613808098213888, 8794326039083341472883378487296, 8873554201597605810476922437632, 78673565376664487230389142683648,
    14181841090053316429244367110144, 74236788275865684325150681464832, 79307390676778601931137494286336, 354783711738875703743889809604608, 74078331950837155649963593564160
  ]
def positiveScales : Array ℕ := #[
    7, 8, 8, 8, 9, 10,
    10, 10, 11, 11, 12
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 9, 33, 35, 37,
    45, 73, 89, 135, 179, 253,
    503, 935, 937, 3073573731
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 792281625142643375935439503360, 7130534626283790383418955530240, 10458117451882892562347801444352, 2772985687999251815774038261760, 2931442013027780490961126162432,
    28522138505135161533675822120960, 5783655863541296644328708374528, 14102612927539052091650823159808, 10695801939425685575128433295360, 42545523270159949287733101330432, 40089450232217754822333238870016,
    39851765744674961809552607019008, 74078331950837155649963593564160, 74236788275865684325150681464832, 177391855869437851871944904802304
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 5, 5, 5,
    5, 6, 6, 7, 7, 7,
    8, 9, 9, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7276124405274237, 8224001674198104, 8487840033823039, 8823367239982289, 9824958740462537, 10064742764750255,
    10277287400130356, 10817783121717284, 11074810461160453, 11128638812852597, 12816783679322438
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 3169925001442313, 5044394119358454, 5129283016944967, 5209453365628950,
    5491853096329881, 6189824558880018, 6475733430966516, 7076815597050831, 7483815777264413, 7982993592700323,
    8974414605457178, 9868822557245328, 9871905240275299, 31517269947832782
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 20524131677 / 200000000000
noncomputable def negativeCeiling : ℝ := 20505897153 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 5, coefficient := (-792281625142643375935439503360) }, { argument := 9, coefficient := (-7130534626283790383418955530240) }, { argument := 33, coefficient := (-10458117451882892562347801444352) }, { argument := 35, coefficient := (-2772985687999251815774038261760) }, { argument := 37, coefficient := (-2931442013027780490961126162432) }, { argument := 45, coefficient := (-28522138505135161533675822120960) }, { argument := 73, coefficient := (-5783655863541296644328708374528) }, { argument := 89, coefficient := (-14102612927539052091650823159808) }, { argument := 135, coefficient := (-10695801939425685575128433295360) }, { argument := 155, coefficient := 14102612927539052091650823159808 }, { argument := 179, coefficient := (-42545523270159949287733101330432) }, { argument := 253, coefficient := (-40089450232217754822333238870016) }, { argument := 299, coefficient := 1584563250285286751870879006720 }, { argument := 359, coefficient := 85804100002948277613808098213888 }, { argument := 453, coefficient := 8794326039083341472883378487296 }, { argument := 503, coefficient := (-39851765744674961809552607019008) }, { argument := 907, coefficient := 8873554201597605810476922437632 }, { argument := 935, coefficient := (-74078331950837155649963593564160) }, { argument := 937, coefficient := (-74236788275865684325150681464832) }, { argument := 1071, coefficient := 78673565376664487230389142683648 }, { argument := 1241, coefficient := 14181841090053316429244367110144 }, { argument := 1805, coefficient := 74236788275865684325150681464832 }, { argument := 2157, coefficient := 79307390676778601931137494286336 }, { argument := 2239, coefficient := 354783711738875703743889809604608 }, { argument := 7215, coefficient := 74078331950837155649963593564160 }, { argument := 3073573731, coefficient := (-177391855869437851871944904802304) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk14
