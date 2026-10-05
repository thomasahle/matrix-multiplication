import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

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
def constantNumerator : ℤ := (-1814319815791790984094708576288768)
def positiveArguments : Array ℕ := #[
    217, 257, 1025, 509, 1025, 743307,
    5415379, 1486615, 1432907, 14321839, 28643671, 1432907,
    469967, 19254635, 396467845, 19254635, 469967, 2651229,
    525831075, 525831075, 2651229, 1066269, 48193419, 133995
  ]
def positiveCoefficients : Array ℕ := #[
    33579123565615939956638744576, 39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 28081344506259098998853861376,
    102293617126544545710799323136, 28081363395725030477434716160, 54133695918954357713771954176, 2164255118932970135605590622208, 2164254590027924054205326688256, 54133695918954357713771954176,
    17754851270838388417160544256, 2909678174844440677414831390720, 29956263404216922460617881681920, 2909678174844440677414831390720, 17754851270838388417160544256, 50080299872048026441048129536,
    9932668176925258510345489612800, 9932668176925258510345489612800, 50080299872048026441048129536, 10070625974645867464724840448, 455173973160986268329991733248, 10124375949953889766547128320
  ]
def positiveScales : Array ℕ := #[
    7, 8, 10, 8, 10, 19,
    22, 20, 20, 23, 24, 20,
    18, 24, 28, 24, 18, 21,
    28, 28, 21, 20, 25, 17
  ]
def negativeArguments : Array ℕ := #[
    7, 1, 1, 7, 113, 63,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    4436777100798802905238461218816, 158456325028528675187087900672, 158456325028528675187087900672, 4436777100798802905238461218816, 35811129456447480592281865551872, 19965496953594613073573075484672,
    475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    2, 0, 0, 2, 6, 5,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7761551232426566, 8005624549193878, 10001408194392808, 8991521844801183, 10001408194392808, 19503598668915806,
    22368630878955848, 20503599639372533, 20450513546689233, 23771713418372172, 24771713065803395, 20450513546689233,
    18842199931969229, 24198702439193696, 28562628621900205, 24198702439193696, 18842199931969229, 21338229857747294,
    28970024161517575, 28970024161517575, 21338229857747294, 20024140018686312, 25522332818461723, 17031819642210997
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 0, 0, 2807354922807594, 6820178963384638, 5977279939904027,
    1584962500724866
  ]

abbrev PositiveTerm := Fin 24
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 20452890477 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4685334171 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28081344506259098998853861376, coefficient := 28081344506259098998853861376 }, { argument := 102293617126544545710799323136, coefficient := 102293617126544545710799323136 }, { argument := 28081363395725030477434716160, coefficient := 28081363395725030477434716160 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 54133695918954357713771954176, coefficient := 54133695918954357713771954176 }, { argument := 2164255118932970135605590622208, coefficient := 2164255118932970135605590622208 }, { argument := 2164254590027924054205326688256, coefficient := 2164254590027924054205326688256 }, { argument := 54133695918954357713771954176, coefficient := 54133695918954357713771954176 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 17754851270838388417160544256, coefficient := 17754851270838388417160544256 }, { argument := 2909678174844440677414831390720, coefficient := 2909678174844440677414831390720 }, { argument := 29956263404216922460617881681920, coefficient := 29956263404216922460617881681920 }, { argument := 2909678174844440677414831390720, coefficient := 2909678174844440677414831390720 }, { argument := 17754851270838388417160544256, coefficient := 17754851270838388417160544256 }, { argument := 35811129456447480592281865551872, coefficient := (-35811129456447480592281865551872) }, { argument := 50080299872048026441048129536, coefficient := 50080299872048026441048129536 }, { argument := 9932668176925258510345489612800, coefficient := 9932668176925258510345489612800 }, { argument := 9932668176925258510345489612800, coefficient := 9932668176925258510345489612800 }, { argument := 50080299872048026441048129536, coefficient := 50080299872048026441048129536 }, { argument := 19965496953594613073573075484672, coefficient := (-19965496953594613073573075484672) }, { argument := 10070625974645867464724840448, coefficient := 10070625974645867464724840448 }, { argument := 455173973160986268329991733248, coefficient := 455173973160986268329991733248 }, { argument := 10124375949953889766547128320, coefficient := 10124375949953889766547128320 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
