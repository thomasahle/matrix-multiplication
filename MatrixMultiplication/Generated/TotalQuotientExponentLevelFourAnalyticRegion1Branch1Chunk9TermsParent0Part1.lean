import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 9, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 40488142784962828088831469682688
def positiveArguments : Array ℕ := #[
    5, 257, 1025, 509, 1025, 3,
    1, 1, 1, 1, 3, 9,
    19, 49, 41, 1147, 35, 41,
    37, 19, 19, 37, 1147, 37,
    3, 49, 2313, 1093527, 41509413, 4374111,
    2313, 47557, 8341051, 2085263, 11889
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 475368975085586025561263702016,
    39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 1856910058928070412348686336, 1392682544196052809261514752,
    1470053796651389076442710016, 1895595685155738545939283968, 25377770805350295635432046592, 44372413283135349228415483904, 1353996917968384675670917120, 25377770805350295635432046592,
    1431368170423720942852112384, 1470053796651389076442710016, 1470053796651389076442710016, 1431368170423720942852112384, 44372413283135349228415483904, 1431368170423720942852112384,
    1856910058928070412348686336, 1895595685155738545939283968, 349530677596079660136923136, 41312282023303956172778766336, 392045321349587056677561040896, 41312310357502853390650048512,
    349530677596079660136923136, 449163165651663434855481344, 78778999348612674158688468992, 78779008793345639897978896384, 449153720918697695565053952
  ]
def positiveScales : Array ℕ := #[
    2, 8, 10, 8, 10, 1,
    0, 0, 0, 0, 1, 3,
    4, 5, 5, 10, 5, 5,
    5, 4, 4, 5, 10, 5,
    1, 5, 11, 20, 25, 22,
    11, 15, 22, 20, 13
  ]
def negativeArguments : Array ℕ := #[
    37925, 1175675, 37925, 61089, 50225, 2313,
    1093527, 41509413, 4374111, 2313, 1, 3,
    1, 1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    179095748862831294729420800, 5551968214747770136612044800, 179095748862831294729420800, 288484646072023756459474944, 237180856602127930857881600, 174765338798039830068461568,
    20656141011651978086389383168, 196022660674793528338780520448, 20656155178751426695325024256, 174765338798039830068461568, 158456325028528675187087900672, 475368975085586025561263702016,
    158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    15, 20, 15, 15, 15, 11,
    20, 25, 22, 11, 0, 1,
    0, 0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 8005624549193878, 10001408194392808, 8991521844801183, 10001408194392808, 1584962500720924,
    0, 0, 0, 0, 1584962500720924, 3169925001442312,
    4247927513443585, 5614709844114682, 5357552004618083, 10163649676015824, 5129283016944966, 5357552004618083,
    5209453365628949, 4247927513443585, 4247927513443585, 5209453365628949, 10163649676015824, 5209453365628949,
    1584962500720924, 5614709844114682, 11175549550636190, 20060557411370183, 25306935194611816, 22060558400848184,
    11175549550636190, 15537370089131860, 22991797747512055, 20991797920475261, 13537339752689083
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15210861560021759, 20165057870408634, 15210861560021759, 15898625008140242, 15616118038516796, 11175549550636191,
    20060557411370184, 25306935194611818, 22060558400848185, 11175549550636191, 0, 1584962500724866,
    0, 0, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 35
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
noncomputable def positiveFloor : ℝ := 246274467 / 1000000000000
noncomputable def negativeCeiling : ℝ := 22471021 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 5551968214747770136612044800, coefficient := (-5551968214747770136612044800) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 288484646072023756459474944, coefficient := (-288484646072023756459474944) }, { argument := 237180856602127930857881600, coefficient := (-237180856602127930857881600) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 20656141011651978086389383168, coefficient := (-20656141011651978086389383168) }, { argument := 196022660674793528338780520448, coefficient := (-196022660674793528338780520448) }, { argument := 20656155178751426695325024256, coefficient := (-20656155178751426695325024256) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1895595685155738545939283968, coefficient := 1895595685155738545939283968 }, { argument := 25377770805350295635432046592, coefficient := 25377770805350295635432046592 }, { argument := 44372413283135349228415483904, coefficient := 44372413283135349228415483904 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 25377770805350295635432046592, coefficient := 25377770805350295635432046592 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 44372413283135349228415483904, coefficient := 44372413283135349228415483904 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1895595685155738545939283968, coefficient := 1895595685155738545939283968 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 349530677596079660136923136, coefficient := 349530677596079660136923136 }, { argument := 41312282023303956172778766336, coefficient := 41312282023303956172778766336 }, { argument := 392045321349587056677561040896, coefficient := 392045321349587056677561040896 }, { argument := 41312310357502853390650048512, coefficient := 41312310357502853390650048512 }, { argument := 349530677596079660136923136, coefficient := 349530677596079660136923136 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 449163165651663434855481344, coefficient := 449163165651663434855481344 }, { argument := 78778999348612674158688468992, coefficient := 78778999348612674158688468992 }, { argument := 78779008793345639897978896384, coefficient := 78779008793345639897978896384 }, { argument := 449153720918697695565053952, coefficient := 449153720918697695565053952 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard2


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9
