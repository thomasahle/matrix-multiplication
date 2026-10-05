import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 14, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

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
def constantNumerator : ℤ := (-32892858445171359957107533747847168)
def positiveArguments : Array ℕ := #[
    7035, 45225, 7035, 91455, 91455, 3015,
    15, 285, 435, 4485, 135, 435,
    135, 135, 11565, 135, 4485, 11565,
    15, 135, 135, 285, 1, 1,
    307117959, 278454337, 307117941, 64935003, 2418092965, 2418003823,
    65024145, 14721019, 1147654849, 11602476229, 1147654849, 14719863,
    32989587, 2772999789, 1386499635, 16495053, 12920931, 62576541,
    12920931
  ]
def positiveCoefficients : Array ℕ := #[
    272153380511645319809854341120, 6998229784585165366539111628800, 272153380511645319809854341120, 7075987893302778315056212869120, 7075987893302778315056212869120, 233274326152838845551303720960,
    74276402357122816493947453440, 88203227799083344586562600960, 67312989636142552447639879680, 694020134524366316615321518080, 83560952651763168555690885120, 67312989636142552447639879680,
    83560952651763168555690885120, 83560952651763168555690885120, 3579194138583855719802092912640, 83560952651763168555690885120, 694020134524366316615321518080, 3579194138583855719802092912640,
    74276402357122816493947453440, 83560952651763168555690885120, 83560952651763168555690885120, 88203227799083344586562600960, 79228162514264337593543950336, 79228162514264337593543950336,
    1450323555868933901084434366464, 5259853712233955661619771998208, 1450323470866337209430820519936, 2453175053857918884482283208704, 91352969363031056826273753989120, 91349601673486929098964639678464,
    2456542743402046611791397519360, 278072186877148886856311504896, 43357174342563390115262844895232, 438329158896971154380571721859072, 43357174342563390115262844895232, 278050350654532097616843374592,
    623155679730048681745431134208, 52380485042312793168335471640576, 52380475238679974730952008007680, 623165483362867119128894767104, 122034742963742735601292541952, 1182037439329272605481206022144,
    122034742963742735601292541952
  ]
def positiveScales : Array ℕ := #[
    12, 15, 12, 16, 16, 11,
    3, 8, 8, 12, 7, 8,
    7, 7, 13, 7, 12, 13,
    3, 7, 7, 8, 0, 0,
    28, 28, 28, 25, 31, 31,
    25, 23, 30, 33, 30, 23,
    24, 31, 30, 23, 23, 25,
    23
  ]
def negativeArguments : Array ℕ := #[
    1005, 15, 1, 103, 37, 3317,
    669, 9
  ]
def negativeCoefficients : Array ℕ := #[
    159248606653671318563023340175360, 9507379501711720511225274040320, 158456325028528675187087900672, 8160500738969226772135026884608, 187612288833777951421512074395648, 525599630119629615595570566529024,
    106007281444085683700161805549568, 1426106925256758076683791106048
  ]
def negativeScales : Array ℕ := #[
    9, 3, 0, 6, 5, 11,
    9, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12780334708097221, 15464832882395960, 12780334708097221, 16480774426264977, 16480774426264977, 11557942286787341,
    3906890595303263, 8154818109052103, 8764871590716857, 12130892269806623, 7076815597050830, 8764871590716857,
    7076815597050830, 7076815597050830, 13497477645523536, 7076815597050830, 12130892269806623, 13497477645523536,
    3906890595303263, 7076815597050830, 7076815597050830, 8154818109052103, 0, 0,
    28194217636774743, 28052865522265930, 28194217552219247, 25952493031464462, 31171222564895166, 31171169379557077,
    25954472187868759, 23811374203447705, 30096041678485851, 33433713690610216, 30096041678485851, 23811260908236886,
    24975507379998264, 31368800360587718, 30368800090570100, 23975530076639614, 23623206689404673, 25899118577876724,
    23623206689404673
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9972979801353332, 3906890600547867, 0, 6686500527235738, 5209453365628950, 11695663296853368,
    9385862400641465, 3169925001442313
  ]

abbrev PositiveTerm := Fin 43
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 326226514341 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2950276953 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 272153380511645319809854341120, coefficient := 272153380511645319809854341120 }, { argument := 6998229784585165366539111628800, coefficient := 6998229784585165366539111628800 }, { argument := 272153380511645319809854341120, coefficient := 272153380511645319809854341120 }, { argument := 7075987893302778315056212869120, coefficient := 7075987893302778315056212869120 }, { argument := 7075987893302778315056212869120, coefficient := 7075987893302778315056212869120 }, { argument := 233274326152838845551303720960, coefficient := 233274326152838845551303720960 }, { argument := 159248606653671318563023340175360, coefficient := (-159248606653671318563023340175360) }, { argument := 74276402357122816493947453440, coefficient := 74276402357122816493947453440 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 67312989636142552447639879680, coefficient := 67312989636142552447639879680 }, { argument := 694020134524366316615321518080, coefficient := 694020134524366316615321518080 }, { argument := 83560952651763168555690885120, coefficient := 83560952651763168555690885120 }, { argument := 67312989636142552447639879680, coefficient := 67312989636142552447639879680 }, { argument := 83560952651763168555690885120, coefficient := 83560952651763168555690885120 }, { argument := 83560952651763168555690885120, coefficient := 83560952651763168555690885120 }, { argument := 3579194138583855719802092912640, coefficient := 3579194138583855719802092912640 }, { argument := 83560952651763168555690885120, coefficient := 83560952651763168555690885120 }, { argument := 694020134524366316615321518080, coefficient := 694020134524366316615321518080 }, { argument := 3579194138583855719802092912640, coefficient := 3579194138583855719802092912640 }, { argument := 74276402357122816493947453440, coefficient := 74276402357122816493947453440 }, { argument := 83560952651763168555690885120, coefficient := 83560952651763168555690885120 }, { argument := 83560952651763168555690885120, coefficient := 83560952651763168555690885120 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 9507379501711720511225274040320, coefficient := (-9507379501711720511225274040320) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1450323555868933901084434366464, coefficient := 1450323555868933901084434366464 }, { argument := 5259853712233955661619771998208, coefficient := 5259853712233955661619771998208 }, { argument := 1450323470866337209430820519936, coefficient := 1450323470866337209430820519936 }, { argument := 8160500738969226772135026884608, coefficient := (-8160500738969226772135026884608) }, { argument := 2453175053857918884482283208704, coefficient := 2453175053857918884482283208704 }, { argument := 91352969363031056826273753989120, coefficient := 91352969363031056826273753989120 }, { argument := 91349601673486929098964639678464, coefficient := 91349601673486929098964639678464 }, { argument := 2456542743402046611791397519360, coefficient := 2456542743402046611791397519360 }, { argument := 187612288833777951421512074395648, coefficient := (-187612288833777951421512074395648) }, { argument := 278072186877148886856311504896, coefficient := 278072186877148886856311504896 }, { argument := 43357174342563390115262844895232, coefficient := 43357174342563390115262844895232 }, { argument := 438329158896971154380571721859072, coefficient := 438329158896971154380571721859072 }, { argument := 43357174342563390115262844895232, coefficient := 43357174342563390115262844895232 }, { argument := 278050350654532097616843374592, coefficient := 278050350654532097616843374592 }, { argument := 525599630119629615595570566529024, coefficient := (-525599630119629615595570566529024) }, { argument := 623155679730048681745431134208, coefficient := 623155679730048681745431134208 }, { argument := 52380485042312793168335471640576, coefficient := 52380485042312793168335471640576 }, { argument := 52380475238679974730952008007680, coefficient := 52380475238679974730952008007680 }, { argument := 623165483362867119128894767104, coefficient := 623165483362867119128894767104 }, { argument := 106007281444085683700161805549568, coefficient := (-106007281444085683700161805549568) }, { argument := 122034742963742735601292541952, coefficient := 122034742963742735601292541952 }, { argument := 1182037439329272605481206022144, coefficient := 1182037439329272605481206022144 }, { argument := 122034742963742735601292541952, coefficient := 122034742963742735601292541952 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
