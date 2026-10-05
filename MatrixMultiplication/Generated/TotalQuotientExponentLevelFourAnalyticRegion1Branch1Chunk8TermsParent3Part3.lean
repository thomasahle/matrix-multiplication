import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 8, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-272796178383634750562423038541824)
def positiveArguments : Array ℕ := #[
    9, 9, 9, 9, 9, 217,
    5257, 3983, 2219, 217, 2219, 4431,
    217, 5257, 217, 9, 27, 57,
    147, 123, 3441, 105, 123, 111,
    57, 57, 111, 3441, 111, 9,
    147, 940545, 36808191, 36808191, 940545, 12345,
    2404305, 196214583, 19234481, 12345, 675037, 125154083,
    125154091, 675029, 355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 356526731314189519170947776512, 356526731314189519170947776512, 356526731314189519170947776512, 356526731314189519170947776512, 8394780891403984989159686144,
    203370337078851378285771751424, 154084849264802176091350368256, 171686809198391176875072290816, 8394780891403984989159686144, 171686809198391176875072290816, 171416009814797499939938107392,
    8394780891403984989159686144, 203370337078851378285771751424, 8394780891403984989159686144, 5570730176784211237046059008, 4178047632588158427784544256, 4410161389954167229328130048,
    5686787055467215637817851904, 76133312416050886906296139776, 133117239849406047685246451712, 4061990753905154027012751360, 76133312416050886906296139776, 4294104511271162828556337152,
    4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 133117239849406047685246451712, 4294104511271162828556337152, 5570730176784211237046059008,
    5686787055467215637817851904, 17766392734522521830062817280, 695287069893856516511832735744, 695287069893856516511832735744, 17766392734522521830062817280, 932761827696412322609233920,
    181664149545534437368245780480, 1853194340418888157926613057536, 181664536779586032679153303552, 932761827696412322609233920, 6375544206993753392235413504, 1182046893506971310510923841536,
    1182046969064835036425247260672, 6375468649130027477911994368, 26855002599055646572599574528, 1213797261762630048879977955328, 26998335866543706044125675520
  ]
def positiveScales : Array ℕ := #[
    3, 3, 3, 3, 3, 7,
    12, 11, 11, 7, 11, 12,
    7, 12, 7, 3, 4, 5,
    7, 6, 11, 6, 6, 6,
    5, 5, 6, 11, 6, 3,
    7, 19, 25, 25, 19, 13,
    21, 27, 24, 13, 19, 26,
    26, 19, 18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    5, 9, 9, 7, 3, 9,
    7, 15, 1
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 1426106925256758076683791106048, 1426106925256758076683791106048, 1109194275199700726309615304704, 475368975085586025561263702016, 1426106925256758076683791106048,
    2218388550399401452619230609408, 2376844875427930127806318510080, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    2, 3, 3, 2, 1, 3,
    2, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 3169925001442312, 3169925001442312, 3169925001442312, 3169925001442312, 7761551232426566,
    12360024019571875, 11959639763607828, 11115693952197011, 7761551232426566, 11115693952197011, 12113416611485945,
    7761551232426566, 12360024019571875, 7761551232426566, 3169925001442312, 4754887502147955, 5832890014087662,
    7199672344836364, 6942514504772358, 11748612176723449, 6714245517659862, 6942514504772358, 6794415866314396,
    5832890014087662, 5832890014087662, 6794415866314396, 11748612176723449, 6794415866314396, 3169925001442312,
    7199672344836364, 19843137444910796, 25133523512019349, 25133523512019349, 19843137444910796, 13591639216029865,
    21197188491195494, 27547857028178609, 24197191566431043, 13591639216029865, 19364607055494452, 26899130116801141,
    26899130209019946, 19364589957722451, 18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 3169925001442313, 3169925001442313, 2807354922807594, 1584962500724866, 3169925001442313,
    2807354922807594, 3906890600547867, 0
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 81011019 / 31250000000
noncomputable def negativeCeiling : ℝ := 4186827 / 10000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }, { argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }, { argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }, { argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 203370337078851378285771751424, coefficient := 203370337078851378285771751424 }, { argument := 154084849264802176091350368256, coefficient := 154084849264802176091350368256 }, { argument := 171686809198391176875072290816, coefficient := 171686809198391176875072290816 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 171686809198391176875072290816, coefficient := 171686809198391176875072290816 }, { argument := 171416009814797499939938107392, coefficient := 171416009814797499939938107392 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 203370337078851378285771751424, coefficient := 203370337078851378285771751424 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 17766392734522521830062817280, coefficient := 17766392734522521830062817280 }, { argument := 695287069893856516511832735744, coefficient := 695287069893856516511832735744 }, { argument := 695287069893856516511832735744, coefficient := 695287069893856516511832735744 }, { argument := 17766392734522521830062817280, coefficient := 17766392734522521830062817280 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 932761827696412322609233920, coefficient := 932761827696412322609233920 }, { argument := 181664149545534437368245780480, coefficient := 181664149545534437368245780480 }, { argument := 1853194340418888157926613057536, coefficient := 1853194340418888157926613057536 }, { argument := 181664536779586032679153303552, coefficient := 181664536779586032679153303552 }, { argument := 932761827696412322609233920, coefficient := 932761827696412322609233920 }, { argument := 2218388550399401452619230609408, coefficient := (-2218388550399401452619230609408) }, { argument := 6375544206993753392235413504, coefficient := 6375544206993753392235413504 }, { argument := 1182046893506971310510923841536, coefficient := 1182046893506971310510923841536 }, { argument := 1182046969064835036425247260672, coefficient := 1182046969064835036425247260672 }, { argument := 6375468649130027477911994368, coefficient := 6375468649130027477911994368 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 26855002599055646572599574528, coefficient := 26855002599055646572599574528 }, { argument := 1213797261762630048879977955328, coefficient := 1213797261762630048879977955328 }, { argument := 26998335866543706044125675520, coefficient := 26998335866543706044125675520 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end TermShard6


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
