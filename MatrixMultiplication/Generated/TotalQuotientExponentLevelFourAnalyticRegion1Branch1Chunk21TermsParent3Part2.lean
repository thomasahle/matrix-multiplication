import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 21, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1023068564072396246637673954934784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3056407965, 116018809335, 12225640245, 6464835, 22039152135, 429822798405,
    859645281495, 2754907155, 280577825, 32794100625, 8978487375, 35909947185,
    700340643555, 1400680773345, 4488764805, 27193602799, 3178404232575, 870194996385,
    123, 123, 1739582515, 203323423875, 55666621725, 3441,
    3441, 928496259, 265438797, 9224433249, 2777396193, 123008223,
    18448859883, 123008223, 239542329, 4525407783, 239542329, 2777396193,
    4525407783, 29015577, 239542329, 239542329, 265438797, 4193414565,
    765469425, 634246095, 8802992535, 4264758225, 16773652815, 17080903455,
    17080903455, 12225640245, 634246095, 140963603, 139712621, 140963603,
    139712621, 886625927, 103629357975, 28372020105, 123, 123,
    111, 111, 335385, 158561415
  ]
def negativeCoefficients : Array ℕ := #[
    28190387757601210327860510720, 267521160442406206888130641920, 28190407092094842584684298240, 238510313447520178242846720, 25409412439743403866728693760, 991103894902836133095863746560,
    991103531369391907987909509120, 25409533617558145569380106240, 41405978644264525393140121600, 151236095339213363179683840000, 41405964693914319650291712000, 82802700677765218195073925120,
    3229751154019032433724982558720, 3229749969357598805051509309440, 82803095564909761086231674880, 1003266862550529450275785146368, 3664450590069139789843739443200, 1003266524533543965126568181760,
    19033328104012721726574034944, 19033328104012721726574034944, 64179266898610014359367188480, 234415947775780712928509952000, 64179245275567195457952153600, 33279309962351511921311612928,
    33279309962351511921311612928, 4281933215792434732005851136, 2448240777746171354180222976, 85080379684660047347756040192, 25616958381783110023007698944, 2269101208642792962410938368,
    85080349178357035450585055232, 2269101208642792962410938368, 2209388018941666831821176832, 83479039202174330564486627328, 2209388018941666831821176832, 25616958381783110023007698944,
    83479039202174330564486627328, 4281943384560105364396179456, 2209388018941666831821176832, 2209388018941666831821176832, 2448240777746171354180222976, 38677422637760533663076843520,
    28240837158449216185014681600, 1462471924276834409581117440, 162386550375920672633845186560, 39335451756411408257699020800, 38677410082445348494513274880, 39385881822765781858029404160,
    39385881822765781858029404160, 28190407092094842584684298240, 1462471924276834409581117440, 10401278032995983885223329792, 10308971853816714596024582144, 10401278032995983885223329792,
    10308971853816714596024582144, 65421446257937950121161392128, 238953030635957113823900467200, 65421424216384625047460904960, 19033328104012721726574034944, 19033328104012721726574034944,
    1073526127817790707139084288, 1073526127817790707139084288, 12373522522322155937464320, 1462470921235125401624248320
  ]
def negativeScales : Array ℕ := #[
    31, 36, 33, 22, 34, 38,
    39, 31, 28, 34, 33, 35,
    39, 40, 32, 34, 41, 39,
    6, 6, 30, 37, 35, 11,
    11, 29, 27, 33, 31, 26,
    34, 26, 27, 32, 27, 31,
    32, 24, 27, 27, 27, 31,
    29, 29, 33, 31, 33, 33,
    33, 33, 29, 27, 27, 27,
    27, 29, 36, 34, 6, 6,
    6, 6, 18, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31509189979101104, 36755567762596226, 33509190968579105, 22624182118377635, 34359349672140249, 38644951051146439,
    39644950521970843, 31359356552355049, 28063825751568094, 34932717266462956, 33063825265500499, 35063664480016139,
    39349265859003603, 40349265329828008, 32063671360230939, 34662548251273941, 41531439758377937, 39662547765206346,
    6942514514520450, 6942514514520450, 30696093967133621, 37564985474202159, 35696093481066025, 11748612176955137,
    11748612176955137, 29790320857045012, 27983804030300356, 33102813128414053, 31371085844937157, 26874179523609959,
    34102812611123226, 26874179523609959, 27835705374381723, 32075400652813046, 27835705374381723, 31371085844937157,
    32075400652813046, 24790324283164172, 27835705374381723, 27835705374381723, 27983804030300356, 31965478330947449,
    29511769512680913, 29240467490863119, 33035346898360709, 31989816829594442, 33965477862625189, 33991665254594692,
    33991665254594692, 33509190968579105, 29240467490863119, 27070747463922485, 27057887112213212, 27070747463922485,
    27057887112213212, 29723750310095794, 36592641817107550, 34723749824028198, 6942514514520450, 6942514514520450,
    6794415866926375, 6794415866926375, 18355458640651126, 27240466501385119
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 7753281947 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 28190387757601210327860510720, coefficient := (-28190387757601210327860510720) }, { argument := 267521160442406206888130641920, coefficient := (-267521160442406206888130641920) }, { argument := 28190407092094842584684298240, coefficient := (-28190407092094842584684298240) }, { argument := 238510313447520178242846720, coefficient := (-238510313447520178242846720) }, { argument := 25409412439743403866728693760, coefficient := (-25409412439743403866728693760) }, { argument := 991103894902836133095863746560, coefficient := (-991103894902836133095863746560) }, { argument := 991103531369391907987909509120, coefficient := (-991103531369391907987909509120) }, { argument := 25409533617558145569380106240, coefficient := (-25409533617558145569380106240) }, { argument := 41405978644264525393140121600, coefficient := (-41405978644264525393140121600) }, { argument := 151236095339213363179683840000, coefficient := (-151236095339213363179683840000) }, { argument := 41405964693914319650291712000, coefficient := (-41405964693914319650291712000) }, { argument := 82802700677765218195073925120, coefficient := (-82802700677765218195073925120) }, { argument := 3229751154019032433724982558720, coefficient := (-3229751154019032433724982558720) }, { argument := 3229749969357598805051509309440, coefficient := (-3229749969357598805051509309440) }, { argument := 82803095564909761086231674880, coefficient := (-82803095564909761086231674880) }, { argument := 1003266862550529450275785146368, coefficient := (-1003266862550529450275785146368) }, { argument := 3664450590069139789843739443200, coefficient := (-3664450590069139789843739443200) }, { argument := 1003266524533543965126568181760, coefficient := (-1003266524533543965126568181760) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 64179266898610014359367188480, coefficient := (-64179266898610014359367188480) }, { argument := 234415947775780712928509952000, coefficient := (-234415947775780712928509952000) }, { argument := 64179245275567195457952153600, coefficient := (-64179245275567195457952153600) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 4281933215792434732005851136, coefficient := (-4281933215792434732005851136) }, { argument := 2448240777746171354180222976, coefficient := (-2448240777746171354180222976) }, { argument := 85080379684660047347756040192, coefficient := (-85080379684660047347756040192) }, { argument := 25616958381783110023007698944, coefficient := (-25616958381783110023007698944) }, { argument := 2269101208642792962410938368, coefficient := (-2269101208642792962410938368) }, { argument := 85080349178357035450585055232, coefficient := (-85080349178357035450585055232) }, { argument := 2269101208642792962410938368, coefficient := (-2269101208642792962410938368) }, { argument := 2209388018941666831821176832, coefficient := (-2209388018941666831821176832) }, { argument := 83479039202174330564486627328, coefficient := (-83479039202174330564486627328) }, { argument := 2209388018941666831821176832, coefficient := (-2209388018941666831821176832) }, { argument := 25616958381783110023007698944, coefficient := (-25616958381783110023007698944) }, { argument := 83479039202174330564486627328, coefficient := (-83479039202174330564486627328) }, { argument := 4281943384560105364396179456, coefficient := (-4281943384560105364396179456) }, { argument := 2209388018941666831821176832, coefficient := (-2209388018941666831821176832) }, { argument := 2209388018941666831821176832, coefficient := (-2209388018941666831821176832) }, { argument := 2448240777746171354180222976, coefficient := (-2448240777746171354180222976) }, { argument := 38677422637760533663076843520, coefficient := (-38677422637760533663076843520) }, { argument := 28240837158449216185014681600, coefficient := (-28240837158449216185014681600) }, { argument := 1462471924276834409581117440, coefficient := (-1462471924276834409581117440) }, { argument := 162386550375920672633845186560, coefficient := (-162386550375920672633845186560) }, { argument := 39335451756411408257699020800, coefficient := (-39335451756411408257699020800) }, { argument := 38677410082445348494513274880, coefficient := (-38677410082445348494513274880) }, { argument := 39385881822765781858029404160, coefficient := (-39385881822765781858029404160) }, { argument := 39385881822765781858029404160, coefficient := (-39385881822765781858029404160) }, { argument := 28190407092094842584684298240, coefficient := (-28190407092094842584684298240) }, { argument := 1462471924276834409581117440, coefficient := (-1462471924276834409581117440) }, { argument := 10401278032995983885223329792, coefficient := (-10401278032995983885223329792) }, { argument := 10308971853816714596024582144, coefficient := (-10308971853816714596024582144) }, { argument := 10401278032995983885223329792, coefficient := (-10401278032995983885223329792) }, { argument := 10308971853816714596024582144, coefficient := (-10308971853816714596024582144) }, { argument := 65421446257937950121161392128, coefficient := (-65421446257937950121161392128) }, { argument := 238953030635957113823900467200, coefficient := (-238953030635957113823900467200) }, { argument := 65421424216384625047460904960, coefficient := (-65421424216384625047460904960) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 1462470921235125401624248320, coefficient := (-1462470921235125401624248320) }] }

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

end TermShard4


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 6001301100104486975779151277981696
def positiveArguments : Array ℕ := #[
    801, 9, 27, 57, 147, 123,
    3441, 105
  ]
def positiveCoefficients : Array ℕ := #[
    63461758173925734412428704219136, 5570730176784211237046059008, 4178047632588158427784544256, 4410161389954167229328130048, 5686787055467215637817851904, 76133312416050886906296139776,
    133117239849406047685246451712, 4061990753905154027012751360
  ]
def positiveScales : Array ℕ := #[
    9, 3, 4, 5, 7, 6,
    11, 6
  ]
def negativeArguments : Array ℕ := #[
    6018864885, 634246095, 335385, 1900812655, 37070963965, 74141900735,
    237602715, 33669339, 3935292075, 1077418485, 1900812655, 37070963965,
    74141900735, 237602715, 1739582515, 203323423875, 55666621725, 57,
    57, 33669339, 3935292075, 1077418485, 57, 57,
    2106305915, 41078635745, 82157241355, 263289495, 886625927, 103629357975,
    28372020105, 111, 111, 886625927, 103629357975, 28372020105,
    3441, 3441, 111, 111, 33831249, 404775,
    335385, 4031697915, 2255175, 1082599605, 9032265, 9032265,
    6464835, 335385, 19599597, 796563, 19599597, 796563,
    147, 147
  ]
def negativeCoefficients : Array ℕ := #[
    13878557518479033988829675520, 1462471924276834409581117440, 12373522522322155937464320, 2191487786178335531629281280, 85479823103508011479130439680, 85479791749807693695926927360,
    2191498237411774792697118720, 2484358718655871523588407296, 9074165720352801790781030400, 2484357881634859179017502720, 2191487786178335531629281280, 85479823103508011479130439680,
    85479791749807693695926927360, 2191498237411774792697118720, 64179266898610014359367188480, 234415947775780712928509952000, 64179245275567195457952153600, 1102540347488541807332032512,
    1102540347488541807332032512, 2484358718655871523588407296, 9074165720352801790781030400, 2484357881634859179017502720, 1102540347488541807332032512, 1102540347488541807332032512,
    2428405384684101535048663040, 94720885060644012720117514240, 94720850317354471392783892480, 2428416965780615310826536960, 65421446257937950121161392128, 238953030635957113823900467200,
    65421424216384625047460904960, 1073526127817790707139084288, 1073526127817790707139084288, 65421446257937950121161392128, 238953030635957113823900467200, 65421424216384625047460904960,
    33279309962351511921311612928, 33279309962351511921311612928, 1073526127817790707139084288, 1073526127817790707139084288, 2496305567987768777596993536, 238936986637945080171724800,
    12373522522322155937464320, 9296462452564175695726510080, 332805088531423504524902400, 2496304730966756433026088960, 333231761721848406453780480, 333231761721848406453780480,
    238510313447520178242846720, 12373522522322155937464320, 1446194999227382026897195008, 58775975198345206255583232, 1446194999227382026897195008, 58775975198345206255583232,
    1421696763866803909454462976, 1421696763866803909454462976
  ]
def negativeScales : Array ℕ := #[
    32, 29, 18, 30, 35, 36,
    27, 25, 31, 30, 30, 35,
    36, 27, 30, 37, 35, 5,
    5, 25, 31, 30, 5, 5,
    30, 35, 36, 27, 29, 36,
    34, 6, 6, 29, 36, 34,
    11, 11, 6, 6, 25, 18,
    18, 31, 21, 30, 23, 23,
    22, 18, 24, 19, 24, 19,
    7, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9645658432407524, 3169925001442312, 4754887502147955, 5832890014087662, 7199672344836364, 6942514504772358,
    11748612176723449, 6714245517659862
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32486844284626926, 29240467490863119, 18355458640651126, 30823969201314635, 35109570579257115, 36109570050081520,
    27823976081529577, 25004932062514525, 31873823572357836, 30004931576446930, 30823969201314635, 35109570579257115,
    36109570050081520, 27823976081529577, 30696093967133621, 37564985474202159, 35696093481066025, 5832890015409720,
    5832890015409720, 25004932062514525, 31873823572357836, 30004931576446930, 5832890015409720, 5832890015409720,
    30972067854318208, 35257669218246249, 36257668689070654, 27972074734534713, 29723750310095794, 36592641817107550,
    34723749824028198, 6794415866926375, 6794415866926375, 29723750310095794, 36592641817107550, 34723749824028198,
    11748612176955137, 11748612176955137, 6794415866926375, 6794415866926375, 25011853104507595, 18626760662480181,
    18355458640651126, 31908740404461534, 21104807959273164, 30011852620766229, 23106656383665533, 23106656383665533,
    22624182118377635, 18355458640651126, 24224320654670451, 19603428943153129, 24224320654670451, 19603428943153129,
    7199672344836365, 7199672344836365
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 56
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
noncomputable def positiveFloor : ℝ := 3697511093 / 500000000000
noncomputable def negativeCeiling : ℝ := 367606087 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13878557518479033988829675520, coefficient := (-13878557518479033988829675520) }, { argument := 1462471924276834409581117440, coefficient := (-1462471924276834409581117440) }, { argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 2191487786178335531629281280, coefficient := (-2191487786178335531629281280) }, { argument := 85479823103508011479130439680, coefficient := (-85479823103508011479130439680) }, { argument := 85479791749807693695926927360, coefficient := (-85479791749807693695926927360) }, { argument := 2191498237411774792697118720, coefficient := (-2191498237411774792697118720) }, { argument := 2484358718655871523588407296, coefficient := (-2484358718655871523588407296) }, { argument := 9074165720352801790781030400, coefficient := (-9074165720352801790781030400) }, { argument := 2484357881634859179017502720, coefficient := (-2484357881634859179017502720) }, { argument := 2191487786178335531629281280, coefficient := (-2191487786178335531629281280) }, { argument := 85479823103508011479130439680, coefficient := (-85479823103508011479130439680) }, { argument := 85479791749807693695926927360, coefficient := (-85479791749807693695926927360) }, { argument := 2191498237411774792697118720, coefficient := (-2191498237411774792697118720) }, { argument := 64179266898610014359367188480, coefficient := (-64179266898610014359367188480) }, { argument := 234415947775780712928509952000, coefficient := (-234415947775780712928509952000) }, { argument := 64179245275567195457952153600, coefficient := (-64179245275567195457952153600) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 2484358718655871523588407296, coefficient := (-2484358718655871523588407296) }, { argument := 9074165720352801790781030400, coefficient := (-9074165720352801790781030400) }, { argument := 2484357881634859179017502720, coefficient := (-2484357881634859179017502720) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 2428405384684101535048663040, coefficient := (-2428405384684101535048663040) }, { argument := 94720885060644012720117514240, coefficient := (-94720885060644012720117514240) }, { argument := 94720850317354471392783892480, coefficient := (-94720850317354471392783892480) }, { argument := 2428416965780615310826536960, coefficient := (-2428416965780615310826536960) }, { argument := 65421446257937950121161392128, coefficient := (-65421446257937950121161392128) }, { argument := 238953030635957113823900467200, coefficient := (-238953030635957113823900467200) }, { argument := 65421424216384625047460904960, coefficient := (-65421424216384625047460904960) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 65421446257937950121161392128, coefficient := (-65421446257937950121161392128) }, { argument := 238953030635957113823900467200, coefficient := (-238953030635957113823900467200) }, { argument := 65421424216384625047460904960, coefficient := (-65421424216384625047460904960) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 2496305567987768777596993536, coefficient := (-2496305567987768777596993536) }, { argument := 238936986637945080171724800, coefficient := (-238936986637945080171724800) }, { argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 9296462452564175695726510080, coefficient := (-9296462452564175695726510080) }, { argument := 332805088531423504524902400, coefficient := (-332805088531423504524902400) }, { argument := 2496304730966756433026088960, coefficient := (-2496304730966756433026088960) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 238510313447520178242846720, coefficient := (-238510313447520178242846720) }, { argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 1446194999227382026897195008, coefficient := (-1446194999227382026897195008) }, { argument := 58775975198345206255583232, coefficient := (-58775975198345206255583232) }, { argument := 1446194999227382026897195008, coefficient := (-1446194999227382026897195008) }, { argument := 58775975198345206255583232, coefficient := (-58775975198345206255583232) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 63461758173925734412428704219136, coefficient := 63461758173925734412428704219136 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }] }

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

end TermShard5


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
