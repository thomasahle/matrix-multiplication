import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 13, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

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
def constantNumerator : ℤ := (-241558459259683323928394407608320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    89109512055, 47619, 2109, 22277386179, 2109, 4107,
    77589, 4107, 47619, 77589, 2340929673, 4107,
    4107, 4551, 84453786132155, 306909976683231, 42224234020659, 43475,
    32375, 34225, 2775, 594775, 1075775, 32375,
    594775, 17575, 17575, 34225, 34225, 1075775,
    34225, 43475, 2775, 821325, 611625, 646575,
    52425, 11236425, 20323425, 611625, 11236425, 332025,
    332025, 646575, 646575, 20323425, 646575, 821325,
    52425, 131095839, 5371020795, 110593477365, 5371020795, 131095839,
    43475, 32375, 34225, 2775, 594775, 1075775,
    32375, 594775, 17575, 17575
  ]
def negativeCoefficients : Array ℕ := #[
    205472545426465137286824591360, 1798994956382157083447918592, 159351534597953308090957824, 205472620737603661215282757632, 159351534597953308090957824, 155158073161165063141195776,
    5862459088629966439767343104, 155158073161165063141195776, 1798994956382157083447918592, 5862459088629966439767343104, 5397816321547948570177437696, 155158073161165063141195776,
    155158073161165063141195776, 171931918908318042940243968, 23771627484675051290812743680, 86387478539180421717254209536, 23770130575180561562738884608, 205304882842757825665433600,
    152886614882904763793408000, 161622992876213607438745600, 209673071839412247488102400, 2808745524848793231976038400, 5080203803109092579763814400, 152886614882904763793408000,
    2808745524848793231976038400, 165991181872868029261414400, 165991181872868029261414400, 161622992876213607438745600, 161622992876213607438745600, 5080203803109092579763814400,
    161622992876213607438745600, 205304882842757825665433600, 209673071839412247488102400, 7757195303085822710277734400, 5776634800170293507653632000, 6106728217322881708090982400,
    7922242011662116810496409600, 106125033614557106440608153600, 191949322074230038554319257600, 5776634800170293507653632000, 106125033614557106440608153600, 6271774925899175808309657600,
    6271774925899175808309657600, 6106728217322881708090982400, 6106728217322881708090982400, 191949322074230038554319257600, 6106728217322881708090982400, 7757195303085822710277734400,
    7922242011662116810496409600, 1209145695580615755706662912, 198155692039874029039323709440, 2040089573173745188228395171840, 198155692039874029039323709440, 1209145695580615755706662912,
    205304882842757825665433600, 152886614882904763793408000, 161622992876213607438745600, 209673071839412247488102400, 2808745524848793231976038400, 5080203803109092579763814400,
    152886614882904763793408000, 2808745524848793231976038400, 165991181872868029261414400, 165991181872868029261414400
  ]
def negativeScales : Array ℕ := #[
    36, 15, 11, 34, 11, 12,
    16, 12, 15, 16, 31, 12,
    12, 12, 46, 48, 45, 15,
    14, 15, 11, 19, 20, 14,
    19, 14, 14, 15, 15, 20,
    15, 15, 11, 19, 19, 19,
    15, 23, 24, 19, 23, 18,
    18, 19, 19, 24, 19, 19,
    15, 26, 32, 36, 32, 26,
    15, 14, 15, 11, 19, 20,
    14, 19, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36374860390296648, 15539249703850609, 11042343379793692, 34374860919082554, 11042343379793692, 12003869231979056,
    16243564511725543, 12003869231979056, 15539249703850609, 16243564511725543, 31124434447155461, 12003869231979056,
    12003869231979056, 12151967870968190, 46263227335208247, 48124808872492309, 45263136485227380, 15407898407081321,
    14982592590237647, 15062762921032625, 11438272056124861, 19181984482731622, 20036944936876893, 14982592590237647,
    19181984482731622, 14101237068847261, 14101237068847261, 15062762921032625, 15062762921032625, 20036944936876893,
    15062762921032625, 15407898407081321, 11438272056124861, 19647593686847837, 19222287852095128, 19302458200779112,
    15677967335914047, 23421679762478125, 24276640216623380, 19222287852095128, 23421679762478125, 18340932348593748,
    18340932348593748, 19302458200779112, 19302458200779112, 24276640216623380, 19302458200779112, 19647593686847837,
    15677967335914047, 26966046667679686, 32322549161177958, 36686475343937075, 32322549161177958, 26966046667679686,
    15407898407081321, 14982592590237647, 15062762921032625, 11438272056124861, 19181984482731622, 20036944936876893,
    14982592590237647, 19181984482731622, 14101237068847261, 14101237068847261
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
noncomputable def negativeCeiling : ℝ := 1508875351 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 205472545426465137286824591360, coefficient := (-205472545426465137286824591360) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 205472620737603661215282757632, coefficient := (-205472620737603661215282757632) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }, { argument := 5397816321547948570177437696, coefficient := (-5397816321547948570177437696) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }, { argument := 23771627484675051290812743680, coefficient := (-23771627484675051290812743680) }, { argument := 86387478539180421717254209536, coefficient := (-86387478539180421717254209536) }, { argument := 23770130575180561562738884608, coefficient := (-23770130575180561562738884608) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 7757195303085822710277734400, coefficient := (-7757195303085822710277734400) }, { argument := 5776634800170293507653632000, coefficient := (-5776634800170293507653632000) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 7922242011662116810496409600, coefficient := (-7922242011662116810496409600) }, { argument := 106125033614557106440608153600, coefficient := (-106125033614557106440608153600) }, { argument := 191949322074230038554319257600, coefficient := (-191949322074230038554319257600) }, { argument := 5776634800170293507653632000, coefficient := (-5776634800170293507653632000) }, { argument := 106125033614557106440608153600, coefficient := (-106125033614557106440608153600) }, { argument := 6271774925899175808309657600, coefficient := (-6271774925899175808309657600) }, { argument := 6271774925899175808309657600, coefficient := (-6271774925899175808309657600) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 191949322074230038554319257600, coefficient := (-191949322074230038554319257600) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 7757195303085822710277734400, coefficient := (-7757195303085822710277734400) }, { argument := 7922242011662116810496409600, coefficient := (-7922242011662116810496409600) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 2040089573173745188228395171840, coefficient := (-2040089573173745188228395171840) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }] }

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
def constantNumerator : ℤ := (-353353506732502013203205377228800)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    34225, 34225, 1075775, 34225, 43475, 2775,
    260532237, 10674053985, 219787037295, 10674053985, 260532237, 1509518655,
    369, 229809652221, 3861, 171, 57452434113, 171,
    333, 6291, 333, 3861, 6291, 6038158851,
    333, 333, 369, 504075, 375375, 396825,
    32175, 6896175, 12473175, 375375, 6896175, 203775,
    203775, 396825, 396825, 12473175, 396825, 504075,
    32175, 41486025, 1699690125, 34997935875, 1699690125, 41486025,
    821325, 611625, 646575, 52425, 11236425, 20323425,
    611625, 11236425, 332025, 332025, 646575, 646575,
    20323425, 646575, 821325, 52425
  ]
def negativeCoefficients : Array ℕ := #[
    161622992876213607438745600, 161622992876213607438745600, 5080203803109092579763814400, 161622992876213607438745600, 205304882842757825665433600, 209673071839412247488102400,
    1201492874722510592695861248, 196901542090254573159327989760, 2027177613849860725011759759360, 196901542090254573159327989760, 1201492874722510592695861248, 6961426075818815804009349120,
    223046813718899082733289472, 264952490011811552889925533696, 2333831294766041621770272768, 206726315154101588874756096, 264952587123542807429253169152, 206726315154101588874756096,
    201286148965835757588578304, 7605352331195632138076553216, 201286148965835757588578304, 2333831294766041621770272768, 7605352331195632138076553216, 6961523187550070343336984576,
    201286148965835757588578304, 201286148965835757588578304, 223046813718899082733289472, 2380426884852516411093811200, 1772658318507193072091136000, 1873953079564746961924915200,
    2431074265381293356010700800, 32566265680003575581560012800, 58902903554967586938342604800, 1772658318507193072091136000, 32566265680003575581560012800, 1924600460093523906841804800,
    1924600460093523906841804800, 1873953079564746961924915200, 1873953079564746961924915200, 58902903554967586938342604800, 1873953079564746961924915200, 2380426884852516411093811200,
    2431074265381293356010700800, 765282085810516301080166400, 125414994961945587999571968000, 1291195932388446321663541248000, 125414994961945587999571968000, 765282085810516301080166400,
    7757195303085822710277734400, 5776634800170293507653632000, 6106728217322881708090982400, 7922242011662116810496409600, 106125033614557106440608153600, 191949322074230038554319257600,
    5776634800170293507653632000, 106125033614557106440608153600, 6271774925899175808309657600, 6271774925899175808309657600, 6106728217322881708090982400, 6106728217322881708090982400,
    191949322074230038554319257600, 6106728217322881708090982400, 7757195303085822710277734400, 7922242011662116810496409600
  ]
def negativeScales : Array ℕ := #[
    15, 15, 20, 15, 15, 11,
    27, 33, 37, 33, 27, 30,
    8, 37, 11, 7, 35, 7,
    8, 12, 8, 11, 12, 32,
    8, 8, 8, 18, 18, 18,
    14, 22, 23, 18, 22, 17,
    17, 18, 18, 23, 18, 18,
    14, 25, 30, 35, 30, 25,
    19, 19, 19, 15, 23, 24,
    19, 23, 18, 18, 19, 19,
    24, 19, 19, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15062762921032625, 15062762921032625, 20036944936876893, 15062762921032625, 15407898407081321, 11438272056124861,
    27956886666464395, 33313389161892482, 37677315344641168, 33313389161892482, 27956886666464395, 30491441440125638,
    8527477006061059, 37741648437749969, 11914758844619001, 7417852514885912, 35741648966533783, 7417852514885912,
    8379378367071265, 12619073646827253, 8379378367071265, 11914758844619001, 12619073646827253, 32491461565547407,
    8379378367071265, 8379378367071265, 8527477006061059, 18943278888253396, 18517973044219726, 18598143392908592,
    14973652543452428, 22717364954710554, 23572325408750069, 18517973044219726, 22717364954710554, 17636617540732957,
    17636617540732957, 18598143392908592, 18598143392908592, 23572325408750069, 18598143392908592, 18943278888253396,
    14973652543452428, 25306122095643427, 30662624602804861, 35026550785482210, 30662624602804861, 25306122095643427,
    19647593686847837, 19222287852095128, 19302458200779112, 15677967335914047, 23421679762478125, 24276640216623380,
    19222287852095128, 23421679762478125, 18340932348593748, 18340932348593748, 19302458200779112, 19302458200779112,
    24276640216623380, 19302458200779112, 19647593686847837, 15677967335914047
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
noncomputable def negativeCeiling : ℝ := 1102985999 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 1201492874722510592695861248, coefficient := (-1201492874722510592695861248) }, { argument := 196901542090254573159327989760, coefficient := (-196901542090254573159327989760) }, { argument := 2027177613849860725011759759360, coefficient := (-2027177613849860725011759759360) }, { argument := 196901542090254573159327989760, coefficient := (-196901542090254573159327989760) }, { argument := 1201492874722510592695861248, coefficient := (-1201492874722510592695861248) }, { argument := 6961426075818815804009349120, coefficient := (-6961426075818815804009349120) }, { argument := 223046813718899082733289472, coefficient := (-223046813718899082733289472) }, { argument := 264952490011811552889925533696, coefficient := (-264952490011811552889925533696) }, { argument := 2333831294766041621770272768, coefficient := (-2333831294766041621770272768) }, { argument := 206726315154101588874756096, coefficient := (-206726315154101588874756096) }, { argument := 264952587123542807429253169152, coefficient := (-264952587123542807429253169152) }, { argument := 206726315154101588874756096, coefficient := (-206726315154101588874756096) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 7605352331195632138076553216, coefficient := (-7605352331195632138076553216) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 2333831294766041621770272768, coefficient := (-2333831294766041621770272768) }, { argument := 7605352331195632138076553216, coefficient := (-7605352331195632138076553216) }, { argument := 6961523187550070343336984576, coefficient := (-6961523187550070343336984576) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 201286148965835757588578304, coefficient := (-201286148965835757588578304) }, { argument := 223046813718899082733289472, coefficient := (-223046813718899082733289472) }, { argument := 2380426884852516411093811200, coefficient := (-2380426884852516411093811200) }, { argument := 1772658318507193072091136000, coefficient := (-1772658318507193072091136000) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 2431074265381293356010700800, coefficient := (-2431074265381293356010700800) }, { argument := 32566265680003575581560012800, coefficient := (-32566265680003575581560012800) }, { argument := 58902903554967586938342604800, coefficient := (-58902903554967586938342604800) }, { argument := 1772658318507193072091136000, coefficient := (-1772658318507193072091136000) }, { argument := 32566265680003575581560012800, coefficient := (-32566265680003575581560012800) }, { argument := 1924600460093523906841804800, coefficient := (-1924600460093523906841804800) }, { argument := 1924600460093523906841804800, coefficient := (-1924600460093523906841804800) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 58902903554967586938342604800, coefficient := (-58902903554967586938342604800) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 2380426884852516411093811200, coefficient := (-2380426884852516411093811200) }, { argument := 2431074265381293356010700800, coefficient := (-2431074265381293356010700800) }, { argument := 765282085810516301080166400, coefficient := (-765282085810516301080166400) }, { argument := 125414994961945587999571968000, coefficient := (-125414994961945587999571968000) }, { argument := 1291195932388446321663541248000, coefficient := (-1291195932388446321663541248000) }, { argument := 125414994961945587999571968000, coefficient := (-125414994961945587999571968000) }, { argument := 765282085810516301080166400, coefficient := (-765282085810516301080166400) }, { argument := 7757195303085822710277734400, coefficient := (-7757195303085822710277734400) }, { argument := 5776634800170293507653632000, coefficient := (-5776634800170293507653632000) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 7922242011662116810496409600, coefficient := (-7922242011662116810496409600) }, { argument := 106125033614557106440608153600, coefficient := (-106125033614557106440608153600) }, { argument := 191949322074230038554319257600, coefficient := (-191949322074230038554319257600) }, { argument := 5776634800170293507653632000, coefficient := (-5776634800170293507653632000) }, { argument := 106125033614557106440608153600, coefficient := (-106125033614557106440608153600) }, { argument := 6271774925899175808309657600, coefficient := (-6271774925899175808309657600) }, { argument := 6271774925899175808309657600, coefficient := (-6271774925899175808309657600) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 191949322074230038554319257600, coefficient := (-191949322074230038554319257600) }, { argument := 6106728217322881708090982400, coefficient := (-6106728217322881708090982400) }, { argument := 7757195303085822710277734400, coefficient := (-7757195303085822710277734400) }, { argument := 7922242011662116810496409600, coefficient := (-7922242011662116810496409600) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
