import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-250689727697161932675880058880000)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    39843, 2109, 24453, 39843, 4565637279, 2109,
    2109, 2337, 8724919883, 517763748565, 139572070523, 12893291519,
    12893289473, 43475, 32375, 34225, 2775, 594775,
    1075775, 32375, 594775, 17575, 17575, 34225,
    34225, 1075775, 34225, 43475, 2775, 4978323,
    203962815, 4199752305, 203962815, 4978323, 43475, 32375,
    34225, 2775, 594775, 1075775, 32375, 594775,
    17575, 17575, 34225, 34225, 1075775, 34225,
    43475, 2775, 257213355, 10538078775, 216987202425, 10538078775,
    257213355, 585666621, 2337, 89111084919, 24453, 1083,
    22277779395, 1083, 2109, 39843
  ]
def negativeCoefficients : Array ℕ := #[
    6020903928863208775977271296, 159351534597953308090957824, 1847616441689782950568132608, 6020903928863208775977271296, 5263821401193790792274018304, 159351534597953308090957824,
    159351534597953308090957824, 176578727527461773830520832, 160946364145320884461453180928, 596940960026441006859094589440, 160915641548470115522941288448, 59459812229680718179966386176,
    59459802794171124477530734592, 205304882842757825665433600, 152886614882904763793408000, 161622992876213607438745600, 209673071839412247488102400, 2808745524848793231976038400,
    5080203803109092579763814400, 152886614882904763793408000, 2808745524848793231976038400, 165991181872868029261414400, 165991181872868029261414400, 161622992876213607438745600,
    161622992876213607438745600, 5080203803109092579763814400, 161622992876213607438745600, 205304882842757825665433600, 209673071839412247488102400, 45916925148630978064809984,
    7524899697716735279974318080, 77471755943306779299812474880, 7524899697716735279974318080, 45916925148630978064809984, 205304882842757825665433600, 152886614882904763793408000,
    161622992876213607438745600, 209673071839412247488102400, 2808745524848793231976038400, 5080203803109092579763814400, 152886614882904763793408000, 2808745524848793231976038400,
    165991181872868029261414400, 165991181872868029261414400, 161622992876213607438745600, 161622992876213607438745600, 5080203803109092579763814400, 161622992876213607438745600,
    205304882842757825665433600, 209673071839412247488102400, 1186187233006300266674257920, 194393242191015661399336550400, 2001353695202091798578488934400, 194393242191015661399336550400,
    1186187233006300266674257920, 5401821135050624015183904768, 176578727527461773830520832, 205476172203923981174348709888, 1847616441689782950568132608, 163658332830330424525848576,
    205476247515062505102806876160, 163658332830330424525848576, 159351534597953308090957824, 6020903928863208775977271296
  ]
def negativeScales : Array ℕ := #[
    15, 11, 14, 15, 32, 11,
    11, 11, 33, 38, 37, 33,
    33, 15, 14, 15, 11, 19,
    20, 14, 19, 14, 14, 15,
    15, 20, 15, 15, 11, 22,
    27, 31, 27, 22, 15, 14,
    15, 11, 19, 20, 14, 19,
    14, 14, 15, 15, 20, 15,
    15, 11, 27, 33, 37, 33,
    27, 29, 11, 36, 14, 10,
    34, 10, 11, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15282038659540179, 11042343379793692, 14577723851667303, 15282038659540179, 32088169101946989, 11042343379793692,
    11042343379793692, 11190442018782826, 33022494737752188, 38913503007220198, 37022219319483052, 33585901564163185,
    33585901335225968, 15407898407081321, 14982592590237647, 15062762921032625, 11438272056124861, 19181984482731622,
    20036944936876893, 14982592590237647, 19181984482731622, 14101237068847261, 14101237068847261, 15062762921032625,
    15062762921032625, 20036944936876893, 15062762921032625, 15407898407081321, 11438272056124861, 22247228406589859,
    27603730913728279, 31967657110430971, 27603730913728279, 22247228406589859, 15407898407081321, 14982592590237647,
    15062762921032625, 11438272056124861, 19181984482731622, 20036944936876893, 14982592590237647, 19181984482731622,
    14101237068847261, 14101237068847261, 15062762921032625, 15062762921032625, 20036944936876893, 15062762921032625,
    15407898407081321, 11438272056124861, 27938390319699783, 33294892818275093, 37658819001008346, 33294892818275093,
    27938390319699783, 29125504432118948, 11190442018782826, 36374885854952601, 14577723851667303, 10080817527608328,
    34374886383729174, 10080817527608328, 11042343379793692, 15282038659540179
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
noncomputable def negativeCeiling : ℝ := 175331493 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6020903928863208775977271296, coefficient := (-6020903928863208775977271296) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 1847616441689782950568132608, coefficient := (-1847616441689782950568132608) }, { argument := 6020903928863208775977271296, coefficient := (-6020903928863208775977271296) }, { argument := 5263821401193790792274018304, coefficient := (-5263821401193790792274018304) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 176578727527461773830520832, coefficient := (-176578727527461773830520832) }, { argument := 160946364145320884461453180928, coefficient := (-160946364145320884461453180928) }, { argument := 596940960026441006859094589440, coefficient := (-596940960026441006859094589440) }, { argument := 160915641548470115522941288448, coefficient := (-160915641548470115522941288448) }, { argument := 59459812229680718179966386176, coefficient := (-59459812229680718179966386176) }, { argument := 59459802794171124477530734592, coefficient := (-59459802794171124477530734592) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 45916925148630978064809984, coefficient := (-45916925148630978064809984) }, { argument := 7524899697716735279974318080, coefficient := (-7524899697716735279974318080) }, { argument := 77471755943306779299812474880, coefficient := (-77471755943306779299812474880) }, { argument := 7524899697716735279974318080, coefficient := (-7524899697716735279974318080) }, { argument := 45916925148630978064809984, coefficient := (-45916925148630978064809984) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 152886614882904763793408000, coefficient := (-152886614882904763793408000) }, { argument := 2808745524848793231976038400, coefficient := (-2808745524848793231976038400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 165991181872868029261414400, coefficient := (-165991181872868029261414400) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 5080203803109092579763814400, coefficient := (-5080203803109092579763814400) }, { argument := 161622992876213607438745600, coefficient := (-161622992876213607438745600) }, { argument := 205304882842757825665433600, coefficient := (-205304882842757825665433600) }, { argument := 209673071839412247488102400, coefficient := (-209673071839412247488102400) }, { argument := 1186187233006300266674257920, coefficient := (-1186187233006300266674257920) }, { argument := 194393242191015661399336550400, coefficient := (-194393242191015661399336550400) }, { argument := 2001353695202091798578488934400, coefficient := (-2001353695202091798578488934400) }, { argument := 194393242191015661399336550400, coefficient := (-194393242191015661399336550400) }, { argument := 1186187233006300266674257920, coefficient := (-1186187233006300266674257920) }, { argument := 5401821135050624015183904768, coefficient := (-5401821135050624015183904768) }, { argument := 176578727527461773830520832, coefficient := (-176578727527461773830520832) }, { argument := 205476172203923981174348709888, coefficient := (-205476172203923981174348709888) }, { argument := 1847616441689782950568132608, coefficient := (-1847616441689782950568132608) }, { argument := 163658332830330424525848576, coefficient := (-163658332830330424525848576) }, { argument := 205476247515062505102806876160, coefficient := (-205476247515062505102806876160) }, { argument := 163658332830330424525848576, coefficient := (-163658332830330424525848576) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 6020903928863208775977271296, coefficient := (-6020903928863208775977271296) }] }

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

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-220916788126450478848444228173824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2109, 24453, 39843, 2342699145, 2109, 2109,
    2337, 4978323, 203962815, 4199752305, 203962815, 4978323,
    585224253, 4551, 89109512055, 47619, 2109, 22277386179,
    2109, 4107, 77589, 4107, 47619, 77589,
    2340929673, 4107, 4107, 4551, 854114511, 25342497985,
    6831613127, 48175, 35875, 37925, 3075, 659075,
    1192075, 35875, 659075, 19475, 19475, 37925,
    37925, 1192075, 37925, 48175, 3075, 131095839,
    5371020795, 110593477365, 5371020795, 131095839, 1140508683, 4551,
    173532112737, 47619, 2109, 43383044085, 2109, 4107,
    77589, 4107, 47619, 77589
  ]
def negativeCoefficients : Array ℕ := #[
    159351534597953308090957824, 1847616441689782950568132608, 6020903928863208775977271296, 5401896446189147943642071040, 159351534597953308090957824, 159351534597953308090957824,
    176578727527461773830520832, 45916925148630978064809984, 7524899697716735279974318080, 77471755943306779299812474880, 7524899697716735279974318080, 45916925148630978064809984,
    5397741010409424641719271424, 171931918908318042940243968, 205472545426465137286824591360, 1798994956382157083447918592, 159351534597953308090957824, 205472620737603661215282757632,
    159351534597953308090957824, 155158073161165063141195776, 5862459088629966439767343104, 155158073161165063141195776, 1798994956382157083447918592, 5862459088629966439767343104,
    5397816321547948570177437696, 155158073161165063141195776, 155158073161165063141195776, 171931918908318042940243968, 7877815897029290817264549888, 29217910907362187706483343360,
    7876313685272726775321853952, 227500005312245158169804800, 169414897572948522041344000, 179095748862831294729420800, 232340430957186544513843200, 3112393689697311419216691200,
    5629415025066832318116659200, 169414897572948522041344000, 3112393689697311419216691200, 183936174507772681073459200, 183936174507772681073459200, 179095748862831294729420800,
    179095748862831294729420800, 5629415025066832318116659200, 179095748862831294729420800, 227500005312245158169804800, 232340430957186544513843200, 1209145695580615755706662912,
    198155692039874029039323709440, 2040089573173745188228395171840, 198155692039874029039323709440, 1209145695580615755706662912, 5259667947286133909521170432, 171931918908318042940243968,
    200068904514347034301339533312, 1798994956382157083447918592, 159351534597953308090957824, 200068977843613491810627747840, 159351534597953308090957824, 155158073161165063141195776,
    5862459088629966439767343104, 155158073161165063141195776, 1798994956382157083447918592, 5862459088629966439767343104
  ]
def negativeScales : Array ℕ := #[
    11, 14, 15, 31, 11, 11,
    11, 22, 27, 31, 27, 22,
    29, 12, 36, 15, 11, 34,
    11, 12, 16, 12, 15, 16,
    31, 12, 12, 12, 29, 34,
    32, 15, 15, 15, 11, 19,
    20, 15, 19, 14, 14, 15,
    15, 20, 15, 15, 11, 26,
    32, 36, 32, 26, 30, 12,
    37, 15, 11, 35, 11, 12,
    16, 12, 15, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11042343379793692, 14577723851667303, 15282038659540179, 31125524545752104, 11042343379793692, 11042343379793692,
    11190442018782826, 22247228406589859, 27603730913728279, 31967657110430971, 27603730913728279, 22247228406589859,
    29124414318318620, 12151967870968190, 36374860390296648, 15539249703850609, 11042343379793692, 34374860919082554,
    11042343379793692, 12003869231979056, 16243564511725543, 12003869231979056, 15539249703850609, 16243564511725543,
    31124434447155461, 12003869231979056, 12003869231979056, 12151967870968190, 29669854263847217, 34560839685388633,
    32669579131736786, 15555997046072039, 15130691211337775, 15210861560021759, 11586370695117825, 19330083121720757,
    20185043575866027, 15130691211337775, 19330083121720757, 14249335707836394, 14249335707836394, 15210861560021759,
    15210861560021759, 20185043575866027, 15210861560021759, 15555997046072039, 11586370695117825, 26966046667679686,
    32322549161177958, 36686475343937075, 32322549161177958, 26966046667679686, 30087030284304312, 12151967870968190,
    37336411707137963, 15539249703850609, 11042343379793692, 35336412235914536, 11042343379793692, 12003869231979056,
    16243564511725543, 12003869231979056, 15539249703850609, 16243564511725543
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
noncomputable def negativeCeiling : ℝ := 369738323 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 1847616441689782950568132608, coefficient := (-1847616441689782950568132608) }, { argument := 6020903928863208775977271296, coefficient := (-6020903928863208775977271296) }, { argument := 5401896446189147943642071040, coefficient := (-5401896446189147943642071040) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 176578727527461773830520832, coefficient := (-176578727527461773830520832) }, { argument := 45916925148630978064809984, coefficient := (-45916925148630978064809984) }, { argument := 7524899697716735279974318080, coefficient := (-7524899697716735279974318080) }, { argument := 77471755943306779299812474880, coefficient := (-77471755943306779299812474880) }, { argument := 7524899697716735279974318080, coefficient := (-7524899697716735279974318080) }, { argument := 45916925148630978064809984, coefficient := (-45916925148630978064809984) }, { argument := 5397741010409424641719271424, coefficient := (-5397741010409424641719271424) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }, { argument := 205472545426465137286824591360, coefficient := (-205472545426465137286824591360) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 205472620737603661215282757632, coefficient := (-205472620737603661215282757632) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }, { argument := 5397816321547948570177437696, coefficient := (-5397816321547948570177437696) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }, { argument := 7877815897029290817264549888, coefficient := (-7877815897029290817264549888) }, { argument := 29217910907362187706483343360, coefficient := (-29217910907362187706483343360) }, { argument := 7876313685272726775321853952, coefficient := (-7876313685272726775321853952) }, { argument := 227500005312245158169804800, coefficient := (-227500005312245158169804800) }, { argument := 169414897572948522041344000, coefficient := (-169414897572948522041344000) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 3112393689697311419216691200, coefficient := (-3112393689697311419216691200) }, { argument := 5629415025066832318116659200, coefficient := (-5629415025066832318116659200) }, { argument := 169414897572948522041344000, coefficient := (-169414897572948522041344000) }, { argument := 3112393689697311419216691200, coefficient := (-3112393689697311419216691200) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 5629415025066832318116659200, coefficient := (-5629415025066832318116659200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 227500005312245158169804800, coefficient := (-227500005312245158169804800) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 2040089573173745188228395171840, coefficient := (-2040089573173745188228395171840) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 5259667947286133909521170432, coefficient := (-5259667947286133909521170432) }, { argument := 171931918908318042940243968, coefficient := (-171931918908318042940243968) }, { argument := 200068904514347034301339533312, coefficient := (-200068904514347034301339533312) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 200068977843613491810627747840, coefficient := (-200068977843613491810627747840) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }, { argument := 155158073161165063141195776, coefficient := (-155158073161165063141195776) }, { argument := 1798994956382157083447918592, coefficient := (-1798994956382157083447918592) }, { argument := 5862459088629966439767343104, coefficient := (-5862459088629966439767343104) }] }

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

end TermShard9


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
