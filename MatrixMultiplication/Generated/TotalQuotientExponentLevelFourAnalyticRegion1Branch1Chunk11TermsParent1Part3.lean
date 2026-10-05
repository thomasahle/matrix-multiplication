import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-759029584084838355085612436946944)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    80185, 80185, 5029060634075, 219067, 163135, 172457,
    13983, 2997023, 5420743, 163135, 2997023, 88559,
    88559, 172457, 172457, 5420743, 172457, 219067,
    13983, 35294733, 913005345, 1473113, 17700853743, 466175,
    55941, 1473113, 2927579, 466175, 45181681, 2890285,
    913005345, 1473113, 55941, 2890285, 55941, 1473113,
    1473113, 35294733, 87448939993405, 3421866883363523, 3421866953905859, 87449077292349,
    32468985, 826247805, 43529, 15974250003, 13775, 1653,
    43529, 86507, 13775, 1335073, 85405, 826247805,
    43529, 1653, 85405, 1653, 43529, 43529,
    32468985, 12955827705, 63317770509, 506542240761
  ]
def negativeCoefficients : Array ℕ := #[
    1514651825715610005840855040, 1514651825715610005840855040, 22648875597643800338707251200, 2069029316605609136057483264, 1540766512365879143872593920, 1628810313072500809236742144,
    2113051216958919968739557376, 28306081927178865414573654016, 51197470110900498409252192256, 1540766512365879143872593920, 28306081927178865414573654016, 1672832213425811641918816256,
    1672832213425811641918816256, 1628810313072500809236742144, 1628810313072500809236742144, 51197470110900498409252192256, 1628810313072500809236742144, 2069029316605609136057483264,
    2113051216958919968739557376, 2604291627203643775345754112, 269471614994302313647382200320, 27826317826718206678733422592, 2612184951066278276935402389504, 17611593561214054859957862400,
    1056695613672843291597471744, 27826317826718206678733422592, 27650201891106066130133843968, 17611593561214054859957862400, 426728911988216549256779005952, 27297970019881785032934686720,
    269471614994302313647382200320, 27826317826718206678733422592, 1056695613672843291597471744, 27297970019881785032934686720, 1056695613672843291597471744, 27826317826718206678733422592,
    27826317826718206678733422592, 2604291627203643775345754112, 98458753392060905732932894720, 3852679605206850670256143204352, 3852679684630460201117224534016, 98458907976929164923582283776,
    149736764157028581444157440, 15241581800299275230254202880, 1644479125062662292055785472, 147336450787397518561508327424, 1040809572824469805098598400, 62448574369468188305915904,
    1644479125062662292055785472, 1634071029334417594004799488, 1040809572824469805098598400, 25218815949536903377539039232, 1613254837877928197902827520, 15241581800299275230254202880,
    1644479125062662292055785472, 62448574369468188305915904, 1613254837877928197902827520, 62448574369468188305915904, 1644479125062662292055785472, 1644479125062662292055785472,
    149736764157028581444157440, 14937052371075673184356270080, 584003353948698584771589046272, 584003442365095851566076788736
  ]
def negativeScales : Array ℕ := #[
    16, 16, 42, 17, 17, 17,
    13, 21, 22, 17, 21, 16,
    16, 17, 17, 22, 17, 17,
    13, 25, 29, 20, 34, 18,
    15, 20, 21, 18, 25, 21,
    29, 20, 15, 21, 15, 20,
    20, 25, 46, 51, 51, 46,
    24, 29, 15, 33, 13, 10,
    15, 16, 13, 20, 16, 29,
    15, 10, 16, 10, 15, 15,
    24, 33, 35, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16291044760249642, 16291044760249642, 42193426086368480, 17741012649401125, 17315706814483911, 17395877163167900,
    13771386298616460, 21515098724867337, 22370059179012165, 17315706814483911, 21515098724867337, 16434351310982556,
    16434351310982556, 17395877163167900, 17395877163167900, 22370059179012165, 17395877163167900, 17741012649401125,
    13771386298616460, 25072949571738482, 29766048065609420, 20490436670632819, 34043099894554130, 18830512113418682,
    15771618423534793, 20490436670632819, 21481276671347290, 18830512113418682, 25429234611906888, 21462780327729832,
    29766048065609420, 20490436670632819, 15771618423534793, 21462780327729832, 15771618423534793, 20490436670632819,
    20490436670632819, 25072949571738482, 46313506130255237, 51603705060862689, 51603705090604078, 46313508395352448,
    24952558960909383, 29621999293088270, 15409689256748271, 33895029150559418, 13749764698569610, 10690871009350625,
    15409689256748271, 16400529257462792, 13749764698569610, 20348487198022505, 16382032913845399, 29621999293088270,
    15409689256748271, 10690871009350625, 16382032913845399, 10690871009350625, 15409689256748271, 15409689256748271,
    24952558960909383, 33592882136357182, 35881891409448614, 38881891627868414
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
noncomputable def negativeCeiling : ℝ := 7026171683 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 22648875597643800338707251200, coefficient := (-22648875597643800338707251200) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1540766512365879143872593920, coefficient := (-1540766512365879143872593920) }, { argument := 28306081927178865414573654016, coefficient := (-28306081927178865414573654016) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1672832213425811641918816256, coefficient := (-1672832213425811641918816256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 51197470110900498409252192256, coefficient := (-51197470110900498409252192256) }, { argument := 1628810313072500809236742144, coefficient := (-1628810313072500809236742144) }, { argument := 2069029316605609136057483264, coefficient := (-2069029316605609136057483264) }, { argument := 2113051216958919968739557376, coefficient := (-2113051216958919968739557376) }, { argument := 2604291627203643775345754112, coefficient := (-2604291627203643775345754112) }, { argument := 269471614994302313647382200320, coefficient := (-269471614994302313647382200320) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 2612184951066278276935402389504, coefficient := (-2612184951066278276935402389504) }, { argument := 17611593561214054859957862400, coefficient := (-17611593561214054859957862400) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 27650201891106066130133843968, coefficient := (-27650201891106066130133843968) }, { argument := 17611593561214054859957862400, coefficient := (-17611593561214054859957862400) }, { argument := 426728911988216549256779005952, coefficient := (-426728911988216549256779005952) }, { argument := 27297970019881785032934686720, coefficient := (-27297970019881785032934686720) }, { argument := 269471614994302313647382200320, coefficient := (-269471614994302313647382200320) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 27297970019881785032934686720, coefficient := (-27297970019881785032934686720) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 2604291627203643775345754112, coefficient := (-2604291627203643775345754112) }, { argument := 98458753392060905732932894720, coefficient := (-98458753392060905732932894720) }, { argument := 3852679605206850670256143204352, coefficient := (-3852679605206850670256143204352) }, { argument := 3852679684630460201117224534016, coefficient := (-3852679684630460201117224534016) }, { argument := 98458907976929164923582283776, coefficient := (-98458907976929164923582283776) }, { argument := 149736764157028581444157440, coefficient := (-149736764157028581444157440) }, { argument := 15241581800299275230254202880, coefficient := (-15241581800299275230254202880) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 147336450787397518561508327424, coefficient := (-147336450787397518561508327424) }, { argument := 1040809572824469805098598400, coefficient := (-1040809572824469805098598400) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 1634071029334417594004799488, coefficient := (-1634071029334417594004799488) }, { argument := 1040809572824469805098598400, coefficient := (-1040809572824469805098598400) }, { argument := 25218815949536903377539039232, coefficient := (-25218815949536903377539039232) }, { argument := 1613254837877928197902827520, coefficient := (-1613254837877928197902827520) }, { argument := 15241581800299275230254202880, coefficient := (-15241581800299275230254202880) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1613254837877928197902827520, coefficient := (-1613254837877928197902827520) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 149736764157028581444157440, coefficient := (-149736764157028581444157440) }, { argument := 14937052371075673184356270080, coefficient := (-14937052371075673184356270080) }, { argument := 584003353948698584771589046272, coefficient := (-584003353948698584771589046272) }, { argument := 584003442365095851566076788736, coefficient := (-584003442365095851566076788736) }] }

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


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-57687435589485236923861817098240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6477988563, 2085646257, 7656921373, 1042684825, 8319, 6195,
    6549, 531, 113811, 205851, 6195, 113811,
    3363, 3363, 6549, 6549, 205851, 6549,
    8319, 531, 429815, 320075, 338365, 27435,
    5880235, 10635635, 320075, 5880235, 173755, 173755,
    338365, 338365, 10635635, 338365, 429815, 27435,
    16490271, 423603195, 43529, 8202901749, 13775, 1653,
    43529, 86507, 13775, 1335073, 85405, 423603195,
    43529, 1653, 85405, 1653, 43529, 43529,
    16490271, 8319, 6195, 6549, 531, 113811,
    205851, 6195, 113811, 3363
  ]
def negativeCoefficients : Array ℕ := #[
    14937224641759813044038270976, 76946765462338516866117402624, 282490537920495506325594177536, 76936560465262523710229708800, 78570733541985157065474048, 58510120722754904197693440,
    61853556192626613008990208, 80242451276921011471122432, 1074914503563754382831910912, 1944207725730398673769070592, 58510120722754904197693440, 1074914503563754382831910912,
    63525273927562467414638592, 63525273927562467414638592, 61853556192626613008990208, 61853556192626613008990208, 1944207725730398673769070592, 61853556192626613008990208,
    78570733541985157065474048, 80242451276921011471122432, 2029743949834616557524746240, 1511511452004501691773747200, 1597883534976187502732247040, 2072929991320459463003996160,
    27768624675396988223157698560, 50225366248035299072367656960, 1511511452004501691773747200, 27768624675396988223157698560, 1641069576462030408211496960, 1641069576462030408211496960,
    1597883534976187502732247040, 1597883534976187502732247040, 50225366248035299072367656960, 1597883534976187502732247040, 2029743949834616557524746240, 2072929991320459463003996160,
    152095904421557240718163968, 15628199453941363133110026240, 1644479125062662292055785472, 151316829225587465868892176384, 1040809572824469805098598400, 62448574369468188305915904,
    1644479125062662292055785472, 1634071029334417594004799488, 1040809572824469805098598400, 25218815949536903377539039232, 1613254837877928197902827520, 15628199453941363133110026240,
    1644479125062662292055785472, 62448574369468188305915904, 1613254837877928197902827520, 62448574369468188305915904, 1644479125062662292055785472, 1644479125062662292055785472,
    152095904421557240718163968, 78570733541985157065474048, 58510120722754904197693440, 61853556192626613008990208, 80242451276921011471122432, 1074914503563754382831910912,
    1944207725730398673769070592, 58510120722754904197693440, 1074914503563754382831910912, 63525273927562467414638592
  ]
def negativeScales : Array ℕ := #[
    32, 30, 32, 29, 13, 12,
    12, 9, 16, 17, 12, 16,
    11, 11, 12, 12, 17, 12,
    13, 9, 18, 18, 18, 14,
    22, 23, 18, 22, 17, 17,
    18, 18, 23, 18, 18, 14,
    23, 28, 15, 32, 13, 10,
    15, 16, 13, 20, 16, 28,
    15, 10, 16, 10, 15, 15,
    23, 13, 12, 12, 9, 16,
    17, 12, 16, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32592898775023392, 30957847351375042, 32834117297974361, 29957656002487406, 13022194401760635, 12596888567033151,
    12677058915753742, 9052568050804154, 16796280478009686, 17651240931578205, 12596888567033151, 16796280478009686,
    11715533063630459, 11715533063630459, 12677058915753742, 12677058915753742, 17651240931578205, 12677058915753742,
    13022194401760635, 9052568050804154, 18713356306412515, 18288050471581046, 18368220820265031, 14743729955553198,
    22487442381964204, 23342402836109298, 18288050471581046, 22487442381964204, 17406694968079673, 17406694968079673,
    18368220820265031, 18368220820265031, 23342402836109298, 18368220820265031, 18713356306412515, 14743729955553198,
    23975111788166332, 28658138229931413, 15409689256748271, 32933487210406575, 13749764698569610, 10690871009350625,
    15409689256748271, 16400529257462792, 13749764698569610, 20348487198022505, 16382032913845399, 28658138229931413,
    15409689256748271, 10690871009350625, 16382032913845399, 10690871009350625, 15409689256748271, 15409689256748271,
    23975111788166332, 13022194401760635, 12596888567033151, 12677058915753742, 9052568050804154, 16796280478009686,
    17651240931578205, 12596888567033151, 16796280478009686, 11715533063630459
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
noncomputable def negativeCeiling : ℝ := 303764747 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14937224641759813044038270976, coefficient := (-14937224641759813044038270976) }, { argument := 76946765462338516866117402624, coefficient := (-76946765462338516866117402624) }, { argument := 282490537920495506325594177536, coefficient := (-282490537920495506325594177536) }, { argument := 76936560465262523710229708800, coefficient := (-76936560465262523710229708800) }, { argument := 78570733541985157065474048, coefficient := (-78570733541985157065474048) }, { argument := 58510120722754904197693440, coefficient := (-58510120722754904197693440) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 80242451276921011471122432, coefficient := (-80242451276921011471122432) }, { argument := 1074914503563754382831910912, coefficient := (-1074914503563754382831910912) }, { argument := 1944207725730398673769070592, coefficient := (-1944207725730398673769070592) }, { argument := 58510120722754904197693440, coefficient := (-58510120722754904197693440) }, { argument := 1074914503563754382831910912, coefficient := (-1074914503563754382831910912) }, { argument := 63525273927562467414638592, coefficient := (-63525273927562467414638592) }, { argument := 63525273927562467414638592, coefficient := (-63525273927562467414638592) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 1944207725730398673769070592, coefficient := (-1944207725730398673769070592) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 78570733541985157065474048, coefficient := (-78570733541985157065474048) }, { argument := 80242451276921011471122432, coefficient := (-80242451276921011471122432) }, { argument := 2029743949834616557524746240, coefficient := (-2029743949834616557524746240) }, { argument := 1511511452004501691773747200, coefficient := (-1511511452004501691773747200) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 2072929991320459463003996160, coefficient := (-2072929991320459463003996160) }, { argument := 27768624675396988223157698560, coefficient := (-27768624675396988223157698560) }, { argument := 50225366248035299072367656960, coefficient := (-50225366248035299072367656960) }, { argument := 1511511452004501691773747200, coefficient := (-1511511452004501691773747200) }, { argument := 27768624675396988223157698560, coefficient := (-27768624675396988223157698560) }, { argument := 1641069576462030408211496960, coefficient := (-1641069576462030408211496960) }, { argument := 1641069576462030408211496960, coefficient := (-1641069576462030408211496960) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 50225366248035299072367656960, coefficient := (-50225366248035299072367656960) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 2029743949834616557524746240, coefficient := (-2029743949834616557524746240) }, { argument := 2072929991320459463003996160, coefficient := (-2072929991320459463003996160) }, { argument := 152095904421557240718163968, coefficient := (-152095904421557240718163968) }, { argument := 15628199453941363133110026240, coefficient := (-15628199453941363133110026240) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 151316829225587465868892176384, coefficient := (-151316829225587465868892176384) }, { argument := 1040809572824469805098598400, coefficient := (-1040809572824469805098598400) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 1634071029334417594004799488, coefficient := (-1634071029334417594004799488) }, { argument := 1040809572824469805098598400, coefficient := (-1040809572824469805098598400) }, { argument := 25218815949536903377539039232, coefficient := (-25218815949536903377539039232) }, { argument := 1613254837877928197902827520, coefficient := (-1613254837877928197902827520) }, { argument := 15628199453941363133110026240, coefficient := (-15628199453941363133110026240) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1613254837877928197902827520, coefficient := (-1613254837877928197902827520) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 1644479125062662292055785472, coefficient := (-1644479125062662292055785472) }, { argument := 152095904421557240718163968, coefficient := (-152095904421557240718163968) }, { argument := 78570733541985157065474048, coefficient := (-78570733541985157065474048) }, { argument := 58510120722754904197693440, coefficient := (-58510120722754904197693440) }, { argument := 61853556192626613008990208, coefficient := (-61853556192626613008990208) }, { argument := 80242451276921011471122432, coefficient := (-80242451276921011471122432) }, { argument := 1074914503563754382831910912, coefficient := (-1074914503563754382831910912) }, { argument := 1944207725730398673769070592, coefficient := (-1944207725730398673769070592) }, { argument := 58510120722754904197693440, coefficient := (-58510120722754904197693440) }, { argument := 1074914503563754382831910912, coefficient := (-1074914503563754382831910912) }, { argument := 63525273927562467414638592, coefficient := (-63525273927562467414638592) }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
