import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10042295515862904026201673695232)
def positiveArguments : Array ℕ := #[
    5, 17, 2445, 2675, 2445, 2675,
    9, 1503, 39, 1617, 2421, 75,
    2421, 2523, 1503, 75, 9, 369098691,
    369098813, 69800769, 254661293, 34901257
  ]
def positiveCoefficients : Array ℕ := #[
    6338253001141147007483516026880, 1346878762742493739090247155712, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200,
    2785365088392105618523029504, 58144496220185204786668240896, 3017478845758114420066615296, 62554657610139372015996370944, 93657901097184551422836867072, 2901421967075110019294822400,
    93657901097184551422836867072, 97603834972406701049077825536, 58144496220185204786668240896, 2901421967075110019294822400, 2852213850513516153367582212096, 1743019287249459972009608871936,
    1743019863378170882106324942848, 659249624008253125346300264448, 2405207909094892401142169337856, 659266105067278340408096063488
  ]
def positiveScales : Array ℕ := #[
    2, 4, 11, 11, 11, 11,
    3, 10, 5, 10, 11, 6,
    11, 11, 10, 6, 3, 28,
    28, 26, 27, 25
  ]
def negativeArguments : Array ℕ := #[
    17156935, 1503, 39, 127915745, 2421, 34321041,
    2421, 2523, 1503, 75, 93524562035, 22439523725,
    182665219, 22439523725, 35781811, 22439523725, 22439529075, 1503,
    39, 182665213, 22439529075, 93524619149, 22439529075, 33342195,
    2421, 35788673, 22439523725, 22439529075, 2421, 2523,
    1503, 75, 17, 5, 3, 9,
    11, 47
  ]
def negativeCoefficients : Array ℕ := #[
    324085339171092465617773527040, 29072248110092602393334120448, 1508739422879057210033307648, 1208130053638600810791216087040, 46828950548592275711418433536, 324153067351189782069428355072,
    46828950548592275711418433536, 48801917486203350524538912768, 29072248110092602393334120448, 1450710983537555009647411200, 431305915116354393170656624640, 51742018911376079030793011200,
    431306053895821745706040819712, 51742018911376079030793011200, 337949649925552765347049766912, 51742018911376079030793011200, 51742031247636178324055654400, 29072248110092602393334120448,
    1508739422879057210033307648, 431306039728722297097105178624, 51742031247636178324055654400, 431306178508189649632489373696, 51742031247636178324055654400, 1259632513066430962366949621760,
    46828950548592275711418433536, 338014459683163668357962530816, 51742018911376079030793011200, 51742031247636178324055654400, 46828950548592275711418433536, 48801917486203350524538912768,
    29072248110092602393334120448, 1450710983537555009647411200, 1346878762742493739090247155712, 792281625142643375935439503360, 475368975085586025561263702016, 2852213850513516153367582212096,
    3486039150627630854115933814784, 3723723638170423866896565665792
  ]
def negativeScales : Array ℕ := #[
    24, 10, 5, 26, 11, 25,
    11, 11, 10, 6, 36, 34,
    27, 34, 25, 34, 34, 10,
    5, 27, 34, 36, 34, 24,
    11, 25, 34, 34, 11, 11,
    10, 6, 4, 2, 1, 3,
    3, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 4087462841250339, 11255618749839595, 11385323176175871, 11255618749839595, 11385323176175871,
    3169925001442312, 10553629293916271, 5285402218862248, 10659103963471994, 11241387363998936, 6228818690495880,
    11241387363998936, 11300924490976300, 10553629293916271, 6228818690495880, 3169925001442312, 28459431380206779,
    28459431857067766, 26056739595007138, 27924004453906886, 25056775661534978
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24032288509866691, 10553629293917849, 5285402218862249, 26930618621386203, 11241387363998937, 25032589976453451,
    11241387363998937, 11300924490976301, 10553629293917849, 6228818690495881, 36444626253687048, 34385323004193215,
    27444626717896812, 34385323004193215, 25092723071573410, 34385323004193215, 34385323348158516, 10553629293917849,
    5285402218862249, 27444626670508642, 34385323348158516, 36444627134718272, 34385323348158516, 24990845768326867,
    11241387363998937, 25092999715598925, 34385323004193215, 34385323348158516, 11241387363998937, 11300924490976301,
    10553629293917849, 6228818690495881, 4087462841250340, 2321928094887363, 1584962500724866, 3169925001442313,
    3459431618637364, 5554588851679165
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 38
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
noncomputable def positiveFloor : ℝ := 586130969 / 200000000000
noncomputable def negativeCeiling : ℝ := 1327554753 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 324085339171092465617773527040, coefficient := (-324085339171092465617773527040) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 1208130053638600810791216087040, coefficient := (-1208130053638600810791216087040) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 324153067351189782069428355072, coefficient := (-324153067351189782069428355072) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 48801917486203350524538912768, coefficient := (-48801917486203350524538912768) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 431305915116354393170656624640, coefficient := (-431305915116354393170656624640) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 431306053895821745706040819712, coefficient := (-431306053895821745706040819712) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 337949649925552765347049766912, coefficient := (-337949649925552765347049766912) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 431306039728722297097105178624, coefficient := (-431306039728722297097105178624) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 431306178508189649632489373696, coefficient := (-431306178508189649632489373696) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 1259632513066430962366949621760, coefficient := (-1259632513066430962366949621760) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 338014459683163668357962530816, coefficient := (-338014459683163668357962530816) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 48801917486203350524538912768, coefficient := (-48801917486203350524538912768) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 6338253001141147007483516026880, coefficient := 6338253001141147007483516026880 }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 3017478845758114420066615296, coefficient := 3017478845758114420066615296 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 97603834972406701049077825536, coefficient := 97603834972406701049077825536 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 2852213850513516153367582212096, coefficient := (-2852213850513516153367582212096) }, { argument := 1743019287249459972009608871936, coefficient := 1743019287249459972009608871936 }, { argument := 1743019863378170882106324942848, coefficient := 1743019863378170882106324942848 }, { argument := 3486039150627630854115933814784, coefficient := (-3486039150627630854115933814784) }, { argument := 659249624008253125346300264448, coefficient := 659249624008253125346300264448 }, { argument := 2405207909094892401142169337856, coefficient := 2405207909094892401142169337856 }, { argument := 659266105067278340408096063488, coefficient := 659266105067278340408096063488 }, { argument := 3723723638170423866896565665792, coefficient := (-3723723638170423866896565665792) }] }

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

end TermShard0


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6
