import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-202602814254494442515334294405120)
def positiveArguments : Array ℕ := #[
    441, 5, 2445, 2675, 2445, 2675,
    3, 501, 13, 539, 807, 25,
    807, 841, 501, 25, 115, 3288333585,
    3288335087, 667978133, 2422080525, 334018863
  ]
def positiveCoefficients : Array ℕ := #[
    34939619668790572878752882098176, 792281625142643375935439503360, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200,
    7427640235712281649394745344, 155051989920493879431115309056, 8046610255354971786844307456, 166812420293704992042656989184, 249754402925825470460898312192, 7737125245533626718119526400,
    249754402925825470460898312192, 260276893259751202797540868096, 155051989920493879431115309056, 7737125245533626718119526400, 18222477378280797646515108577280, 15528716306298581533231058780160,
    15528723399293038803438169751552, 3154437546569042092217040109568, 11437951890071313785752544870400, 3154718966554855742984259895296
  ]
def positiveScales : Array ℕ := #[
    8, 2, 11, 11, 11, 11,
    1, 8, 3, 9, 9, 4,
    9, 9, 8, 4, 6, 31,
    31, 29, 31, 28
  ]
def negativeArguments : Array ℕ := #[
    331786811, 501, 13, 1217902811, 807, 165924469,
    807, 841, 501, 25, 6888231017751041, 22439529075,
    6888234193780223, 22439529075, 168882093, 22439529075, 22439523725, 501,
    13, 6888234185391615, 22439523725, 6888237361422849, 22439523725, 619750809,
    807, 84456797, 22439529075, 22439523725, 807, 841,
    501, 25, 5, 5, 1, 115,
    49, 7
  ]
def negativeCoefficients : Array ℕ := #[
    1566818915724605714153609363456, 77525994960246939715557654528, 4023305127677485893422153728, 5751383414059124252333054099456, 124877201462912735230449156096, 1567112302187086956601800654848,
    124877201462912735230449156096, 130138446629875601398770434048, 77525994960246939715557654528, 3868562622766813359059763200, 3877729330598185083201799585792, 51742031247636178324055654400,
    3877731118543665154829452312576, 51742031247636178324055654400, 1595046271080148659712825491456, 51742031247636178324055654400, 51742018911376079030793011200, 77525994960246939715557654528,
    4023305127677485893422153728, 3877731113821298671959807098880, 51742018911376079030793011200, 3877732901767933916891880357888, 51742018911376079030793011200, 5853380896305894525462147760128,
    124877201462912735230449156096, 1595343789613302413100578766848, 51742031247636178324055654400, 51742018911376079030793011200, 124877201462912735230449156096, 130138446629875601398770434048,
    77525994960246939715557654528, 3868562622766813359059763200, 792281625142643375935439503360, 792281625142643375935439503360, 1267650600228229401496703205376, 18222477378280797646515108577280,
    31057439705591620336669228531712, 17747108403195211620953844875264
  ]
def negativeScales : Array ℕ := #[
    28, 8, 3, 30, 9, 27,
    9, 9, 8, 4, 52, 34,
    52, 34, 27, 34, 34, 8,
    3, 52, 34, 52, 34, 29,
    9, 26, 34, 34, 9, 9,
    8, 4, 2, 2, 0, 6,
    5, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8784634845528344, 2321928094887362, 11255618749839595, 11385323176175871, 11255618749839595, 11385323176175871,
    1584962500720924, 8968666792316714, 3700439718136550, 9074141462752505, 9656424863276222, 4643856189773592,
    9656424863276222, 9715961990248632, 8968666792316714, 4643856189773592, 6845490050846035, 31614709514627474,
    31614710173601814, 29315225634359868, 31173599683959456, 28315354337211783
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28305681297342409, 8968666807433246, 3700439718214233, 30181751864338272, 9656424863302849, 27305951416350320,
    9656424863302849, 9715961990360049, 8968666807433246, 4643856189792934, 52613054952025227, 34385323348158516,
    52613055617223663, 34385323348158516, 27331441122704810, 34385323348158516, 34385323004193215, 8968666807433246,
    3700439718214233, 52613055615466724, 34385323004193215, 52613056280665284, 34385323004193215, 29207113008653376,
    9656424863302849, 26331710198589220, 34385323348158516, 34385323004193215, 9656424863302849, 9715961990360049,
    8968666807433246, 4643856189792934, 2321928094887363, 2321928094887363, 0, 6845490052533228,
    5614709844123661, 2807354922807594
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
noncomputable def positiveFloor : ℝ := 23766929419 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1286779449 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1566818915724605714153609363456, coefficient := (-1566818915724605714153609363456) }, { argument := 77525994960246939715557654528, coefficient := (-77525994960246939715557654528) }, { argument := 4023305127677485893422153728, coefficient := (-4023305127677485893422153728) }, { argument := 5751383414059124252333054099456, coefficient := (-5751383414059124252333054099456) }, { argument := 124877201462912735230449156096, coefficient := (-124877201462912735230449156096) }, { argument := 1567112302187086956601800654848, coefficient := (-1567112302187086956601800654848) }, { argument := 124877201462912735230449156096, coefficient := (-124877201462912735230449156096) }, { argument := 130138446629875601398770434048, coefficient := (-130138446629875601398770434048) }, { argument := 77525994960246939715557654528, coefficient := (-77525994960246939715557654528) }, { argument := 3868562622766813359059763200, coefficient := (-3868562622766813359059763200) }, { argument := 3877729330598185083201799585792, coefficient := (-3877729330598185083201799585792) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 3877731118543665154829452312576, coefficient := (-3877731118543665154829452312576) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 1595046271080148659712825491456, coefficient := (-1595046271080148659712825491456) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 77525994960246939715557654528, coefficient := (-77525994960246939715557654528) }, { argument := 4023305127677485893422153728, coefficient := (-4023305127677485893422153728) }, { argument := 3877731113821298671959807098880, coefficient := (-3877731113821298671959807098880) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 3877732901767933916891880357888, coefficient := (-3877732901767933916891880357888) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 5853380896305894525462147760128, coefficient := (-5853380896305894525462147760128) }, { argument := 124877201462912735230449156096, coefficient := (-124877201462912735230449156096) }, { argument := 1595343789613302413100578766848, coefficient := (-1595343789613302413100578766848) }, { argument := 51742031247636178324055654400, coefficient := (-51742031247636178324055654400) }, { argument := 51742018911376079030793011200, coefficient := (-51742018911376079030793011200) }, { argument := 124877201462912735230449156096, coefficient := (-124877201462912735230449156096) }, { argument := 130138446629875601398770434048, coefficient := (-130138446629875601398770434048) }, { argument := 77525994960246939715557654528, coefficient := (-77525994960246939715557654528) }, { argument := 3868562622766813359059763200, coefficient := (-3868562622766813359059763200) }, { argument := 34939619668790572878752882098176, coefficient := 34939619668790572878752882098176 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 7427640235712281649394745344, coefficient := 7427640235712281649394745344 }, { argument := 155051989920493879431115309056, coefficient := 155051989920493879431115309056 }, { argument := 8046610255354971786844307456, coefficient := 8046610255354971786844307456 }, { argument := 166812420293704992042656989184, coefficient := 166812420293704992042656989184 }, { argument := 249754402925825470460898312192, coefficient := 249754402925825470460898312192 }, { argument := 7737125245533626718119526400, coefficient := 7737125245533626718119526400 }, { argument := 249754402925825470460898312192, coefficient := 249754402925825470460898312192 }, { argument := 260276893259751202797540868096, coefficient := 260276893259751202797540868096 }, { argument := 155051989920493879431115309056, coefficient := 155051989920493879431115309056 }, { argument := 7737125245533626718119526400, coefficient := 7737125245533626718119526400 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 18222477378280797646515108577280, coefficient := 18222477378280797646515108577280 }, { argument := 18222477378280797646515108577280, coefficient := (-18222477378280797646515108577280) }, { argument := 15528716306298581533231058780160, coefficient := 15528716306298581533231058780160 }, { argument := 15528723399293038803438169751552, coefficient := 15528723399293038803438169751552 }, { argument := 31057439705591620336669228531712, coefficient := (-31057439705591620336669228531712) }, { argument := 3154437546569042092217040109568, coefficient := 3154437546569042092217040109568 }, { argument := 11437951890071313785752544870400, coefficient := 11437951890071313785752544870400 }, { argument := 3154718966554855742984259895296, coefficient := 3154718966554855742984259895296 }, { argument := 17747108403195211620953844875264, coefficient := (-17747108403195211620953844875264) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9
