import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

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
def constantNumerator : ℤ := (-30055922752818374105330344242708480)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    768731, 86777637, 909, 1173, 15705, 3447,
    1388356287, 15705, 891, 57, 909, 111,
    3447, 111, 12299585, 1173, 142408044919653, 1565989000004109,
    81344304995, 127112385531270019, 25711075045, 3053452295, 81302361955, 162244014105,
    25711075045, 2502396442475, 160096531135, 782995953328523, 81302361955, 3053452295,
    160096531135, 3053452295, 81302361955, 81595963235, 142408044919653, 18182508051185407,
    885297303, 355331587749069673, 9264470547, 410314797, 710663228854146911, 410314797,
    799073691, 15098778501, 799116699, 9264470547, 15098778501, 1136413249546797,
    799073691, 799116699, 885297303, 3255, 3675, 1575,
    41475, 3675, 1575, 3675, 3675, 152355,
    945, 41475, 152355, 3255
  ]
def negativeCoefficients : Array ℕ := #[
    58083672139885843756315836416, 6556732870902860650766382661632, 17582617120475166716926623744, 22689119782527360350885511168, 303778879952764019020167905280, 533397414427088225947160150016,
    6556327196010149733894300106752, 303778879952764019020167905280, 17234446484426153514611245056, 17640645559816668917312520192, 17582617120475166716926623744, 17176418045084651314225348608,
    533397414427088225947160150016, 17176418045084651314225348608, 58083147957206245225697116160, 22689119782527360350885511168, 80168602254338763347497844736, 14105174953769601902825730736128,
    187567197012067315962074890240, 143115823028200621198619082489856, 118571405303763823283069255680, 7040781628393259943162019840, 187470482946498145628098396160, 187054612855391103253720596480,
    118571405303763823283069255680, 2885066671581098196269111705600, 184578733558501122827364597760, 14105201134571769839941301829632, 187470482946498145628098396160, 7040781628393259943162019840,
    184578733558501122827364597760, 7040781628393259943162019840, 187470482946498145628098396160, 188147481405482337965933854720, 80168602254338763347497844736, 5117921030248727648498448596992,
    8165426388793149625492045824, 200033900772459610106811411070976, 85449658579464468989504126976, 7568972049915087708280061952, 200033915790840596838771763183616, 7568972049915087708280061952,
    7370153936955733735876067328, 278523302833574937258010607616, 7370550615740294786074017792, 85449658579464468989504126976, 278523302833574937258010607616, 5117950287197849451548809101312,
    7370153936955733735876067328, 7370550615740294786074017792, 8165426388793149625492045824, 245940846427851122729287680, 277675149192735138565324800, 238007270736630118770278400,
    3133762398032296563808665600, 277675149192735138565324800, 238007270736630118770278400, 277675149192735138565324800, 277675149192735138565324800, 11511618327961676744522465280,
    285608724883956142524334080, 3133762398032296563808665600, 11511618327961676744522465280, 245940846427851122729287680
  ]
def negativeScales : Array ℕ := #[
    19, 26, 9, 10, 13, 11,
    30, 13, 9, 5, 9, 6,
    11, 6, 23, 10, 47, 50,
    36, 56, 34, 31, 36, 37,
    34, 41, 37, 49, 36, 31,
    37, 31, 36, 36, 47, 54,
    29, 58, 33, 28, 59, 28,
    29, 33, 29, 33, 33, 50,
    29, 29, 29, 11, 11, 10,
    15, 11, 10, 11, 11, 17,
    9, 15, 17, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19552119322483782, 26370819965567890, 9828136485328458, 10195987298028509, 13938936331176498, 11751125583597746,
    30370730701101301, 13938936331176498, 9799281622158559, 5832890015409720, 9828136485328458, 6794415866926375,
    11751125583597746, 6794415866926375, 23552106302660191, 10195987298028509, 47017023977802159, 50475995502034490,
    36243322293627288, 56818882224026485, 34581670883033983, 31507794159687001, 36242578214227644, 37239374295604281,
    34581670883033983, 41186447505404284, 37220151092598605, 49475998179837391, 36242578214227644, 31507794159687001,
    37220151092598605, 31507794159687001, 36242578214227644, 36247778728951471, 47017023977802159, 54013400733320719,
    29721586785640432, 58301943558054047, 33109061384362570, 28612155941544868, 59301943666370402, 28612155941544868,
    29573753314492584, 33813712789221155, 29573830961597367, 33109061384362570, 33813712789221155, 50013408980563010,
    29573753314492584, 29573830961597367, 29721586785640432, 11668441828086828, 11843528536141147, 10621136113284685,
    15339954360730589, 11843528536141147, 10621136113284685, 11843528536141147, 11843528536141147, 17217077321732868,
    9884170522387776, 15339954360730589, 17217077321732868, 11668441828086828
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
noncomputable def negativeCeiling : ℝ := 411815348197 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 58083672139885843756315836416, coefficient := (-58083672139885843756315836416) }, { argument := 6556732870902860650766382661632, coefficient := (-6556732870902860650766382661632) }, { argument := 17582617120475166716926623744, coefficient := (-17582617120475166716926623744) }, { argument := 22689119782527360350885511168, coefficient := (-22689119782527360350885511168) }, { argument := 303778879952764019020167905280, coefficient := (-303778879952764019020167905280) }, { argument := 533397414427088225947160150016, coefficient := (-533397414427088225947160150016) }, { argument := 6556327196010149733894300106752, coefficient := (-6556327196010149733894300106752) }, { argument := 303778879952764019020167905280, coefficient := (-303778879952764019020167905280) }, { argument := 17234446484426153514611245056, coefficient := (-17234446484426153514611245056) }, { argument := 17640645559816668917312520192, coefficient := (-17640645559816668917312520192) }, { argument := 17582617120475166716926623744, coefficient := (-17582617120475166716926623744) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 533397414427088225947160150016, coefficient := (-533397414427088225947160150016) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 58083147957206245225697116160, coefficient := (-58083147957206245225697116160) }, { argument := 22689119782527360350885511168, coefficient := (-22689119782527360350885511168) }, { argument := 80168602254338763347497844736, coefficient := (-80168602254338763347497844736) }, { argument := 14105174953769601902825730736128, coefficient := (-14105174953769601902825730736128) }, { argument := 187567197012067315962074890240, coefficient := (-187567197012067315962074890240) }, { argument := 143115823028200621198619082489856, coefficient := (-143115823028200621198619082489856) }, { argument := 118571405303763823283069255680, coefficient := (-118571405303763823283069255680) }, { argument := 7040781628393259943162019840, coefficient := (-7040781628393259943162019840) }, { argument := 187470482946498145628098396160, coefficient := (-187470482946498145628098396160) }, { argument := 187054612855391103253720596480, coefficient := (-187054612855391103253720596480) }, { argument := 118571405303763823283069255680, coefficient := (-118571405303763823283069255680) }, { argument := 2885066671581098196269111705600, coefficient := (-2885066671581098196269111705600) }, { argument := 184578733558501122827364597760, coefficient := (-184578733558501122827364597760) }, { argument := 14105201134571769839941301829632, coefficient := (-14105201134571769839941301829632) }, { argument := 187470482946498145628098396160, coefficient := (-187470482946498145628098396160) }, { argument := 7040781628393259943162019840, coefficient := (-7040781628393259943162019840) }, { argument := 184578733558501122827364597760, coefficient := (-184578733558501122827364597760) }, { argument := 7040781628393259943162019840, coefficient := (-7040781628393259943162019840) }, { argument := 187470482946498145628098396160, coefficient := (-187470482946498145628098396160) }, { argument := 188147481405482337965933854720, coefficient := (-188147481405482337965933854720) }, { argument := 80168602254338763347497844736, coefficient := (-80168602254338763347497844736) }, { argument := 5117921030248727648498448596992, coefficient := (-5117921030248727648498448596992) }, { argument := 8165426388793149625492045824, coefficient := (-8165426388793149625492045824) }, { argument := 200033900772459610106811411070976, coefficient := (-200033900772459610106811411070976) }, { argument := 85449658579464468989504126976, coefficient := (-85449658579464468989504126976) }, { argument := 7568972049915087708280061952, coefficient := (-7568972049915087708280061952) }, { argument := 200033915790840596838771763183616, coefficient := (-200033915790840596838771763183616) }, { argument := 7568972049915087708280061952, coefficient := (-7568972049915087708280061952) }, { argument := 7370153936955733735876067328, coefficient := (-7370153936955733735876067328) }, { argument := 278523302833574937258010607616, coefficient := (-278523302833574937258010607616) }, { argument := 7370550615740294786074017792, coefficient := (-7370550615740294786074017792) }, { argument := 85449658579464468989504126976, coefficient := (-85449658579464468989504126976) }, { argument := 278523302833574937258010607616, coefficient := (-278523302833574937258010607616) }, { argument := 5117950287197849451548809101312, coefficient := (-5117950287197849451548809101312) }, { argument := 7370153936955733735876067328, coefficient := (-7370153936955733735876067328) }, { argument := 7370550615740294786074017792, coefficient := (-7370550615740294786074017792) }, { argument := 8165426388793149625492045824, coefficient := (-8165426388793149625492045824) }, { argument := 245940846427851122729287680, coefficient := (-245940846427851122729287680) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 238007270736630118770278400, coefficient := (-238007270736630118770278400) }, { argument := 3133762398032296563808665600, coefficient := (-3133762398032296563808665600) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 238007270736630118770278400, coefficient := (-238007270736630118770278400) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 11511618327961676744522465280, coefficient := (-11511618327961676744522465280) }, { argument := 285608724883956142524334080, coefficient := (-285608724883956142524334080) }, { argument := 3133762398032296563808665600, coefficient := (-3133762398032296563808665600) }, { argument := 11511618327961676744522465280, coefficient := (-11511618327961676744522465280) }, { argument := 245940846427851122729287680, coefficient := (-245940846427851122729287680) }] }

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

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-47108674705145301749762772451721216)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3675, 945, 3675, 1136431307747245, 3255, 2697,
    66439988501153689, 18135, 18181745567530391, 72633, 72633, 51987,
    2697, 2697, 3045, 1305, 34365, 3045,
    1305, 3045, 3045, 126237, 783, 34365,
    126237, 2697, 3045, 783, 3045, 1801070193,
    3675, 3045, 13211837641, 20475, 3602142805, 82005,
    82005, 58695, 3045, 71356791518959, 71356801222929, 142408064025755,
    1565988972576243, 81344358557, 127112381315361917, 25711091995, 3053454329, 81302415517,
    162244120551, 25711091995, 2502398085269, 160096636225, 782995939614325, 81302415517,
    3053454329, 160096636225, 3053454329, 81302415517, 81596016797, 142408064025755,
    66440663580602387, 6494903551, 1298419888627964287, 68004932379
  ]
def negativeCoefficients : Array ℕ := #[
    277675149192735138565324800, 285608724883956142524334080, 277675149192735138565324800, 5118031614102658046072738283520, 245940846427851122729287680, 12736222404299433141338112,
    18701194216018487051862340009984, 342560464667364063801507840, 5117706410179689764034493546496, 342999644750270940806381568, 342999644750270940806381568, 245501666344944245724413952,
    12736222404299433141338112, 12736222404299433141338112, 14379605940338069675704320, 12325376520289774007746560, 162284124183815357768663040, 14379605940338069675704320,
    12325376520289774007746560, 14379605940338069675704320, 14379605940338069675704320, 596137377698015402841341952, 14790451824347728809295872, 162284124183815357768663040,
    596137377698015402841341952, 12736222404299433141338112, 14379605940338069675704320, 14790451824347728809295872, 14379605940338069675704320, 8305970227264417088743145472,
    277675149192735138565324800, 14379605940338069675704320, 30464423463366191567687647232, 386761814947023943001702400, 8305975805098656376668815360, 387257663427725255749140480,
    387257663427725255749140480, 277179300712033825817886720, 14379605940338069675704320, 80340604923784480414725308416, 80340615849483399418343325696, 80168613010117994310333890560,
    14105174706721347708489937453056, 187567320517630575465950347264, 143115818281510081899755321950208, 118571483471841835627294228480, 7040786318477940683815518208, 187470606452061405131973853184,
    187054735579273582634153803776, 118571483471841835627294228480, 2885068565593628435369682796544, 184578854719022041960913305600, 14105200887518741830000495820800, 187470606452061405131973853184,
    7040786318477940683815518208, 184578854719022041960913305600, 7040786318477940683815518208, 187470606452061405131973853184, 188147604911045597469809311744, 80168613010117994310333890560,
    18701384233990587163904281935872, 29952455897181093133344047104, 730945415824417609969953400684544, 313617395836334262333122543616
  ]
def negativeScales : Array ℕ := #[
    11, 9, 11, 50, 11, 11,
    55, 14, 54, 16, 16, 15,
    11, 11, 11, 10, 15, 11,
    10, 11, 11, 16, 9, 15,
    16, 11, 11, 9, 11, 30,
    11, 11, 33, 14, 31, 16,
    16, 15, 11, 46, 46, 47,
    50, 36, 56, 34, 31, 36,
    37, 34, 41, 37, 49, 36,
    31, 37, 31, 36, 36, 47,
    55, 32, 60, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11843528536141147, 9884170522387776, 11843528536141147, 50013431905559047, 11668441828086828, 11397139806235610,
    55882901345013264, 14146489124857643, 54013340232621348, 16148337549250011, 16148337549250011, 15665863283982959,
    11397139806235610, 11397139806235610, 11572226512796267, 10349834091457248, 15068652338913194, 11572226512796267,
    10349834091457248, 11572226512796267, 11572226512796267, 16945775309620080, 9612868497299083, 15068652338913194,
    16945775309620080, 11397139806235610, 11572226512796267, 9612868497299083, 11572226512796267, 30746207262599884,
    11843528536141147, 11572226512796267, 33621112094588297, 14321575831415734, 31746208231434459, 16323424255808103,
    16323424255808103, 15840949991965165, 11572226512796267, 46020115981028361, 46020116177223680, 47017024171360583,
    50475995476766084, 36243323243584465, 56818882176176939, 34581671834128903, 31507795120710934, 36242579164674894,
    37239375242135756, 34581671834128903, 41186448452516396, 37220152039607082, 49475998154568543, 36242579164674894,
    31507795120710934, 37220152039607082, 31507795120710934, 36242579164674894, 36247779675978792, 47017024171360583,
    55882916003788861, 32596660955872863, 60171462711711940, 35984920355883321
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
noncomputable def negativeCeiling : ℝ := 27135081731 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 285608724883956142524334080, coefficient := (-285608724883956142524334080) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 5118031614102658046072738283520, coefficient := (-5118031614102658046072738283520) }, { argument := 245940846427851122729287680, coefficient := (-245940846427851122729287680) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 18701194216018487051862340009984, coefficient := (-18701194216018487051862340009984) }, { argument := 342560464667364063801507840, coefficient := (-342560464667364063801507840) }, { argument := 5117706410179689764034493546496, coefficient := (-5117706410179689764034493546496) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 245501666344944245724413952, coefficient := (-245501666344944245724413952) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 8305970227264417088743145472, coefficient := (-8305970227264417088743145472) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 30464423463366191567687647232, coefficient := (-30464423463366191567687647232) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 8305975805098656376668815360, coefficient := (-8305975805098656376668815360) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 80340604923784480414725308416, coefficient := (-80340604923784480414725308416) }, { argument := 80340615849483399418343325696, coefficient := (-80340615849483399418343325696) }, { argument := 80168613010117994310333890560, coefficient := (-80168613010117994310333890560) }, { argument := 14105174706721347708489937453056, coefficient := (-14105174706721347708489937453056) }, { argument := 187567320517630575465950347264, coefficient := (-187567320517630575465950347264) }, { argument := 143115818281510081899755321950208, coefficient := (-143115818281510081899755321950208) }, { argument := 118571483471841835627294228480, coefficient := (-118571483471841835627294228480) }, { argument := 7040786318477940683815518208, coefficient := (-7040786318477940683815518208) }, { argument := 187470606452061405131973853184, coefficient := (-187470606452061405131973853184) }, { argument := 187054735579273582634153803776, coefficient := (-187054735579273582634153803776) }, { argument := 118571483471841835627294228480, coefficient := (-118571483471841835627294228480) }, { argument := 2885068565593628435369682796544, coefficient := (-2885068565593628435369682796544) }, { argument := 184578854719022041960913305600, coefficient := (-184578854719022041960913305600) }, { argument := 14105200887518741830000495820800, coefficient := (-14105200887518741830000495820800) }, { argument := 187470606452061405131973853184, coefficient := (-187470606452061405131973853184) }, { argument := 7040786318477940683815518208, coefficient := (-7040786318477940683815518208) }, { argument := 184578854719022041960913305600, coefficient := (-184578854719022041960913305600) }, { argument := 7040786318477940683815518208, coefficient := (-7040786318477940683815518208) }, { argument := 187470606452061405131973853184, coefficient := (-187470606452061405131973853184) }, { argument := 188147604911045597469809311744, coefficient := (-188147604911045597469809311744) }, { argument := 80168613010117994310333890560, coefficient := (-80168613010117994310333890560) }, { argument := 18701384233990587163904281935872, coefficient := (-18701384233990587163904281935872) }, { argument := 29952455897181093133344047104, coefficient := (-29952455897181093133344047104) }, { argument := 730945415824417609969953400684544, coefficient := (-730945415824417609969953400684544) }, { argument := 313617395836334262333122543616, coefficient := (-313617395836334262333122543616) }] }

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

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
