import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-269267266177190782099415587880960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 1, 55116545400447, 47478568809,
    333694577359233, 20603907219, 3967211949, 82287654297, 41335789017, 55116545400447,
    47478568809, 3967211949, 579389594397, 18660058227939, 2446605, 22998087,
    271573155, 19083519, 9330027204105, 271573155, 2446605, 19083519,
    19083519, 19083519, 19083519, 19083519, 289696707063, 22998087,
    28216425, 2362536855, 1181268855, 14107785, 4324833409, 462703417077,
    418506179, 17873351353791, 13796907, 32192783, 418506179, 418506179,
    13796907, 5164642187, 206953605, 462703417077, 418506179, 32192783,
    206953605, 32192783, 418506179, 418506179, 18476036501, 1,
    1, 1, 1, 198147234917221, 86344894615, 1202466208900251,
    37470425965, 7214802515, 149648968295, 75173587495
  ]
def negativeCoefficients : Array ℕ := #[
    9903520314283042199192993792, 9903520314283042199192993792, 9903520314283042199192993792, 9903520314283042199192993792, 15513928332962633402372063232, 109478125975703989285099143168,
    187853346781324611242422173696, 95018750846837424662538878976, 4573883969335341870401716224, 94871206202665316860267855872, 95313840135181640267080925184, 15513928332962633402372063232,
    109478125975703989285099143168, 4573883969335341870401716224, 10437355045714688068338843648, 336149725128231353247885950976, 5776882724410644164027351040, 6787837201182506892732137472,
    80154247801197687775879495680, 180238741001612097917653352448, 336149656318110949022776688640, 80154247801197687775879495680, 5776882724410644164027351040, 5632460656300378059926667264,
    5632460656300378059926667264, 5632460656300378059926667264, 180238741001612097917653352448, 5632460656300378059926667264, 10437423855835092293448105984, 6787837201182506892732137472,
    260250585325010017478246400, 21790556364445826129162403840, 21790564250428917639995719680, 260242699341918506644930560, 155818545033694975373606912, 16670647493848259163938881536,
    1930019094319769700653858816, 160988836993590195638262300672, 1018032049751087314630606848, 74231503627683450025148416, 1930019094319769700653858816, 1930019094319769700653858816,
    1018032049751087314630606848, 23817708163968146965211906048, 1908810093283288714932387840, 16670647493848259163938881536, 1930019094319769700653858816, 74231503627683450025148416,
    1908810093283288714932387840, 74231503627683450025148416, 1930019094319769700653858816, 1930019094319769700653858816, 166417342202374565492948992, 9903520314283042199192993792,
    9903520314283042199192993792, 9903520314283042199192993792, 9903520314283042199192993792, 55773488333605664339028606976, 398195543258581756600605736960, 676928296291097925542385549312,
    345603679054618128370337054720, 16636201942070127297329889280, 345067027379067479102681251840, 346676982405719426905648660480
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 0, 45, 35,
    48, 34, 31, 36, 35, 45,
    35, 31, 39, 44, 21, 24,
    28, 24, 43, 28, 21, 24,
    24, 24, 24, 24, 38, 24,
    24, 31, 30, 23, 32, 38,
    28, 44, 23, 24, 28, 28,
    23, 32, 27, 38, 28, 24,
    27, 24, 28, 28, 34, 0,
    0, 0, 0, 47, 36, 50,
    35, 32, 37, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 0, 45647550699068327, 35466557396000156,
    48245521570890241, 34262198897493885, 31885478333124769, 36259956946707215, 35266672374073193, 45647550699068327,
    35466557396000156, 31885478333124769, 39075742818381987, 44085018721602541, 21222349769008547, 24455010525798878,
    28016765635358653, 24185823892983433, 43085018426281670, 28016765635358653, 21222349769008547, 24185823892983433,
    24185823892983433, 24185823892983433, 24185823892983433, 24185823892983433, 38075752329574411, 24455010525798878,
    24750031875564819, 31137689689187065, 30137690211297030, 23749988159078591, 32009997415720965, 38751296797275994,
    28640673682600610, 44022875406704880, 23717841543215820, 24940233973273646, 28640673682600610, 28640673682600610,
    23717841543215820, 32266021254785741, 27624732138725865, 38751296797275994, 28640673682600610, 24940233973273646,
    27624732138725865, 24940233973273646, 28640673682600610, 28640673682600610, 34104936250344226, 0,
    0, 0, 0, 47493566163510937, 36329391825743395, 50094917775985998,
    35125033327237209, 32748312759726197, 37122791376450539, 36129506803816517
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
noncomputable def negativeCeiling : ℝ := 1041658643 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 15513928332962633402372063232, coefficient := (-15513928332962633402372063232) }, { argument := 109478125975703989285099143168, coefficient := (-109478125975703989285099143168) }, { argument := 187853346781324611242422173696, coefficient := (-187853346781324611242422173696) }, { argument := 95018750846837424662538878976, coefficient := (-95018750846837424662538878976) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 94871206202665316860267855872, coefficient := (-94871206202665316860267855872) }, { argument := 95313840135181640267080925184, coefficient := (-95313840135181640267080925184) }, { argument := 15513928332962633402372063232, coefficient := (-15513928332962633402372063232) }, { argument := 109478125975703989285099143168, coefficient := (-109478125975703989285099143168) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 10437355045714688068338843648, coefficient := (-10437355045714688068338843648) }, { argument := 336149725128231353247885950976, coefficient := (-336149725128231353247885950976) }, { argument := 5776882724410644164027351040, coefficient := (-5776882724410644164027351040) }, { argument := 6787837201182506892732137472, coefficient := (-6787837201182506892732137472) }, { argument := 80154247801197687775879495680, coefficient := (-80154247801197687775879495680) }, { argument := 180238741001612097917653352448, coefficient := (-180238741001612097917653352448) }, { argument := 336149656318110949022776688640, coefficient := (-336149656318110949022776688640) }, { argument := 80154247801197687775879495680, coefficient := (-80154247801197687775879495680) }, { argument := 5776882724410644164027351040, coefficient := (-5776882724410644164027351040) }, { argument := 5632460656300378059926667264, coefficient := (-5632460656300378059926667264) }, { argument := 5632460656300378059926667264, coefficient := (-5632460656300378059926667264) }, { argument := 5632460656300378059926667264, coefficient := (-5632460656300378059926667264) }, { argument := 180238741001612097917653352448, coefficient := (-180238741001612097917653352448) }, { argument := 5632460656300378059926667264, coefficient := (-5632460656300378059926667264) }, { argument := 10437423855835092293448105984, coefficient := (-10437423855835092293448105984) }, { argument := 6787837201182506892732137472, coefficient := (-6787837201182506892732137472) }, { argument := 260250585325010017478246400, coefficient := (-260250585325010017478246400) }, { argument := 21790556364445826129162403840, coefficient := (-21790556364445826129162403840) }, { argument := 21790564250428917639995719680, coefficient := (-21790564250428917639995719680) }, { argument := 260242699341918506644930560, coefficient := (-260242699341918506644930560) }, { argument := 155818545033694975373606912, coefficient := (-155818545033694975373606912) }, { argument := 16670647493848259163938881536, coefficient := (-16670647493848259163938881536) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 160988836993590195638262300672, coefficient := (-160988836993590195638262300672) }, { argument := 1018032049751087314630606848, coefficient := (-1018032049751087314630606848) }, { argument := 74231503627683450025148416, coefficient := (-74231503627683450025148416) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 1018032049751087314630606848, coefficient := (-1018032049751087314630606848) }, { argument := 23817708163968146965211906048, coefficient := (-23817708163968146965211906048) }, { argument := 1908810093283288714932387840, coefficient := (-1908810093283288714932387840) }, { argument := 16670647493848259163938881536, coefficient := (-16670647493848259163938881536) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 74231503627683450025148416, coefficient := (-74231503627683450025148416) }, { argument := 1908810093283288714932387840, coefficient := (-1908810093283288714932387840) }, { argument := 74231503627683450025148416, coefficient := (-74231503627683450025148416) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 166417342202374565492948992, coefficient := (-166417342202374565492948992) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 55773488333605664339028606976, coefficient := (-55773488333605664339028606976) }, { argument := 398195543258581756600605736960, coefficient := (-398195543258581756600605736960) }, { argument := 676928296291097925542385549312, coefficient := (-676928296291097925542385549312) }, { argument := 345603679054618128370337054720, coefficient := (-345603679054618128370337054720) }, { argument := 16636201942070127297329889280, coefficient := (-16636201942070127297329889280) }, { argument := 345067027379067479102681251840, coefficient := (-345067027379067479102681251840) }, { argument := 346676982405719426905648660480, coefficient := (-346676982405719426905648660480) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4468427430520944340820541902422016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    198147234917221, 86344894615, 7214802515, 21190145076195, 652578412696605, 91925235,
    864097209, 10203701085, 717016833, 326289129179895, 10203701085, 91925235,
    717016833, 717016833, 717016833, 717016833, 717016833, 10595149706505,
    864097209, 444037425, 37178869455, 18589441455, 222011985, 463468596469,
    42648146058361, 30905586257, 1564014712553803, 1018865481, 2377352789, 30905586257,
    30905586257, 1018865481, 381395311721, 15282982215, 42648146058361, 30905586257,
    2377352789, 15282982215, 2377352789, 30905586257, 30905586257, 2027659672857,
    13365675, 1119096405, 559548405, 6682635, 416843791, 30782823253,
    320844218695, 30782823253, 416843791, 290090532027, 28216425, 10609283204805,
    444037425, 13365675, 84870171583971, 13365675, 13365675, 1144992825,
    13365675, 444037425, 1144992825, 2324818310685
  ]
def negativeCoefficients : Array ℕ := #[
    55773488333605664339028606976, 398195543258581756600605736960, 16636201942070127297329889280, 381727717876314210277659770880, 11755807585001840135027105464320, 217052324346957805317815009280,
    255036481107675421248432635904, 3011601000314039548784683253760, 6772032519625083525915828289536, 11755804804716950040830395023360, 3011601000314039548784683253760, 217052324346957805317815009280,
    211626016238283860184869634048, 211626016238283860184869634048, 211626016238283860184869634048, 6772032519625083525915828289536, 211626016238283860184869634048, 381730498161204304474370211840,
    255036481107675421248432635904, 2047761184530999874368307200, 171457272446560579279462072320, 171457334496795957219966320640, 2047699134295621933864058880, 16698215986845721425443028992,
    1536561397571816698827084136448, 285053720065417056716540870656, 14087392153318561206347629592576, 150358006188351854092241338368, 10963604617900656027559264256, 285053720065417056716540870656,
    285053720065417056716540870656, 150358006188351854092241338368, 3517750853114981919699729645568, 281921261603159726422952509440, 1536561397571816698827084136448, 285053720065417056716540870656,
    10963604617900656027559264256, 281921261603159726422952509440, 10963604617900656027559264256, 285053720065417056716540870656, 285053720065417056716540870656, 18263534694225934044987654144,
    246553186097377911295180800, 20643684976843414227627540480, 20643692447774764079995944960, 246545715166028058926776320, 1922352682822968232130904064, 283921431207163165726604263424,
    2959265594897981289297147330560, 283921431207163165726604263424, 1922352682822968232130904064, 10451612895524049085463003136, 260250585325010017478246400, 382239711102622876783859466240,
    2047761184530999874368307200, 246553186097377911295180800, 382221273120441853869991919616, 246553186097377911295180800, 246553186097377911295180800, 10560694804504353867143577600,
    246553186097377911295180800, 2047761184530999874368307200, 10560694804504353867143577600, 10470050877705071999330549760
  ]
def negativeScales : Array ℕ := #[
    47, 36, 32, 44, 49, 26,
    29, 33, 29, 48, 33, 26,
    29, 29, 29, 29, 29, 43,
    29, 28, 35, 34, 27, 38,
    45, 34, 50, 29, 31, 34,
    34, 29, 38, 33, 45, 34,
    31, 33, 31, 34, 34, 40,
    23, 30, 29, 22, 28, 34,
    38, 34, 28, 38, 24, 43,
    28, 23, 46, 23, 23, 30,
    23, 28, 30, 41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47493566163510937, 36329391825743395, 32748312759726197, 44268458698545964, 49213144592269233, 26453957623787035,
    29686618380629924, 33248373490137087, 29417431747761880, 48213144251067349, 33248373490137087, 26453957623787035,
    29417431747761880, 29417431747761880, 29417431747761880, 29417431747761880, 29417431747761880, 43268469206267641,
    29686618380629924, 28726106036226496, 35113763849941584, 34113764372051550, 27726062319740353, 38753680632578631,
    45277548261584724, 34847148582716669, 50474175507329582, 29924316448310161, 31146708862935373, 34847148582716669,
    34847148582716669, 29924316448310161, 38472496153278476, 33831207038412152, 45277548261584724, 34847148582716669,
    31146708862935373, 33831207038412152, 31146708862935373, 34847148582716669, 34847148582716669, 40882952669204824,
    23672029363375464, 30059687177185791, 29059687699295757, 22671985646889411, 28634931605203684, 34841406505150601,
    38223082031238806, 34841406505150601, 28634931605203684, 38077712253393416, 24750031875564819, 43270392420249614,
    28726106036226496, 23672029363375464, 46270322827723610, 23672029363375464, 23672029363375464, 30092691411811231,
    23672029363375464, 28726106036226496, 30092691411811231, 41080255109700776
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
noncomputable def negativeCeiling : ℝ := 37366691073 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 55773488333605664339028606976, coefficient := (-55773488333605664339028606976) }, { argument := 398195543258581756600605736960, coefficient := (-398195543258581756600605736960) }, { argument := 16636201942070127297329889280, coefficient := (-16636201942070127297329889280) }, { argument := 381727717876314210277659770880, coefficient := (-381727717876314210277659770880) }, { argument := 11755807585001840135027105464320, coefficient := (-11755807585001840135027105464320) }, { argument := 217052324346957805317815009280, coefficient := (-217052324346957805317815009280) }, { argument := 255036481107675421248432635904, coefficient := (-255036481107675421248432635904) }, { argument := 3011601000314039548784683253760, coefficient := (-3011601000314039548784683253760) }, { argument := 6772032519625083525915828289536, coefficient := (-6772032519625083525915828289536) }, { argument := 11755804804716950040830395023360, coefficient := (-11755804804716950040830395023360) }, { argument := 3011601000314039548784683253760, coefficient := (-3011601000314039548784683253760) }, { argument := 217052324346957805317815009280, coefficient := (-217052324346957805317815009280) }, { argument := 211626016238283860184869634048, coefficient := (-211626016238283860184869634048) }, { argument := 211626016238283860184869634048, coefficient := (-211626016238283860184869634048) }, { argument := 211626016238283860184869634048, coefficient := (-211626016238283860184869634048) }, { argument := 6772032519625083525915828289536, coefficient := (-6772032519625083525915828289536) }, { argument := 211626016238283860184869634048, coefficient := (-211626016238283860184869634048) }, { argument := 381730498161204304474370211840, coefficient := (-381730498161204304474370211840) }, { argument := 255036481107675421248432635904, coefficient := (-255036481107675421248432635904) }, { argument := 2047761184530999874368307200, coefficient := (-2047761184530999874368307200) }, { argument := 171457272446560579279462072320, coefficient := (-171457272446560579279462072320) }, { argument := 171457334496795957219966320640, coefficient := (-171457334496795957219966320640) }, { argument := 2047699134295621933864058880, coefficient := (-2047699134295621933864058880) }, { argument := 16698215986845721425443028992, coefficient := (-16698215986845721425443028992) }, { argument := 1536561397571816698827084136448, coefficient := (-1536561397571816698827084136448) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 14087392153318561206347629592576, coefficient := (-14087392153318561206347629592576) }, { argument := 150358006188351854092241338368, coefficient := (-150358006188351854092241338368) }, { argument := 10963604617900656027559264256, coefficient := (-10963604617900656027559264256) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 150358006188351854092241338368, coefficient := (-150358006188351854092241338368) }, { argument := 3517750853114981919699729645568, coefficient := (-3517750853114981919699729645568) }, { argument := 281921261603159726422952509440, coefficient := (-281921261603159726422952509440) }, { argument := 1536561397571816698827084136448, coefficient := (-1536561397571816698827084136448) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 10963604617900656027559264256, coefficient := (-10963604617900656027559264256) }, { argument := 281921261603159726422952509440, coefficient := (-281921261603159726422952509440) }, { argument := 10963604617900656027559264256, coefficient := (-10963604617900656027559264256) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 18263534694225934044987654144, coefficient := (-18263534694225934044987654144) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 2959265594897981289297147330560, coefficient := (-2959265594897981289297147330560) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 10451612895524049085463003136, coefficient := (-10451612895524049085463003136) }, { argument := 260250585325010017478246400, coefficient := (-260250585325010017478246400) }, { argument := 382239711102622876783859466240, coefficient := (-382239711102622876783859466240) }, { argument := 2047761184530999874368307200, coefficient := (-2047761184530999874368307200) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 382221273120441853869991919616, coefficient := (-382221273120441853869991919616) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 10560694804504353867143577600, coefficient := (-10560694804504353867143577600) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 2047761184530999874368307200, coefficient := (-2047761184530999874368307200) }, { argument := 10560694804504353867143577600, coefficient := (-10560694804504353867143577600) }, { argument := 10470050877705071999330549760, coefficient := (-10470050877705071999330549760) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
