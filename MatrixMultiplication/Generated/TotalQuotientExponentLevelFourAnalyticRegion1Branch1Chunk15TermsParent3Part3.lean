import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9517636726888778767174363498151936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    87, 61211110843, 585, 4264748381, 2343, 2343,
    1677, 87, 27615597807, 276016619139, 552033103371, 27615597807,
    1652906137663, 85785, 71079, 5933114025461, 477945, 413346576499,
    1914231, 1914231, 1370109, 71079, 16417683577, 16417687431,
    105736924227, 5495, 4553, 379543885089, 30615, 26441910183,
    122617, 122617, 87763, 4553, 459538378091, 459538485909,
    751, 664649008497747, 3365489141, 12882342143531357, 35214508329, 1559616919,
    25764684236067715, 1559616919, 3037148737, 57377485599, 3037148737, 35214508329,
    57377485599, 41540747066199, 3037148737, 3037148737, 3365489141, 5359596463178331,
    3045, 2523, 19571079107673811, 16965, 2679571099639657, 67947,
    67947, 48633, 2523, 8647504623462793
  ]
def negativeCoefficients : Array ℕ := #[
    105176546306472738199437312, 1129145696188288726154805772288, 2828886417898232268812451840, 314682887692296619674287734784, 2832513195357076156336570368, 2832513195357076156336570368,
    2027368599493733125982257152, 105176546306472738199437312, 127354466297055934990440726528, 5091607933347694651299933978624, 5091606689050243275332694048768, 127354466297055934990440726528,
    7622684124833272385618525028352, 51853850717820481876084654080, 2685288697887132097154383872, 27361658996953930871832779423744, 72225006356964242613117911040, 7624898510421060071749933072384,
    72317602518960350616468062208, 72317602518960350616468062208, 51761254555824373872734502912, 2685288697887132097154383872, 1211411228912253532136148041728, 1211411513287260172442595753984,
    487625495089172040506784350208, 3321523689391193657505218560, 172007476772043957263663104, 1750337228244552451126204563456, 4626407995937734022953697280, 487767149965815495459474505728,
    4632339288240218297342099456, 4632339288240218297342099456, 3315592397088709383116816384, 172007476772043957263663104, 2119246713173063375857872011264, 2119247210395826510661981044736,
    116211621187915073306155286528, 374164128375327877324093784064, 3880144804179724971976687616, 14504227819316764020703408160768, 40599563926661024706780463104, 3596231769727549974027173888,
    14504227790609131708933556142080, 3596231769727549974027173888, 3501594091576824974710669312, 132303474054713549044473397248, 3501594091576824974710669312, 40599563926661024706780463104,
    132303474054713549044473397248, 374165786016051682665622929408, 3501594091576824974710669312, 3501594091576824974710669312, 3880144804179724971976687616, 12068738317213079888652127961088,
    1840589560363272918490152960, 95316245090240918993240064, 44070152288279137291172606640128, 2563678316220272993611284480, 12067715405849909473740033359872, 2566965083292350266680016896,
    2566965083292350266680016896, 1837302793291195645421420544, 95316245090240918993240064, 9736224649977918969038170488832
  ]
def negativeScales : Array ℕ := #[
    6, 35, 9, 31, 11, 11,
    10, 6, 34, 38, 39, 34,
    40, 16, 16, 42, 18, 38,
    20, 20, 20, 16, 33, 33,
    36, 12, 12, 38, 14, 34,
    16, 16, 16, 12, 38, 38,
    9, 49, 31, 53, 35, 30,
    54, 30, 31, 35, 31, 35,
    35, 45, 31, 31, 31, 52,
    11, 11, 54, 14, 51, 16,
    16, 15, 11, 52
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    6442943495848765, 35833074500151989, 9192292814470767, 31989813499532049, 11194141238863136, 11194141238863136,
    10711666973659367, 6442943495848765, 34684764307325522, 38005964178980333, 39005963826411556, 34684764307325522,
    40588141940371025, 16388437785811811, 16117135763994412, 42431926648125250, 18866485084981325, 38588560981632235,
    20868333509456728, 20868333509456728, 20385859241710034, 16117135763994412, 33934531543941814, 33934531882609980,
    36621688309771453, 12423903765836611, 12152601744019200, 38465475751904655, 14901951067164140, 34622107350842923,
    16903799491708359, 16903799491708359, 16421325221734833, 12152601744019200, 38741394396363454, 38741394734851997,
    9552669097515714, 49239586003803113, 31648169055724972, 53516244432432668, 35035450888586099, 30538544564531076,
    54516244429577200, 30538544564531076, 31500070416715775, 35739765696641504, 31500070416715775, 35035450888586099,
    35739765696641504, 45239592395289023, 31500070416715775, 31500070416715775, 31648169055724972, 52251045804126362,
    11572226512796267, 11300924490976301, 54119572823491531, 14050273809598340, 51250923520283944, 16052122233990708,
    16052122233990708, 15569647968694305, 11300924490976301, 52941205312236727
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
noncomputable def negativeCeiling : ℝ := 50181146171 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 1129145696188288726154805772288, coefficient := (-1129145696188288726154805772288) }, { argument := 2828886417898232268812451840, coefficient := (-2828886417898232268812451840) }, { argument := 314682887692296619674287734784, coefficient := (-314682887692296619674287734784) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 2027368599493733125982257152, coefficient := (-2027368599493733125982257152) }, { argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 127354466297055934990440726528, coefficient := (-127354466297055934990440726528) }, { argument := 5091607933347694651299933978624, coefficient := (-5091607933347694651299933978624) }, { argument := 5091606689050243275332694048768, coefficient := (-5091606689050243275332694048768) }, { argument := 127354466297055934990440726528, coefficient := (-127354466297055934990440726528) }, { argument := 7622684124833272385618525028352, coefficient := (-7622684124833272385618525028352) }, { argument := 51853850717820481876084654080, coefficient := (-51853850717820481876084654080) }, { argument := 2685288697887132097154383872, coefficient := (-2685288697887132097154383872) }, { argument := 27361658996953930871832779423744, coefficient := (-27361658996953930871832779423744) }, { argument := 72225006356964242613117911040, coefficient := (-72225006356964242613117911040) }, { argument := 7624898510421060071749933072384, coefficient := (-7624898510421060071749933072384) }, { argument := 72317602518960350616468062208, coefficient := (-72317602518960350616468062208) }, { argument := 72317602518960350616468062208, coefficient := (-72317602518960350616468062208) }, { argument := 51761254555824373872734502912, coefficient := (-51761254555824373872734502912) }, { argument := 2685288697887132097154383872, coefficient := (-2685288697887132097154383872) }, { argument := 1211411228912253532136148041728, coefficient := (-1211411228912253532136148041728) }, { argument := 1211411513287260172442595753984, coefficient := (-1211411513287260172442595753984) }, { argument := 487625495089172040506784350208, coefficient := (-487625495089172040506784350208) }, { argument := 3321523689391193657505218560, coefficient := (-3321523689391193657505218560) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }, { argument := 1750337228244552451126204563456, coefficient := (-1750337228244552451126204563456) }, { argument := 4626407995937734022953697280, coefficient := (-4626407995937734022953697280) }, { argument := 487767149965815495459474505728, coefficient := (-487767149965815495459474505728) }, { argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 3315592397088709383116816384, coefficient := (-3315592397088709383116816384) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }, { argument := 2119246713173063375857872011264, coefficient := (-2119246713173063375857872011264) }, { argument := 2119247210395826510661981044736, coefficient := (-2119247210395826510661981044736) }, { argument := 116211621187915073306155286528, coefficient := (-116211621187915073306155286528) }, { argument := 374164128375327877324093784064, coefficient := (-374164128375327877324093784064) }, { argument := 3880144804179724971976687616, coefficient := (-3880144804179724971976687616) }, { argument := 14504227819316764020703408160768, coefficient := (-14504227819316764020703408160768) }, { argument := 40599563926661024706780463104, coefficient := (-40599563926661024706780463104) }, { argument := 3596231769727549974027173888, coefficient := (-3596231769727549974027173888) }, { argument := 14504227790609131708933556142080, coefficient := (-14504227790609131708933556142080) }, { argument := 3596231769727549974027173888, coefficient := (-3596231769727549974027173888) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 132303474054713549044473397248, coefficient := (-132303474054713549044473397248) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 40599563926661024706780463104, coefficient := (-40599563926661024706780463104) }, { argument := 132303474054713549044473397248, coefficient := (-132303474054713549044473397248) }, { argument := 374165786016051682665622929408, coefficient := (-374165786016051682665622929408) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 3880144804179724971976687616, coefficient := (-3880144804179724971976687616) }, { argument := 12068738317213079888652127961088, coefficient := (-12068738317213079888652127961088) }, { argument := 1840589560363272918490152960, coefficient := (-1840589560363272918490152960) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 44070152288279137291172606640128, coefficient := (-44070152288279137291172606640128) }, { argument := 2563678316220272993611284480, coefficient := (-2563678316220272993611284480) }, { argument := 12067715405849909473740033359872, coefficient := (-12067715405849909473740033359872) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 1837302793291195645421420544, coefficient := (-1837302793291195645421420544) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 9736224649977918969038170488832, coefficient := (-9736224649977918969038170488832) }] }

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

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1077276137261546338142450853347328)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8647503523714679, 53890915415, 5355, 4437, 193429927165, 29835,
    13476642731, 119493, 119493, 85527, 4437, 16417683577,
    16417687431, 66838411, 14826862901, 14826866379, 317, 87,
    2523, 2233, 145, 87, 145, 4437,
    145, 87, 71079, 4553, 2523, 4437,
    145, 4553, 145, 4437, 145, 87,
    1461769841, 14610321757, 29220636373, 1461769841, 2046397547, 175,
    145, 7343711449, 975, 511748015, 3905, 3905,
    2795, 145, 1461769841, 14610321757, 29220636373, 1461769841,
    105736924227, 5495, 4553, 379543885089, 30615, 26441910183,
    122617, 122617, 87763, 4553
  ]
def negativeCoefficients : Array ℕ := #[
    9736223411771619866086731677696, 497055962279216985707716280320, 3236898882018169615275786240, 167625120675940926505353216, 1784076181304516980223844024320, 4508537728525307678419845120,
    497200358863150313982071406592, 4514317905100340124161409024, 4514317905100340124161409024, 3231118705443137169534222336, 167625120675940926505353216, 1211411228912253532136148041728,
    1211411513287260172442595753984, 315635471874665806217196077056, 68376836337681440076153749504, 68376852377125412166608879616, 98106748113366386785755594752, 6573534144154546137464832,
    95316245090240918993240064, 168720709699966684194930688, 5477945120128788447887360, 105176546306472738199437312, 5477945120128788447887360, 167625120675940926505353216,
    175294243844121230332395520, 105176546306472738199437312, 2685288697887132097154383872, 172007476772043957263663104, 95316245090240918993240064, 167625120675940926505353216,
    5477945120128788447887360, 172007476772043957263663104, 5477945120128788447887360, 167625120675940926505353216, 175294243844121230332395520, 6573534144154546137464832,
    3370611768949262943237701632, 134756433142964736836979654656, 134756400210914879247002632192, 3370611768949262943237701632, 18874685911288006808726142976, 105781009216280052786790400,
    5477945120128788447887360, 67733782825436867051537825792, 147337834265532930667315200, 18880169325867753452056084480, 147526728924847716475863040, 147526728924847716475863040,
    105592114556965266978242560, 5477945120128788447887360, 3370611768949262943237701632, 134756433142964736836979654656, 134756400210914879247002632192, 3370611768949262943237701632,
    487625495089172040506784350208, 3321523689391193657505218560, 172007476772043957263663104, 1750337228244552451126204563456, 4626407995937734022953697280, 487767149965815495459474505728,
    4632339288240218297342099456, 4632339288240218297342099456, 3315592397088709383116816384, 172007476772043957263663104
  ]
def negativeScales : Array ℕ := #[
    52, 35, 12, 12, 37, 14,
    33, 16, 16, 16, 12, 33,
    33, 25, 33, 33, 8, 6,
    11, 11, 7, 6, 7, 12,
    7, 6, 16, 12, 11, 12,
    7, 12, 7, 12, 7, 6,
    30, 33, 34, 30, 30, 7,
    7, 32, 9, 28, 11, 11,
    11, 7, 30, 33, 34, 30,
    36, 12, 12, 38, 14, 34,
    16, 16, 16, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    52941205128761659, 35649323042088436, 12386670859637623, 12115368837820224, 37493020067284943, 14864718158730226,
    33649742089436104, 16866566583203111, 16866566583203111, 16384092315535846, 12115368837820224, 33934531543941814,
    33934531882609980, 25994174121309653, 33787494330986783, 33787494669405831, 8308339030139408, 6442943495848765,
    11300924490976301, 11124767535822474, 7179909090014935, 6442943495848765, 7179909090014935, 12115368837820224,
    7179909090014935, 6442943495848765, 16117135763994412, 12152601744019200, 11300924490976301, 12115368837820224,
    7179909090014935, 12152601744019200, 7179909090014935, 12115368837820224, 7179909090014935, 6442943495848765,
    30445069027528702, 33766268899553436, 34766268546984657, 30445069027528702, 30930439301435900, 7451211111832378,
    7179909090014935, 32773862227482370, 9929258415949272, 28930858367860654, 11931106840579056, 11931106840579056,
    11448632567730597, 7179909090014935, 30445069027528702, 33766268899553436, 34766268546984657, 30445069027528702,
    36621688309771453, 12423903765836611, 12152601744019200, 38465475751904655, 14901951067164140, 34622107350842923,
    16903799491708359, 16903799491708359, 16421325221734833, 12152601744019200
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
noncomputable def negativeCeiling : ℝ := 10082965757 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9736223411771619866086731677696, coefficient := (-9736223411771619866086731677696) }, { argument := 497055962279216985707716280320, coefficient := (-497055962279216985707716280320) }, { argument := 3236898882018169615275786240, coefficient := (-3236898882018169615275786240) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 1784076181304516980223844024320, coefficient := (-1784076181304516980223844024320) }, { argument := 4508537728525307678419845120, coefficient := (-4508537728525307678419845120) }, { argument := 497200358863150313982071406592, coefficient := (-497200358863150313982071406592) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 3231118705443137169534222336, coefficient := (-3231118705443137169534222336) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 1211411228912253532136148041728, coefficient := (-1211411228912253532136148041728) }, { argument := 1211411513287260172442595753984, coefficient := (-1211411513287260172442595753984) }, { argument := 315635471874665806217196077056, coefficient := (-315635471874665806217196077056) }, { argument := 68376836337681440076153749504, coefficient := (-68376836337681440076153749504) }, { argument := 68376852377125412166608879616, coefficient := (-68376852377125412166608879616) }, { argument := 98106748113366386785755594752, coefficient := (-98106748113366386785755594752) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 168720709699966684194930688, coefficient := (-168720709699966684194930688) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 2685288697887132097154383872, coefficient := (-2685288697887132097154383872) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 134756433142964736836979654656, coefficient := (-134756433142964736836979654656) }, { argument := 134756400210914879247002632192, coefficient := (-134756400210914879247002632192) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 18874685911288006808726142976, coefficient := (-18874685911288006808726142976) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 67733782825436867051537825792, coefficient := (-67733782825436867051537825792) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 18880169325867753452056084480, coefficient := (-18880169325867753452056084480) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 134756433142964736836979654656, coefficient := (-134756433142964736836979654656) }, { argument := 134756400210914879247002632192, coefficient := (-134756400210914879247002632192) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 487625495089172040506784350208, coefficient := (-487625495089172040506784350208) }, { argument := 3321523689391193657505218560, coefficient := (-3321523689391193657505218560) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }, { argument := 1750337228244552451126204563456, coefficient := (-1750337228244552451126204563456) }, { argument := 4626407995937734022953697280, coefficient := (-4626407995937734022953697280) }, { argument := 487767149965815495459474505728, coefficient := (-487767149965815495459474505728) }, { argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 3315592397088709383116816384, coefficient := (-3315592397088709383116816384) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
