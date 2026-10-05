import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1602007057194316231042383998877696)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14640464277, 688290057, 2136735, 7276422009, 1139083055659, 284770868359,
    29106105813, 18550607725, 66492702575, 4638999625, 231733185, 36276530435,
    9069135935, 926946045, 36124867675, 129485789225, 9033841375, 780140265,
    780140823, 8309525, 5353350975, 56935138855, 2676683555, 8309525,
    7091035461, 1110061831311, 277515559611, 28364548977, 36124867675, 129485789225,
    9033841375, 231733185, 36276530435, 9069135935, 926946045, 1135492462325,
    4070053320775, 283955608625, 7876900095, 7876905729, 36124867675, 129485789225,
    9033841375, 16030624155, 16030635621, 6619627780583, 2036825, 64048768518683,
    22987025, 2036825, 128097560232419, 2036825, 2036825, 84440945,
    523755, 22987025, 84440945, 6619693177319, 2036825, 523755,
    2036825, 25219355800951, 41694723, 1081899
  ]
def negativeCoefficients : Array ℕ := #[
    270068897638106145307735621632, 25393421059915918966442164224, 78831607396675557544427520, 67113147286165249826091958272, 2626546700805078197751007674368, 2626547664133253058020425859072,
    67114110614340110095510142976, 42774789139356797201756979200, 153321733396289136567412326400, 42787219420204791152771072000, 2137361378540294580448788480, 83647984102072554068503429120,
    83648014781313791656701460480, 2137392057781532168646819840, 41649136793584249906973900800, 149286950938492054026164633600, 41661239961778349280329728000, 1798880976256368641342177280,
    1798882262916767782583402496, 76641840524545680945971200, 24687973843142125002581606400, 262566983814825419049187409920, 24688048252696032328485437440, 76641840524545680945971200,
    65403258183333014161732927488, 2559628313523420154496204931072, 2559629252308202024695064690688, 65404196968114884360592687104, 41649136793584249906973900800, 149286950938492054026164633600,
    41661239961778349280329728000, 68395564113289426574361231360, 2676735491266321730192109731840, 2676736473002041333014446735360, 68396545849009029396698234880, 1309133678133472503832720179200,
    4692451998418006995471066726400, 1309514110149951897649283072000, 36325790036660863531619450880, 36325816018899891351522902016, 41649136793584249906973900800, 149286950938492054026164633600,
    41661239961778349280329728000, 36964102641138929823708610560, 36964129079934873467923464192, 3726519150745622782091984896, 75145578995866914940518400, 144225005017139956936169488384,
    848071534381926611471564800, 75145578995866914940518400, 144225031132447968845895827456, 75145578995866914940518400, 75145578995866914940518400, 3115321003514368387962634240,
    77292595538605969653104640, 848071534381926611471564800, 3115321003514368387962634240, 3726555965835107887929622528, 75145578995866914940518400, 77292595538605969653104640,
    75145578995866914940518400, 56788940693843440146053070848, 192282971101302834270830592, 9978756983301145091899392
  ]
def negativeScales : Array ℕ := #[
    33, 29, 21, 32, 40, 38,
    34, 34, 35, 32, 27, 35,
    33, 29, 35, 36, 33, 29,
    29, 22, 32, 35, 31, 22,
    32, 40, 38, 34, 35, 36,
    33, 27, 35, 33, 29, 40,
    41, 38, 32, 32, 35, 36,
    33, 33, 33, 42, 20, 45,
    24, 20, 46, 20, 20, 26,
    18, 24, 26, 42, 20, 18,
    20, 44, 25, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33769242254168380, 29358441428109483, 21026976563942232, 32760582071342685, 40051010082901396, 38051010612032869,
    34760602779339121, 34110747399734907, 35952476976498227, 32111166583551751, 27787889417559181, 35078317428897131,
    33078317958028605, 29787910125555707, 35072273251920271, 36914002823416988, 33072692435737115, 29539158295160941,
    29539159327056846, 22986334598453789, 32317795095335792, 35728600269470391, 31317799443612136, 22986334598453789,
    32723349164984993, 40013777176702421, 38013777705833894, 34723369872981362, 35072273251920271, 36914002823416988,
    33072692435737115, 27787889417559181, 35078317428897131, 33078317958028605, 29787910125555707, 40046455267764540,
    41888184837187639, 38046874451581384, 32874980834475251, 32874981866371209, 35072273251920271, 36914002823416988,
    33072692435737115, 33900111551405769, 33900112583301755, 42589887235714655, 20957890613333172, 45864236067586742,
    24454316427550289, 20957890613333172, 46864236328820386, 20957890613333172, 20957890613333172, 26331439388552514,
    18998532609056515, 24454316427550289, 26331439388552514, 42589901488340908, 20957890613333172, 18998532609056515,
    20957890613333172, 44519596657709764, 25313361467941953, 20045134392887837
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
noncomputable def negativeCeiling : ℝ := 11801972719 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 270068897638106145307735621632, coefficient := (-270068897638106145307735621632) }, { argument := 25393421059915918966442164224, coefficient := (-25393421059915918966442164224) }, { argument := 78831607396675557544427520, coefficient := (-78831607396675557544427520) }, { argument := 67113147286165249826091958272, coefficient := (-67113147286165249826091958272) }, { argument := 2626546700805078197751007674368, coefficient := (-2626546700805078197751007674368) }, { argument := 2626547664133253058020425859072, coefficient := (-2626547664133253058020425859072) }, { argument := 67114110614340110095510142976, coefficient := (-67114110614340110095510142976) }, { argument := 42774789139356797201756979200, coefficient := (-42774789139356797201756979200) }, { argument := 153321733396289136567412326400, coefficient := (-153321733396289136567412326400) }, { argument := 42787219420204791152771072000, coefficient := (-42787219420204791152771072000) }, { argument := 2137361378540294580448788480, coefficient := (-2137361378540294580448788480) }, { argument := 83647984102072554068503429120, coefficient := (-83647984102072554068503429120) }, { argument := 83648014781313791656701460480, coefficient := (-83648014781313791656701460480) }, { argument := 2137392057781532168646819840, coefficient := (-2137392057781532168646819840) }, { argument := 41649136793584249906973900800, coefficient := (-41649136793584249906973900800) }, { argument := 149286950938492054026164633600, coefficient := (-149286950938492054026164633600) }, { argument := 41661239961778349280329728000, coefficient := (-41661239961778349280329728000) }, { argument := 1798880976256368641342177280, coefficient := (-1798880976256368641342177280) }, { argument := 1798882262916767782583402496, coefficient := (-1798882262916767782583402496) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 24687973843142125002581606400, coefficient := (-24687973843142125002581606400) }, { argument := 262566983814825419049187409920, coefficient := (-262566983814825419049187409920) }, { argument := 24688048252696032328485437440, coefficient := (-24688048252696032328485437440) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 65403258183333014161732927488, coefficient := (-65403258183333014161732927488) }, { argument := 2559628313523420154496204931072, coefficient := (-2559628313523420154496204931072) }, { argument := 2559629252308202024695064690688, coefficient := (-2559629252308202024695064690688) }, { argument := 65404196968114884360592687104, coefficient := (-65404196968114884360592687104) }, { argument := 41649136793584249906973900800, coefficient := (-41649136793584249906973900800) }, { argument := 149286950938492054026164633600, coefficient := (-149286950938492054026164633600) }, { argument := 41661239961778349280329728000, coefficient := (-41661239961778349280329728000) }, { argument := 68395564113289426574361231360, coefficient := (-68395564113289426574361231360) }, { argument := 2676735491266321730192109731840, coefficient := (-2676735491266321730192109731840) }, { argument := 2676736473002041333014446735360, coefficient := (-2676736473002041333014446735360) }, { argument := 68396545849009029396698234880, coefficient := (-68396545849009029396698234880) }, { argument := 1309133678133472503832720179200, coefficient := (-1309133678133472503832720179200) }, { argument := 4692451998418006995471066726400, coefficient := (-4692451998418006995471066726400) }, { argument := 1309514110149951897649283072000, coefficient := (-1309514110149951897649283072000) }, { argument := 36325790036660863531619450880, coefficient := (-36325790036660863531619450880) }, { argument := 36325816018899891351522902016, coefficient := (-36325816018899891351522902016) }, { argument := 41649136793584249906973900800, coefficient := (-41649136793584249906973900800) }, { argument := 149286950938492054026164633600, coefficient := (-149286950938492054026164633600) }, { argument := 41661239961778349280329728000, coefficient := (-41661239961778349280329728000) }, { argument := 36964102641138929823708610560, coefficient := (-36964102641138929823708610560) }, { argument := 36964129079934873467923464192, coefficient := (-36964129079934873467923464192) }, { argument := 3726519150745622782091984896, coefficient := (-3726519150745622782091984896) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 144225005017139956936169488384, coefficient := (-144225005017139956936169488384) }, { argument := 848071534381926611471564800, coefficient := (-848071534381926611471564800) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 144225031132447968845895827456, coefficient := (-144225031132447968845895827456) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 3115321003514368387962634240, coefficient := (-3115321003514368387962634240) }, { argument := 77292595538605969653104640, coefficient := (-77292595538605969653104640) }, { argument := 848071534381926611471564800, coefficient := (-848071534381926611471564800) }, { argument := 3115321003514368387962634240, coefficient := (-3115321003514368387962634240) }, { argument := 3726555965835107887929622528, coefficient := (-3726555965835107887929622528) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 77292595538605969653104640, coefficient := (-77292595538605969653104640) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 56788940693843440146053070848, coefficient := (-56788940693843440146053070848) }, { argument := 192282971101302834270830592, coefficient := (-192282971101302834270830592) }, { argument := 9978756983301145091899392, coefficient := (-9978756983301145091899392) }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 98745791054467267180359292859449344
def positiveArguments : Array ℕ := #[
    9939, 21, 3507, 91, 3773, 5649,
    175, 5649, 5887, 3507, 175, 28303,
    31955, 13695, 360635, 31955, 13695, 31955,
    31955, 1324763, 8217, 360635, 1324763, 28303,
    31955, 8217, 31955, 5319, 154251, 136521,
    8865, 5319, 8865, 271269, 8865, 5319,
    4345623, 278361, 154251, 271269, 8865, 278361,
    8865, 271269, 8865, 5319
  ]
def positiveCoefficients : Array ℕ := #[
    787448707229273251342233322389504, 6499185206248246443220402176, 135670491180432144502225895424, 7040783973435600313488769024, 145960867756991868037324865536, 218535102560097286653286023168,
    6769984589841923378354585600, 218535102560097286653286023168, 227742281602282302447848259584, 135670491180432144502225895424, 6769984589841923378354585600, 547459639560845592507342389248,
    618099593052567604443773665280, 529799651187915089523234570240, 6975695407307548678722588508160, 618099593052567604443773665280, 529799651187915089523234570240, 618099593052567604443773665280,
    618099593052567604443773665280, 25624643129122159829940445380608, 635759581425498107427881484288, 6975695407307548678722588508160, 25624643129122159829940445380608, 547459639560845592507342389248,
    618099593052567604443773665280, 635759581425498107427881484288, 618099593052567604443773665280, 411537691809933605136777609216, 5967296531244037274483275333632, 10562800756454962531843958636544,
    342948076508278004280648007680, 6584603068958937682188441747456, 342948076508278004280648007680, 10494211141153306930987829035008, 10974338448264896136980736245760, 6584603068958937682188441747456,
    168113147104357877698373653364736, 10768569602359929334412347441152, 5967296531244037274483275333632, 10494211141153306930987829035008, 342948076508278004280648007680, 10768569602359929334412347441152,
    342948076508278004280648007680, 10494211141153306930987829035008, 10974338448264896136980736245760, 411537691809933605136777609216
  ]
def positiveScales : Array ℕ := #[
    13, 4, 11, 6, 11, 12,
    7, 12, 12, 11, 7, 14,
    14, 13, 18, 14, 13, 14,
    14, 20, 13, 18, 20, 14,
    14, 13, 14, 12, 17, 17,
    13, 12, 13, 18, 13, 12,
    22, 18, 17, 18, 13, 18,
    13, 18, 13, 12
  ]
def negativeArguments : Array ℕ := #[
    181147497012447, 67160961, 50452709914675, 67160961, 69990543, 41694723,
    2080575, 1146035945, 1146036503, 2929043325, 10498847775, 732473625,
    2390752425, 2390754135, 780140265, 780140823, 7, 913
  ]
def negativeCoefficients : Array ℕ := #[
    203953950011088586652598140928, 309725264827847080352415744, 56804701392890514759693107200, 309725264827847080352415744, 322774408575240885472591872, 192282971101302834270830592,
    9594958637789562588364800, 2642578972085859455221104640, 2642580258746258596462329856, 54031312597082270149587763200, 193669557974259961979889254400, 54047014004469209877184512000,
    44101598127575489271614668800, 44101629671507855314947932160, 1798880976256368641342177280, 1798882262916767782583402496, 1109194275199700726309615304704, 72335312375523340222905626656768
  ]
def negativeScales : Array ℕ := #[
    47, 26, 45, 26, 26, 25,
    20, 30, 30, 31, 33, 29,
    31, 31, 29, 29, 2, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13278884988802170, 4392317422778759, 11776021715228447, 6507794640198673, 11881496384617007, 12463779785335379,
    7451211111832325, 12463779785335379, 12523316912312711, 11776021715228447, 7451211111832325, 14788667360339376,
    14963754066119267, 13741361645581203, 18460179893048682, 14963754066119267, 13741361645581203, 14963754066119267,
    14963754066119267, 20337302854050966, 13004396051426534, 18460179893048682, 20337302854050966, 14788667360339376,
    14963754066119267, 13004396051426534, 14963754066119267, 12376939321619844, 17234920316747416, 17058763361593589,
    13113904915786050, 12376939321619844, 13113904915786050, 18049364663591340, 13113904915786050, 12376939321619844,
    22051131589765528, 18086597569790315, 17234920316747416, 18049364663591340, 13113904915786050, 18086597569790315,
    13113904915786050, 18049364663591340, 13113904915786050, 12376939321619844
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    47364158200056518, 26001119538024525, 45519996994948447, 26001119538024525, 26060656665001889, 25313361467941953,
    20988550884224041, 30094005148395205, 30094005850837079, 31447782387012520, 33289511952907164, 29448201570829365,
    31154817593104060, 31154818624999965, 29539158295160941, 29539159327056846, 2807354922807594, 9834471051268172
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 26183904813 / 125000000000
noncomputable def negativeCeiling : ℝ := 1112706147 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 203953950011088586652598140928, coefficient := (-203953950011088586652598140928) }, { argument := 309725264827847080352415744, coefficient := (-309725264827847080352415744) }, { argument := 56804701392890514759693107200, coefficient := (-56804701392890514759693107200) }, { argument := 309725264827847080352415744, coefficient := (-309725264827847080352415744) }, { argument := 322774408575240885472591872, coefficient := (-322774408575240885472591872) }, { argument := 192282971101302834270830592, coefficient := (-192282971101302834270830592) }, { argument := 9594958637789562588364800, coefficient := (-9594958637789562588364800) }, { argument := 2642578972085859455221104640, coefficient := (-2642578972085859455221104640) }, { argument := 2642580258746258596462329856, coefficient := (-2642580258746258596462329856) }, { argument := 54031312597082270149587763200, coefficient := (-54031312597082270149587763200) }, { argument := 193669557974259961979889254400, coefficient := (-193669557974259961979889254400) }, { argument := 54047014004469209877184512000, coefficient := (-54047014004469209877184512000) }, { argument := 44101598127575489271614668800, coefficient := (-44101598127575489271614668800) }, { argument := 44101629671507855314947932160, coefficient := (-44101629671507855314947932160) }, { argument := 1798880976256368641342177280, coefficient := (-1798880976256368641342177280) }, { argument := 1798882262916767782583402496, coefficient := (-1798882262916767782583402496) }, { argument := 787448707229273251342233322389504, coefficient := 787448707229273251342233322389504 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 227742281602282302447848259584, coefficient := 227742281602282302447848259584 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 547459639560845592507342389248, coefficient := 547459639560845592507342389248 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 529799651187915089523234570240, coefficient := 529799651187915089523234570240 }, { argument := 6975695407307548678722588508160, coefficient := 6975695407307548678722588508160 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 529799651187915089523234570240, coefficient := 529799651187915089523234570240 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 25624643129122159829940445380608, coefficient := 25624643129122159829940445380608 }, { argument := 635759581425498107427881484288, coefficient := 635759581425498107427881484288 }, { argument := 6975695407307548678722588508160, coefficient := 6975695407307548678722588508160 }, { argument := 25624643129122159829940445380608, coefficient := 25624643129122159829940445380608 }, { argument := 547459639560845592507342389248, coefficient := 547459639560845592507342389248 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 635759581425498107427881484288, coefficient := 635759581425498107427881484288 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 72335312375523340222905626656768, coefficient := (-72335312375523340222905626656768) }, { argument := 411537691809933605136777609216, coefficient := 411537691809933605136777609216 }, { argument := 5967296531244037274483275333632, coefficient := 5967296531244037274483275333632 }, { argument := 10562800756454962531843958636544, coefficient := 10562800756454962531843958636544 }, { argument := 342948076508278004280648007680, coefficient := 342948076508278004280648007680 }, { argument := 6584603068958937682188441747456, coefficient := 6584603068958937682188441747456 }, { argument := 342948076508278004280648007680, coefficient := 342948076508278004280648007680 }, { argument := 10494211141153306930987829035008, coefficient := 10494211141153306930987829035008 }, { argument := 10974338448264896136980736245760, coefficient := 10974338448264896136980736245760 }, { argument := 6584603068958937682188441747456, coefficient := 6584603068958937682188441747456 }, { argument := 168113147104357877698373653364736, coefficient := 168113147104357877698373653364736 }, { argument := 10768569602359929334412347441152, coefficient := 10768569602359929334412347441152 }, { argument := 5967296531244037274483275333632, coefficient := 5967296531244037274483275333632 }, { argument := 10494211141153306930987829035008, coefficient := 10494211141153306930987829035008 }, { argument := 342948076508278004280648007680, coefficient := 342948076508278004280648007680 }, { argument := 10768569602359929334412347441152, coefficient := 10768569602359929334412347441152 }, { argument := 342948076508278004280648007680, coefficient := 342948076508278004280648007680 }, { argument := 10494211141153306930987829035008, coefficient := 10494211141153306930987829035008 }, { argument := 10974338448264896136980736245760, coefficient := 10974338448264896136980736245760 }, { argument := 411537691809933605136777609216, coefficient := 411537691809933605136777609216 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
