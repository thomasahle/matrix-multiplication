import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 16, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

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
def constantNumerator : ℤ := (-1369482113538117416333159530758144)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    27809886915, 295769842187, 13904985367, 43166785, 65733645, 2572483571,
    2572483571, 65733645, 43166785, 27809886915, 295769842187, 13904985367,
    43166785, 2037742995, 79746990701, 79746990701, 2037742995, 40859644943,
    146970927779, 20429829287, 65733645, 2572483571, 2572483571, 65733645,
    81590395107, 293478224871, 40795211163, 8388607, 8388609, 1097506059,
    603091711701, 43329525, 23655458278815, 13711875, 1645425, 43329525,
    86110575, 13711875, 1328954925, 85013625, 2412370984365, 43329525,
    1645425, 85013625, 1645425, 43329525, 43329525, 1097506059,
    7006164232833, 46585881, 135404578767315, 487447389, 21588579, 270809138452785,
    21588579, 42040917, 794232459, 42040917, 487447389, 794232459,
    875771324181, 42040917, 42040917, 46585881
  ]
def negativeCoefficients : Array ℕ := #[
    256500933319904527498157752320, 2727995291772525788569425412096, 256501706413725284628611203072, 796286635379844367054274560, 4850286905388309996141281280, 189815784272237738231746002944,
    189815784272237738231746002944, 4850286905388309996141281280, 796286635379844367054274560, 256500933319904527498157752320, 2727995291772525788569425412096, 256501706413725284628611203072,
    796286635379844367054274560, 150358894067037609880379719680, 5884289312439369885184126091264, 5884289312439369885184126091264, 150358894067037609880379719680, 94215926650770212492186484736,
    338891886376857845397201092608, 94215958081716271084048744448, 4850286905388309996141281280, 189815784272237738231746002944, 189815784272237738231746002944, 4850286905388309996141281280,
    94067321088229565469328146432, 338357356587619899268814340096, 94067352469599999363095986176, 9903519133691421481781690368, 9903521494874662916604297216, 158167292107176371130728448,
    21728668864694865618762989568, 799288658510399859484262400, 213069426179499097344945684480, 505878897791392316129280000, 30352733867483538967756800, 799288658510399859484262400,
    794229869532485936322969600, 505878897791392316129280000, 12257445693485435819812454400, 784112291576658090000384000, 21728706132531221264156590080, 799288658510399859484262400,
    30352733867483538967756800, 784112291576658090000384000, 30352733867483538967756800, 799288658510399859484262400, 799288658510399859484262400, 158167292107176371130728448,
    7888239657070798944224673792, 107419728031911050018291712, 304904005240369404303240069120, 1123977154285118059947491328, 99559747932015119529148416, 304903983756121896417849507840,
    99559747932015119529148416, 96939754565383142699433984, 3662750726551503607940775936, 96939754565383142699433984, 1123977154285118059947491328, 3662750726551503607940775936,
    7888246818486634906021527552, 96939754565383142699433984, 96939754565383142699433984, 107419728031911050018291712
  ]
def negativeScales : Array ℕ := #[
    34, 38, 33, 25, 25, 31,
    31, 25, 25, 34, 38, 33,
    25, 30, 36, 36, 30, 35,
    37, 34, 25, 31, 31, 25,
    36, 38, 35, 22, 23, 30,
    39, 25, 44, 23, 20, 25,
    26, 23, 30, 26, 41, 25,
    20, 26, 20, 25, 25, 30,
    42, 25, 46, 28, 24, 47,
    24, 25, 29, 25, 28, 29,
    39, 25, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34694878827117496, 38105684001048099, 33694883175393847, 25363418311162450, 25970128665027614, 31260514717456327,
    31260514717456327, 25970128665027614, 25363418311162450, 34694878827117496, 38105684001048099, 33694883175393847,
    25363418311162450, 30924324967540876, 36214711027843202, 36214711027843202, 30924324967540876, 35249957616449446,
    37096739848502321, 34249958097740285, 25970128665027614, 31260514717456327, 31260514717456327, 25970128665027614,
    36247680275738380, 38094462507791255, 35247680757029219, 22999999851693669, 23000000171982641, 30031581758453158,
    39133586452114240, 25368847085360887, 44427238344085982, 23708922527047674, 20650028837926260, 25368847085360887,
    26359687086075410, 23708922527047674, 30307645026635128, 26341190742458020, 41133588926544539, 25368847085360887,
    20650028837926260, 26341190742458020, 20650028837926260, 25368847085360887, 25368847085360887, 30031581758453158,
    42671761945711227, 25473389441029040, 46944269863008359, 28860671276030903, 24363764949854435, 47944269761352681,
    24363764949854435, 25325290802039798, 29564986081788365, 25325290802039798, 28860671276030903, 29564986081788365,
    39671763255475494, 25325290802039798, 25325290802039798, 25473389441029040
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
noncomputable def negativeCeiling : ℝ := 9432686443 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 256500933319904527498157752320, coefficient := (-256500933319904527498157752320) }, { argument := 2727995291772525788569425412096, coefficient := (-2727995291772525788569425412096) }, { argument := 256501706413725284628611203072, coefficient := (-256501706413725284628611203072) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 4850286905388309996141281280, coefficient := (-4850286905388309996141281280) }, { argument := 189815784272237738231746002944, coefficient := (-189815784272237738231746002944) }, { argument := 189815784272237738231746002944, coefficient := (-189815784272237738231746002944) }, { argument := 4850286905388309996141281280, coefficient := (-4850286905388309996141281280) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 256500933319904527498157752320, coefficient := (-256500933319904527498157752320) }, { argument := 2727995291772525788569425412096, coefficient := (-2727995291772525788569425412096) }, { argument := 256501706413725284628611203072, coefficient := (-256501706413725284628611203072) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 150358894067037609880379719680, coefficient := (-150358894067037609880379719680) }, { argument := 5884289312439369885184126091264, coefficient := (-5884289312439369885184126091264) }, { argument := 5884289312439369885184126091264, coefficient := (-5884289312439369885184126091264) }, { argument := 150358894067037609880379719680, coefficient := (-150358894067037609880379719680) }, { argument := 94215926650770212492186484736, coefficient := (-94215926650770212492186484736) }, { argument := 338891886376857845397201092608, coefficient := (-338891886376857845397201092608) }, { argument := 94215958081716271084048744448, coefficient := (-94215958081716271084048744448) }, { argument := 4850286905388309996141281280, coefficient := (-4850286905388309996141281280) }, { argument := 189815784272237738231746002944, coefficient := (-189815784272237738231746002944) }, { argument := 189815784272237738231746002944, coefficient := (-189815784272237738231746002944) }, { argument := 4850286905388309996141281280, coefficient := (-4850286905388309996141281280) }, { argument := 94067321088229565469328146432, coefficient := (-94067321088229565469328146432) }, { argument := 338357356587619899268814340096, coefficient := (-338357356587619899268814340096) }, { argument := 94067352469599999363095986176, coefficient := (-94067352469599999363095986176) }, { argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 158167292107176371130728448, coefficient := (-158167292107176371130728448) }, { argument := 21728668864694865618762989568, coefficient := (-21728668864694865618762989568) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 213069426179499097344945684480, coefficient := (-213069426179499097344945684480) }, { argument := 505878897791392316129280000, coefficient := (-505878897791392316129280000) }, { argument := 30352733867483538967756800, coefficient := (-30352733867483538967756800) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 794229869532485936322969600, coefficient := (-794229869532485936322969600) }, { argument := 505878897791392316129280000, coefficient := (-505878897791392316129280000) }, { argument := 12257445693485435819812454400, coefficient := (-12257445693485435819812454400) }, { argument := 784112291576658090000384000, coefficient := (-784112291576658090000384000) }, { argument := 21728706132531221264156590080, coefficient := (-21728706132531221264156590080) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 30352733867483538967756800, coefficient := (-30352733867483538967756800) }, { argument := 784112291576658090000384000, coefficient := (-784112291576658090000384000) }, { argument := 30352733867483538967756800, coefficient := (-30352733867483538967756800) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 158167292107176371130728448, coefficient := (-158167292107176371130728448) }, { argument := 7888239657070798944224673792, coefficient := (-7888239657070798944224673792) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }, { argument := 304904005240369404303240069120, coefficient := (-304904005240369404303240069120) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 304903983756121896417849507840, coefficient := (-304903983756121896417849507840) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 7888246818486634906021527552, coefficient := (-7888246818486634906021527552) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }] }

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
def constantNumerator : ℤ := 63161953745239940826725597881303040
def positiveArguments : Array ℕ := #[
    6781, 1, 1, 1, 1, 1333,
    32293, 24467, 13631, 1333, 13631, 27219,
    1333, 32293, 1333, 3249, 9747, 20577,
    53067, 44403, 1242201, 37905, 44403, 40071,
    20577, 20577, 40071, 1242201, 40071, 3249,
    53067, 3189, 47835, 83977, 3189, 26575,
    3189, 83977, 166891, 26575, 2575649, 164765,
    47835, 83977
  ]
def positiveCoefficients : Array ℕ := #[
    537246170009226473221821527228416, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 51567939761481622076266643456,
    1249274927770087038041169330176, 946521216912356224561152262144, 1054647542218688657946872643584, 51567939761481622076266643456, 1054647542218688657946872643584, 1052984060290898928202476945408,
    51567939761481622076266643456, 1249274927770087038041169330176, 51567939761481622076266643456, 1005516796909550128286813650944, 754137597682162596215110238208, 796034130886727184893727473664,
    1026465063511832422626122268672, 13742062891097185086586453229568, 24027661792817791607186984534016, 733189331079880301875801620480, 13742062891097185086586453229568, 775085864284444890554418855936,
    796034130886727184893727473664, 796034130886727184893727473664, 775085864284444890554418855936, 24027661792817791607186984534016, 775085864284444890554418855936, 1005516796909550128286813650944,
    1026465063511832422626122268672, 246736924080067356040831696896, 3701053861201010340612475453440, 6497405667441773709075234684928, 246736924080067356040831696896, 4112282068001122600680528281600,
    246736924080067356040831696896, 6497405667441773709075234684928, 6456282846761762483068429402112, 4112282068001122600680528281600, 99640594507667200614489200263168, 6374037205401740031054818836480,
    3701053861201010340612475453440, 6497405667441773709075234684928
  ]
def positiveScales : Array ℕ := #[
    12, 0, 0, 0, 0, 10,
    14, 14, 13, 10, 13, 14,
    10, 14, 10, 11, 13, 14,
    15, 15, 20, 15, 15, 15,
    14, 14, 15, 20, 15, 11,
    15, 11, 15, 16, 11, 14,
    11, 16, 17, 14, 21, 17,
    15, 16
  ]
def negativeArguments : Array ℕ := #[
    101217125089, 11716675698689, 3238948283359, 87052665, 3406802567, 3406802567,
    87052665, 96799979029, 348186645937, 48400005661, 8388607, 8388609,
    3995738149, 14372551297, 1997869741, 8388607, 8388609, 1,
    43, 1083
  ]
def negativeCoefficients : Array ℕ := #[
    7293462509349332508479586304, 26383608155318363134332239872, 7293463141003950045142188032, 6423352928757491616511426560, 251377660252422950631231193088, 251377660252422950631231193088,
    6423352928757491616511426560, 111602777468025914166612066304, 401431871717697542418451136512, 111602814699320062435521462272, 9903519133691421481781690368, 9903521494874662916604297216,
    4606772438760057708608487424, 16570423466376329979989327872, 4606773975604423349535506432, 9903519133691421481781690368, 9903521494874662916604297216, 158456325028528675187087900672,
    6813621976226733033044779728896, 85804100002948277613808098213888
  ]
def negativeScales : Array ℕ := #[
    36, 43, 41, 26, 31, 31,
    26, 36, 38, 35, 22, 23,
    31, 33, 30, 22, 23, 0,
    5, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12727282329203763, 0, 0, 0, 0, 10380461065088972,
    14978933851176784, 14578549597008487, 13734603784831575, 10380461065088972, 13734603784831575, 14732326444121002,
    10380461065088972, 14978933851176784, 10380461065088972, 11665780028327515, 13250742529050639, 14328745041051912,
    15695527371719490, 15438369532226408, 20244467203624151, 15210100544553293, 15438369532226408, 15290270893237276,
    14328745041051912, 14328745041051912, 15290270893237276, 20244467203624151, 15290270893237276, 11665780028327515,
    15695527371719490, 11638888382251264, 15545778977860706, 16357706629708207, 11638888382251264, 14697782071301563,
    11638888382251264, 16357706629708207, 17348546630422731, 14697782071301563, 21296504570982450, 17330050286805341,
    15545778977860706, 16357706629708207
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36558662446352340, 43413628534241720, 41558662571297788, 26375385128928030, 31665771195974250, 31665771195974250,
    26375385128928030, 36494287683824534, 38341069915877186, 35494288165115373, 22999999851693669, 23000000171982641,
    31895814900748032, 33742597128940913, 30895815382038907, 22999999851693669, 23000000171982641, 0,
    5426264754702117, 10080817527608328
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 20
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
noncomputable def positiveFloor : ℝ := 68534095547 / 500000000000
noncomputable def negativeCeiling : ℝ := 14220391 / 1250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7293462509349332508479586304, coefficient := (-7293462509349332508479586304) }, { argument := 26383608155318363134332239872, coefficient := (-26383608155318363134332239872) }, { argument := 7293463141003950045142188032, coefficient := (-7293463141003950045142188032) }, { argument := 6423352928757491616511426560, coefficient := (-6423352928757491616511426560) }, { argument := 251377660252422950631231193088, coefficient := (-251377660252422950631231193088) }, { argument := 251377660252422950631231193088, coefficient := (-251377660252422950631231193088) }, { argument := 6423352928757491616511426560, coefficient := (-6423352928757491616511426560) }, { argument := 111602777468025914166612066304, coefficient := (-111602777468025914166612066304) }, { argument := 401431871717697542418451136512, coefficient := (-401431871717697542418451136512) }, { argument := 111602814699320062435521462272, coefficient := (-111602814699320062435521462272) }, { argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 4606772438760057708608487424, coefficient := (-4606772438760057708608487424) }, { argument := 16570423466376329979989327872, coefficient := (-16570423466376329979989327872) }, { argument := 4606773975604423349535506432, coefficient := (-4606773975604423349535506432) }, { argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 537246170009226473221821527228416, coefficient := 537246170009226473221821527228416 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 1249274927770087038041169330176, coefficient := 1249274927770087038041169330176 }, { argument := 946521216912356224561152262144, coefficient := 946521216912356224561152262144 }, { argument := 1054647542218688657946872643584, coefficient := 1054647542218688657946872643584 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 1054647542218688657946872643584, coefficient := 1054647542218688657946872643584 }, { argument := 1052984060290898928202476945408, coefficient := 1052984060290898928202476945408 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 1249274927770087038041169330176, coefficient := 1249274927770087038041169330176 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 6813621976226733033044779728896, coefficient := (-6813621976226733033044779728896) }, { argument := 1005516796909550128286813650944, coefficient := 1005516796909550128286813650944 }, { argument := 754137597682162596215110238208, coefficient := 754137597682162596215110238208 }, { argument := 796034130886727184893727473664, coefficient := 796034130886727184893727473664 }, { argument := 1026465063511832422626122268672, coefficient := 1026465063511832422626122268672 }, { argument := 13742062891097185086586453229568, coefficient := 13742062891097185086586453229568 }, { argument := 24027661792817791607186984534016, coefficient := 24027661792817791607186984534016 }, { argument := 733189331079880301875801620480, coefficient := 733189331079880301875801620480 }, { argument := 13742062891097185086586453229568, coefficient := 13742062891097185086586453229568 }, { argument := 775085864284444890554418855936, coefficient := 775085864284444890554418855936 }, { argument := 796034130886727184893727473664, coefficient := 796034130886727184893727473664 }, { argument := 796034130886727184893727473664, coefficient := 796034130886727184893727473664 }, { argument := 775085864284444890554418855936, coefficient := 775085864284444890554418855936 }, { argument := 24027661792817791607186984534016, coefficient := 24027661792817791607186984534016 }, { argument := 775085864284444890554418855936, coefficient := 775085864284444890554418855936 }, { argument := 1005516796909550128286813650944, coefficient := 1005516796909550128286813650944 }, { argument := 1026465063511832422626122268672, coefficient := 1026465063511832422626122268672 }, { argument := 85804100002948277613808098213888, coefficient := (-85804100002948277613808098213888) }, { argument := 246736924080067356040831696896, coefficient := 246736924080067356040831696896 }, { argument := 3701053861201010340612475453440, coefficient := 3701053861201010340612475453440 }, { argument := 6497405667441773709075234684928, coefficient := 6497405667441773709075234684928 }, { argument := 246736924080067356040831696896, coefficient := 246736924080067356040831696896 }, { argument := 4112282068001122600680528281600, coefficient := 4112282068001122600680528281600 }, { argument := 246736924080067356040831696896, coefficient := 246736924080067356040831696896 }, { argument := 6497405667441773709075234684928, coefficient := 6497405667441773709075234684928 }, { argument := 6456282846761762483068429402112, coefficient := 6456282846761762483068429402112 }, { argument := 4112282068001122600680528281600, coefficient := 4112282068001122600680528281600 }, { argument := 99640594507667200614489200263168, coefficient := 99640594507667200614489200263168 }, { argument := 6374037205401740031054818836480, coefficient := 6374037205401740031054818836480 }, { argument := 3701053861201010340612475453440, coefficient := 3701053861201010340612475453440 }, { argument := 6497405667441773709075234684928, coefficient := 6497405667441773709075234684928 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
