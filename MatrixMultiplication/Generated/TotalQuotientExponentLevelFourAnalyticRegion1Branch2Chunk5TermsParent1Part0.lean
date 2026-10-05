import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-543585103741190557960664659263488)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    255641, 17231965, 459, 141079055, 471, 15,
    459, 261, 471, 7353, 9, 8615985,
    459, 15, 9, 15, 231, 261,
    255641, 41286797054585, 1175, 371571572094315, 29075, 925,
    371571743590605, 475, 475, 16075, 875, 29075,
    16075, 41286605091095, 925, 875, 1175, 16861695426421,
    3178959255, 1037344599, 497537381713895, 10473834177, 134893521228913, 20981131083,
    9403026849, 3178959255, 1037344599, 186314869, 6752112523, 54016920035,
    1490499101, 813222135, 1378301705, 813222135, 164137638457075, 100323391,
    164106694005005, 50654443, 265367223, 449761609, 265367223, 1175,
    1175, 255641, 41278839909767, 1175
  ]
def negativeCoefficients : Array ℕ := #[
    1207230490047278972074459136, 81375653949982825884826992640, 17756702438499673318084313088, 666227000766923234933504737280, 18220929953231690921171484672, 580284393415022003858964480,
    17756702438499673318084313088, 10096948445421382867145981952, 18220929953231690921171484672, 284455409652043786291664388096, 11141460353568422474092118016, 81375677561815240233053061120,
    17756702438499673318084313088, 580284393415022003858964480, 11141460353568422474092118016, 580284393415022003858964480, 17872759317182677718856105984, 10096948445421382867145981952,
    1207230490047278972074459136, 46484800957587574450332631040, 22727805408755028484476108800, 836704796812713211997580165120, 562392291284725492073313075200, 17892102130296511785651404800,
    836705182988027081708839895040, 18375672458142363455533875200, 18375672458142363455533875200, 310935720804882623734428467200, 16924961474604808445886464000, 562392291284725492073313075200,
    310935720804882623734428467200, 46484584825912066265348833280, 17892102130296511785651404800, 16924961474604808445886464000, 22727805408755028484476108800, 303753300957057649014697099264,
    117282895595470762583166812160, 4783907583499465315892330496, 1120354583444794876246318120960, 96604069266795654443503190016, 303753205970613339228339175424, 96758388866263379131112620032,
    86727614900861274436499668992, 117282895595470762583166812160, 4783907583499465315892330496, 3436902705569721453383778304, 124554491668670298531108487168, 124554537441959874432147128320,
    3436856932280145552345137152, 120010404795365431480449761280, 406802860935880330673892884480, 120010404795365431480449761280, 46200637962047260250551091200, 3701279836767392334413299712,
    46191927873121532989700833280, 3737638184869233123552919552, 4895161248232011020913082368, 16593274590805645066961420288, 4895161248232011020913082368, 22727805408755028484476108800,
    22727805408755028484476108800, 1207230490047278972074459136, 46475842008978254982029508608, 22727805408755028484476108800
  ]
def negativeScales : Array ℕ := #[
    17, 24, 8, 27, 8, 3,
    8, 8, 8, 12, 3, 23,
    8, 3, 3, 3, 7, 8,
    17, 45, 10, 48, 14, 9,
    48, 8, 8, 13, 9, 14,
    13, 45, 9, 9, 10, 43,
    31, 29, 48, 33, 46, 34,
    33, 31, 29, 27, 32, 35,
    30, 29, 30, 29, 47, 26,
    47, 25, 27, 28, 27, 10,
    10, 17, 45, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17963759723507909, 24038583888938322, 8842350344909532, 27071928576299917, 8879583252627603, 3906890600547867,
    8842350344909532, 8027905996569885, 8879583252627603, 12844117271135484, 3169925001442313, 23038584307548397,
    8842350344909532, 3906890600547867, 3169925001442313, 3906890600547867, 7851749043206919, 8027905996569885,
    17963759723507909, 45230745735055352, 10198445041452363, 48400633457787882, 14827491572368013, 9853309557248504,
    48400634123653649, 8891783706984896, 8891783706984896, 13972531132277330, 9773139207089529, 14827491572368013,
    13972531132277330, 45230739027210747, 9853309557248504, 9773139207089529, 10198445041452363, 43938814847255530,
    31565907379433729, 29950248091955322, 48821798253848706, 33286070618033261, 46938814396111416, 34288373403902682,
    33130478091321569, 31565907379433729, 29950248091955322, 27473167573349391, 32652691800563269, 35652692330747969,
    30473148359148908, 29599074243372301, 30360244577053537, 29599074243372301, 47221899430096294, 26580082777269022,
    47221627416822878, 25594185480388788, 27983414963552446, 28744585279309155, 27983414963552446, 10198445041452363,
    10198445041452363, 17963759723507909, 45230467659724593, 10198445041452363
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
noncomputable def negativeCeiling : ℝ := 1651886907 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1207230490047278972074459136, coefficient := (-1207230490047278972074459136) }, { argument := 81375653949982825884826992640, coefficient := (-81375653949982825884826992640) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 666227000766923234933504737280, coefficient := (-666227000766923234933504737280) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 10096948445421382867145981952, coefficient := (-10096948445421382867145981952) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 284455409652043786291664388096, coefficient := (-284455409652043786291664388096) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 81375677561815240233053061120, coefficient := (-81375677561815240233053061120) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 17872759317182677718856105984, coefficient := (-17872759317182677718856105984) }, { argument := 10096948445421382867145981952, coefficient := (-10096948445421382867145981952) }, { argument := 1207230490047278972074459136, coefficient := (-1207230490047278972074459136) }, { argument := 46484800957587574450332631040, coefficient := (-46484800957587574450332631040) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 836704796812713211997580165120, coefficient := (-836704796812713211997580165120) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 836705182988027081708839895040, coefficient := (-836705182988027081708839895040) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 46484584825912066265348833280, coefficient := (-46484584825912066265348833280) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 303753300957057649014697099264, coefficient := (-303753300957057649014697099264) }, { argument := 117282895595470762583166812160, coefficient := (-117282895595470762583166812160) }, { argument := 4783907583499465315892330496, coefficient := (-4783907583499465315892330496) }, { argument := 1120354583444794876246318120960, coefficient := (-1120354583444794876246318120960) }, { argument := 96604069266795654443503190016, coefficient := (-96604069266795654443503190016) }, { argument := 303753205970613339228339175424, coefficient := (-303753205970613339228339175424) }, { argument := 96758388866263379131112620032, coefficient := (-96758388866263379131112620032) }, { argument := 86727614900861274436499668992, coefficient := (-86727614900861274436499668992) }, { argument := 117282895595470762583166812160, coefficient := (-117282895595470762583166812160) }, { argument := 4783907583499465315892330496, coefficient := (-4783907583499465315892330496) }, { argument := 3436902705569721453383778304, coefficient := (-3436902705569721453383778304) }, { argument := 124554491668670298531108487168, coefficient := (-124554491668670298531108487168) }, { argument := 124554537441959874432147128320, coefficient := (-124554537441959874432147128320) }, { argument := 3436856932280145552345137152, coefficient := (-3436856932280145552345137152) }, { argument := 120010404795365431480449761280, coefficient := (-120010404795365431480449761280) }, { argument := 406802860935880330673892884480, coefficient := (-406802860935880330673892884480) }, { argument := 120010404795365431480449761280, coefficient := (-120010404795365431480449761280) }, { argument := 46200637962047260250551091200, coefficient := (-46200637962047260250551091200) }, { argument := 3701279836767392334413299712, coefficient := (-3701279836767392334413299712) }, { argument := 46191927873121532989700833280, coefficient := (-46191927873121532989700833280) }, { argument := 3737638184869233123552919552, coefficient := (-3737638184869233123552919552) }, { argument := 4895161248232011020913082368, coefficient := (-4895161248232011020913082368) }, { argument := 16593274590805645066961420288, coefficient := (-16593274590805645066961420288) }, { argument := 4895161248232011020913082368, coefficient := (-4895161248232011020913082368) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 1207230490047278972074459136, coefficient := (-1207230490047278972074459136) }, { argument := 46475842008978254982029508608, coefficient := (-46475842008978254982029508608) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1227472073292191540511621641142272)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    371432331979413, 29075, 925, 371432503407411, 475, 475,
    16075, 875, 29075, 16075, 41278648014569, 925,
    875, 1175, 498385131802599, 5387906665, 1758159017, 14608459412213389,
    17751734591, 3987079900623419, 35560183989, 15936860767, 5387906665, 1758159017,
    1469208104683225, 3635752897, 1468666615347495, 1835733781, 2679352929, 4541141407,
    2679352929, 29075, 29075, 17231965, 925, 925,
    459, 134893521228913, 3178959255, 1037344599, 3980297899913787, 10473834177,
    1079147832371773, 20981131083, 9403026849, 3178959255, 1037344599, 1469208780184975,
    29086033865, 1468667290583665, 14685875645, 141079055, 475, 475,
    471, 15, 94072537, 3409219879, 27273769055, 752570273,
    5367266091, 9096791253, 5367266091, 475
  ]
def negativeCoefficients : Array ℕ := #[
    836391255947919375873997799424, 562392291284725492073313075200, 17892102130296511785651404800, 836391641969453332709064572928, 18375672458142363455533875200, 18375672458142363455533875200,
    310935720804882623734428467200, 16924961474604808445886464000, 562392291284725492073313075200, 310935720804882623734428467200, 46475625954192703235142189056, 17892102130296511785651404800,
    16924961474604808445886464000, 22727805408755028484476108800, 1122263546936590195911454359552, 397557341369155777704031682560, 16216154713741880406348660736, 4111915772831327107699582173184,
    327461704864594101108847149056, 1122263222171501501920380452864, 327984806629553516605826138112, 293983191907191509302191849472, 397557341369155777704031682560, 16216154713741880406348660736,
    827090634097635598638723891200, 134135606412414167648886063104, 826785802701308257963018813440, 135453244982280711535417360384, 98850675528814158035212566528, 335077093349817219739285454848,
    98850675528814158035212566528, 562392291284725492073313075200, 562392291284725492073313075200, 81375653949982825884826992640, 17892102130296511785651404800, 17892102130296511785651404800,
    17756702438499673318084313088, 303753205970613339228339175424, 117282895595470762583166812160, 4783907583499465315892330496, 1120354258679706182255244214272, 96604069266795654443503190016,
    303753110984199710214442713088, 96758388866263379131112620032, 86727614900861274436499668992, 117282895595470762583166812160, 4783907583499465315892330496, 827091014371314297153467187200,
    134135655706726018619235368960, 826786182825478707848130068480, 135453294760819594440642396160, 666227000766923234933504737280, 18375672458142363455533875200, 18375672458142363455533875200,
    18220929953231690921171484672, 580284393415022003858964480, 3470664028807145043299139584, 125778013197832089282887548928, 125778059420761051980596510720, 3470617805878182345590177792,
    99008583956176480971371053056, 335612360272101272805961629696, 99008583956176480971371053056, 18375672458142363455533875200
  ]
def negativeScales : Array ℕ := #[
    48, 14, 9, 48, 8, 8,
    13, 9, 14, 13, 45, 9,
    9, 10, 48, 32, 30, 53,
    34, 51, 35, 33, 32, 30,
    50, 31, 50, 30, 31, 32,
    31, 14, 14, 24, 9, 9,
    8, 46, 31, 29, 51, 33,
    49, 34, 33, 31, 29, 50,
    34, 50, 33, 27, 8, 8,
    8, 3, 26, 31, 34, 29,
    32, 33, 32, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48400092731085068, 14827491572368013, 9853309557248504, 48400093396935196, 8891783706984896, 8891783706984896,
    13972531132277330, 9773139207089529, 14827491572368013, 13972531132277330, 45230460952973758, 9853309557248504,
    9773139207089529, 10198445041452363, 48824254358922118, 32327077713118337, 30711418415268740, 53697653559819630,
    34047240951720007, 51824253941429220, 35049543737589428, 33891648428765684, 32327077713118337, 30711418415268740,
    50383960182942175, 31759607004733990, 50383428367216425, 30773709707949477, 31319237481968461, 32080407815655207,
    31319237481968461, 14827491572368013, 14827491572368013, 24038583888938322, 9853309557248504, 9853309557248504,
    8842350344909532, 46938814396111416, 31565907379433729, 29950248091955322, 51821797835644446, 33286070618033261,
    49938813944967307, 34288373403902682, 33130478091321569, 31565907379433729, 29950248091955322, 50383960846253790,
    34759607534918693, 50383429030511716, 33773710238134181, 27071928576299917, 8891783706984896, 8891783706984896,
    8879583252627603, 3906890600547867, 26487270276467642, 31666794503691118, 34666795033875818, 29487251062267159,
    32321540267837881, 33082710601524627, 32321540267837881, 8891783706984896
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
noncomputable def negativeCeiling : ℝ := 2625457487 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 836391255947919375873997799424, coefficient := (-836391255947919375873997799424) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 836391641969453332709064572928, coefficient := (-836391641969453332709064572928) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 46475625954192703235142189056, coefficient := (-46475625954192703235142189056) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 1122263546936590195911454359552, coefficient := (-1122263546936590195911454359552) }, { argument := 397557341369155777704031682560, coefficient := (-397557341369155777704031682560) }, { argument := 16216154713741880406348660736, coefficient := (-16216154713741880406348660736) }, { argument := 4111915772831327107699582173184, coefficient := (-4111915772831327107699582173184) }, { argument := 327461704864594101108847149056, coefficient := (-327461704864594101108847149056) }, { argument := 1122263222171501501920380452864, coefficient := (-1122263222171501501920380452864) }, { argument := 327984806629553516605826138112, coefficient := (-327984806629553516605826138112) }, { argument := 293983191907191509302191849472, coefficient := (-293983191907191509302191849472) }, { argument := 397557341369155777704031682560, coefficient := (-397557341369155777704031682560) }, { argument := 16216154713741880406348660736, coefficient := (-16216154713741880406348660736) }, { argument := 827090634097635598638723891200, coefficient := (-827090634097635598638723891200) }, { argument := 134135606412414167648886063104, coefficient := (-134135606412414167648886063104) }, { argument := 826785802701308257963018813440, coefficient := (-826785802701308257963018813440) }, { argument := 135453244982280711535417360384, coefficient := (-135453244982280711535417360384) }, { argument := 98850675528814158035212566528, coefficient := (-98850675528814158035212566528) }, { argument := 335077093349817219739285454848, coefficient := (-335077093349817219739285454848) }, { argument := 98850675528814158035212566528, coefficient := (-98850675528814158035212566528) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 81375653949982825884826992640, coefficient := (-81375653949982825884826992640) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 303753205970613339228339175424, coefficient := (-303753205970613339228339175424) }, { argument := 117282895595470762583166812160, coefficient := (-117282895595470762583166812160) }, { argument := 4783907583499465315892330496, coefficient := (-4783907583499465315892330496) }, { argument := 1120354258679706182255244214272, coefficient := (-1120354258679706182255244214272) }, { argument := 96604069266795654443503190016, coefficient := (-96604069266795654443503190016) }, { argument := 303753110984199710214442713088, coefficient := (-303753110984199710214442713088) }, { argument := 96758388866263379131112620032, coefficient := (-96758388866263379131112620032) }, { argument := 86727614900861274436499668992, coefficient := (-86727614900861274436499668992) }, { argument := 117282895595470762583166812160, coefficient := (-117282895595470762583166812160) }, { argument := 4783907583499465315892330496, coefficient := (-4783907583499465315892330496) }, { argument := 827091014371314297153467187200, coefficient := (-827091014371314297153467187200) }, { argument := 134135655706726018619235368960, coefficient := (-134135655706726018619235368960) }, { argument := 826786182825478707848130068480, coefficient := (-826786182825478707848130068480) }, { argument := 135453294760819594440642396160, coefficient := (-135453294760819594440642396160) }, { argument := 666227000766923234933504737280, coefficient := (-666227000766923234933504737280) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 3470664028807145043299139584, coefficient := (-3470664028807145043299139584) }, { argument := 125778013197832089282887548928, coefficient := (-125778013197832089282887548928) }, { argument := 125778059420761051980596510720, coefficient := (-125778059420761051980596510720) }, { argument := 3470617805878182345590177792, coefficient := (-3470617805878182345590177792) }, { argument := 99008583956176480971371053056, coefficient := (-99008583956176480971371053056) }, { argument := 335612360272101272805961629696, coefficient := (-335612360272101272805961629696) }, { argument := 99008583956176480971371053056, coefficient := (-99008583956176480971371053056) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5
