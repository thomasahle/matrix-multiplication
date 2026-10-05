import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 11, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 249599107639085717047355629371392
def positiveArguments : Array ℕ := #[
    19, 257, 1025, 509, 1025, 3
  ]
def positiveCoefficients : Array ℕ := #[
    3010670175542044828554670112768, 39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 475368975085586025561263702016
  ]
def positiveScales : Array ℕ := #[
    4, 8, 10, 8, 10, 1
  ]
def negativeArguments : Array ℕ := #[
    4957815, 15443433, 6565755, 52247181, 2361477531, 6565755,
    250007149, 43848905107, 10962227591, 62500473, 2691, 1914165,
    40211, 69206787, 12725, 1527, 40211, 79913,
    12725, 1233307, 78895, 7656665, 40211, 1527,
    78895, 1527, 40211, 40211, 2691, 10319869,
    1810008067, 452502071, 2579913, 10785, 1914795, 80975,
    69206955, 25625, 3075, 80975, 160925, 25625,
    2483575, 158875, 7659185, 80975, 3075, 158875,
    3075, 80975, 80975, 10785, 629061, 12268383,
    24536757, 78633, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    45727772234899160322539520, 71220264042620130460434432, 60558401067839428535255040, 60236898529986267794374656, 2722598228135782122579296256, 60558401067839428535255040,
    288238618387548178349031424, 50554345651325296393093906432, 50554351712233646111288459264, 288232557479198460154478592, 101663105643217722160447488, 9039388638682174430474403840,
    759564314570685214751719424, 81704952828974671267457138688, 480736907956129882754252800, 28844214477367792965255168, 759564314570685214751719424, 754756945491123915924176896,
    480736907956129882754252800, 11648255279777027059135545344, 745142207332001318269091840, 9039394541640278017530920960, 759564314570685214751719424, 28844214477367792965255168,
    745142207332001318269091840, 28844214477367792965255168, 759564314570685214751719424, 759564314570685214751719424, 101663105643217722160447488, 11897998894825557295366144,
    2086797223956170689994555392, 2086797474140137189680349184, 11897748710859057609572352, 101861445035498247259422720, 9042363729566382306959032320, 764787251900739042358067200,
    81705151168366951792556113920, 484042564494138634403840000, 29042553869648318064230400, 764787251900739042358067200, 759946826255797656014028800, 484042564494138634403840000,
    11728351337692979111605043200, 750265974965914883325952000, 9042369632524485894015549440, 764787251900739042358067200, 29042553869648318064230400, 750265974965914883325952000,
    29042553869648318064230400, 764787251900739042358067200, 764787251900739042358067200, 101861445035498247259422720, 2970656582080461887772819456, 115871601356415493111478747136,
    115871558855117147284671823872, 2970670749179910496708460544, 158456325028528675187087900672, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    22, 23, 22, 25, 31, 22,
    27, 35, 33, 25, 11, 20,
    15, 26, 13, 10, 15, 16,
    13, 20, 16, 22, 15, 10,
    16, 10, 15, 15, 11, 23,
    30, 28, 21, 13, 20, 16,
    26, 14, 11, 16, 17, 14,
    21, 17, 22, 16, 11, 17,
    11, 16, 16, 13, 19, 23,
    24, 16, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4247927513443585, 8005624549193878, 10001408194392808, 8991521844801183, 10001408194392808, 1584962500720924
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    22241273007839948, 23880490159620450, 22646529486345706, 25638849862817523, 31137042662576968, 22646529486345706,
    27897394112871740, 35351821768364106, 33351821941327316, 25897363776426689, 11393926675640423, 20868283766495419,
    15295302594252799, 26044410191829388, 13635378035865042, 10576484346799762, 15295302594252799, 16286142594967323,
    13635378035865042, 20234100535527042, 16267646251349933, 22868284708612893, 15295302594252799, 10576484346799762,
    16267646251349933, 10576484346799762, 15295302594252799, 15295302594252799, 11393926675640423, 23298921321576397,
    30753348981478623, 28753349154441834, 21298890985133620, 13396738556047823, 20868758515735728, 16305188942569912,
    26044413693978284, 14645264384186412, 11586370695117825, 16305188942569912, 17296028943284436, 14645264384186412,
    21243986883844155, 17277532599667047, 22868759457543230, 16305188942569912, 11586370695117825, 17277532599667047,
    11586370695117825, 16305188942569912, 16305188942569912, 13396738556047823, 19262840396359288, 23548441775348019,
    24548441246172424, 16262847276574088, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 36130917 / 200000000000
noncomputable def negativeCeiling : ℝ := 47844957 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 71220264042620130460434432, coefficient := (-71220264042620130460434432) }, { argument := 60558401067839428535255040, coefficient := (-60558401067839428535255040) }, { argument := 60236898529986267794374656, coefficient := (-60236898529986267794374656) }, { argument := 2722598228135782122579296256, coefficient := (-2722598228135782122579296256) }, { argument := 60558401067839428535255040, coefficient := (-60558401067839428535255040) }, { argument := 288238618387548178349031424, coefficient := (-288238618387548178349031424) }, { argument := 50554345651325296393093906432, coefficient := (-50554345651325296393093906432) }, { argument := 50554351712233646111288459264, coefficient := (-50554351712233646111288459264) }, { argument := 288232557479198460154478592, coefficient := (-288232557479198460154478592) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }, { argument := 9039388638682174430474403840, coefficient := (-9039388638682174430474403840) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 81704952828974671267457138688, coefficient := (-81704952828974671267457138688) }, { argument := 480736907956129882754252800, coefficient := (-480736907956129882754252800) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 754756945491123915924176896, coefficient := (-754756945491123915924176896) }, { argument := 480736907956129882754252800, coefficient := (-480736907956129882754252800) }, { argument := 11648255279777027059135545344, coefficient := (-11648255279777027059135545344) }, { argument := 745142207332001318269091840, coefficient := (-745142207332001318269091840) }, { argument := 9039394541640278017530920960, coefficient := (-9039394541640278017530920960) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 745142207332001318269091840, coefficient := (-745142207332001318269091840) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }, { argument := 11897998894825557295366144, coefficient := (-11897998894825557295366144) }, { argument := 2086797223956170689994555392, coefficient := (-2086797223956170689994555392) }, { argument := 2086797474140137189680349184, coefficient := (-2086797474140137189680349184) }, { argument := 11897748710859057609572352, coefficient := (-11897748710859057609572352) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 9042363729566382306959032320, coefficient := (-9042363729566382306959032320) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 81705151168366951792556113920, coefficient := (-81705151168366951792556113920) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 759946826255797656014028800, coefficient := (-759946826255797656014028800) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 11728351337692979111605043200, coefficient := (-11728351337692979111605043200) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 9042369632524485894015549440, coefficient := (-9042369632524485894015549440) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 2970656582080461887772819456, coefficient := (-2970656582080461887772819456) }, { argument := 115871601356415493111478747136, coefficient := (-115871601356415493111478747136) }, { argument := 115871558855117147284671823872, coefficient := (-115871558855117147284671823872) }, { argument := 2970670749179910496708460544, coefficient := (-2970670749179910496708460544) }, { argument := 3010670175542044828554670112768, coefficient := 3010670175542044828554670112768 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end TermShard4


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-51459492787491102793970913116160)
def positiveArguments : Array ℕ := #[
    5, 5, 5, 5, 217, 5257,
    3983, 2219, 217, 2219, 4431, 217,
    5257, 217, 9, 27, 57, 147,
    123, 3441, 105, 123, 111, 57,
    57, 111, 3441, 111, 9, 147,
    3, 45, 79, 3, 25, 3,
    79, 157, 25, 2423, 155, 45,
    79, 3, 155, 3, 79, 79,
    3, 629061, 12268383, 24536757, 78633, 3855,
    1822545, 69182355, 7290185, 3855
  ]
def positiveCoefficients : Array ℕ := #[
    198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 8394780891403984989159686144, 203370337078851378285771751424,
    154084849264802176091350368256, 171686809198391176875072290816, 8394780891403984989159686144, 171686809198391176875072290816, 171416009814797499939938107392, 8394780891403984989159686144,
    203370337078851378285771751424, 8394780891403984989159686144, 5570730176784211237046059008, 4178047632588158427784544256, 4410161389954167229328130048, 5686787055467215637817851904,
    76133312416050886906296139776, 133117239849406047685246451712, 4061990753905154027012751360, 76133312416050886906296139776, 4294104511271162828556337152, 4410161389954167229328130048,
    4410161389954167229328130048, 4294104511271162828556337152, 133117239849406047685246451712, 4294104511271162828556337152, 5570730176784211237046059008, 5686787055467215637817851904,
    232113757366008801543585792, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 3868562622766813359059763200, 232113757366008801543585792,
    6112328943971565107314425856, 6073643317743896973723828224, 3868562622766813359059763200, 93735272349639887690018062336, 5996272065288560706542632960, 3481706360490132023153786880,
    6112328943971565107314425856, 232113757366008801543585792, 5996272065288560706542632960, 232113757366008801543585792, 6112328943971565107314425856, 6112328943971565107314425856,
    232113757366008801543585792, 5941313164160923775545638912, 231743202712830986222957494272, 231743117710234294569343647744, 5941341498359820993416921088, 582551129326799433561538560,
    68853803372173260287964610560, 653408868915978427795935068160, 68853850595838088984416747520, 582551129326799433561538560
  ]
def positiveScales : Array ℕ := #[
    2, 2, 2, 2, 7, 12,
    11, 11, 7, 11, 12, 7,
    12, 7, 3, 4, 5, 7,
    6, 11, 6, 6, 6, 5,
    5, 6, 11, 6, 3, 7,
    1, 5, 6, 1, 4, 1,
    6, 7, 4, 11, 7, 5,
    6, 1, 7, 1, 6, 6,
    1, 19, 23, 24, 16, 11,
    20, 26, 22, 11
  ]
def negativeArguments : Array ℕ := #[
    5, 7, 3, 1, 3, 5
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 1109194275199700726309615304704, 475368975085586025561263702016, 158456325028528675187087900672, 475368975085586025561263702016, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    2, 2, 1, 0, 1, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 2321928094887362, 2321928094887362, 2321928094887362, 7761551232426566, 12360024019571875,
    11959639763607828, 11115693952197011, 7761551232426566, 11115693952197011, 12113416611485945, 7761551232426566,
    12360024019571875, 7761551232426566, 3169925001442312, 4754887502147955, 5832890014087662, 7199672344836364,
    6942514504772358, 11748612176723449, 6714245517659862, 6942514504772358, 6794415866314396, 5832890014087662,
    5832890014087662, 6794415866314396, 11748612176723449, 6794415866314396, 3169925001442312, 7199672344836364,
    1584962500720924, 5491853096329661, 6303780748177102, 1584962500720924, 4643856189773592, 1584962500720924,
    6303780748177102, 7294620748891626, 4643856189773592, 11242578689451346, 7276124405274237, 5491853096329661,
    6303780748177102, 1584962500720924, 7276124405274237, 1584962500720924, 6303780748177102, 6303780748177102,
    1584962500720924, 19262840396359287, 23548441775346671, 24548441246171076, 16262847276574087, 11912515144465203,
    20797523005498334, 26043900788778023, 22797523994976334, 11912515144465203
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 2807354922807594, 1584962500724866, 0, 1584962500724866, 2321928094887363
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 314300813 / 500000000000
noncomputable def negativeCeiling : ℝ := 99907953 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 203370337078851378285771751424, coefficient := 203370337078851378285771751424 }, { argument := 154084849264802176091350368256, coefficient := 154084849264802176091350368256 }, { argument := 171686809198391176875072290816, coefficient := 171686809198391176875072290816 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 171686809198391176875072290816, coefficient := 171686809198391176875072290816 }, { argument := 171416009814797499939938107392, coefficient := 171416009814797499939938107392 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 203370337078851378285771751424, coefficient := 203370337078851378285771751424 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5941313164160923775545638912, coefficient := 5941313164160923775545638912 }, { argument := 231743202712830986222957494272, coefficient := 231743202712830986222957494272 }, { argument := 231743117710234294569343647744, coefficient := 231743117710234294569343647744 }, { argument := 5941341498359820993416921088, coefficient := 5941341498359820993416921088 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 582551129326799433561538560, coefficient := 582551129326799433561538560 }, { argument := 68853803372173260287964610560, coefficient := 68853803372173260287964610560 }, { argument := 653408868915978427795935068160, coefficient := 653408868915978427795935068160 }, { argument := 68853850595838088984416747520, coefficient := 68853850595838088984416747520 }, { argument := 582551129326799433561538560, coefficient := 582551129326799433561538560 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end TermShard5


end Parent3

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-36889950603797319649291839471616)
def positiveArguments : Array ℕ := #[
    332899, 58387357, 14596841, 83223, 1066269, 48193419,
    133995
  ]
def positiveCoefficients : Array ℕ := #[
    3144142159561644043988369408, 551452995440288719110819282944, 551453061553419479285852274688, 3144076046430883868955377664, 10070625974645867464724840448, 455173973160986268329991733248,
    10124375949953889766547128320
  ]
def positiveScales : Array ℕ := #[
    18, 25, 23, 16, 20, 25,
    17
  ]
def negativeArguments : Array ℕ := #[
    7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    18344725011189521, 25799152670810491, 23799152843773700, 16344694674746743, 20024140018686312, 25522332818461723,
    17031819642210997
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 1584962500724866
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 118719729 / 250000000000
noncomputable def negativeCeiling : ℝ := 46551461 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3144142159561644043988369408, coefficient := 3144142159561644043988369408 }, { argument := 551452995440288719110819282944, coefficient := 551452995440288719110819282944 }, { argument := 551453061553419479285852274688, coefficient := 551453061553419479285852274688 }, { argument := 3144076046430883868955377664, coefficient := 3144076046430883868955377664 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 10070625974645867464724840448, coefficient := 10070625974645867464724840448 }, { argument := 455173973160986268329991733248, coefficient := 455173973160986268329991733248 }, { argument := 10124375949953889766547128320, coefficient := 10124375949953889766547128320 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
