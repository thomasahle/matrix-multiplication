import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2604602014112884371624026183827456)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    64359169173, 6578077311, 3559914195, 12760138065, 890237175, 98502011385,
    177504975, 98502042183, 177504975, 315435435, 1130645145, 78881775,
    38109432515, 38109459773, 83397, 239754265740155, 10070573275, 1683505839026975,
    113653612675, 10070573275, 3367010873839175, 10070573275, 10070573275, 417497194915,
    2589575985, 113653612675, 417497194915, 239754277720955, 10070573275, 2589575985,
    10070573275, 837097224094485, 80935136679, 2100113327, 6247058034456525, 130368573453,
    1674531554894345, 130368573453, 135861177539, 80935136679, 4038679475, 575050274219,
    1887840055, 575050275989, 1887840055, 315435435, 1130645145, 78881775,
    1484783085, 1484784147, 2139707, 2474638475, 2474640245, 111,
    275525, 177504975, 1887840055, 88752755, 275525, 1644495723,
    257436582273, 64359169173, 6578077311, 315435435
  ]
def negativeCoefficients : Array ℕ := #[
    593608561265454107060059766784, 15168013581636564136149123072, 525350608636246072839068712960, 1883064009842035322635230904320, 525503274628069856036624793600, 227130174345589941557809643520,
    13097555382540848467437158400, 227130245360942939321155977216, 13097555382540848467437158400, 46550053929793955821183303680, 166853773023977813398058434560, 46563581296158088509574348800,
    175748737099627585755215298560, 175748862804965076048954785792, 3150649580575038415092842496, 134969652730981116670231183360, 46442321969866010154080665600, 3790918134658969416137231564800,
    524134776517059257453196083200, 46442321969866010154080665600, 3790917229193629162175410995200, 46442321969866010154080665600, 46442321969866010154080665600, 1925365976522159449530601308160,
    47769245454719324729911541760, 524134776517059257453196083200, 1925365976522159449530601308160, 134969659475571918620285992960, 46442321969866010154080665600, 47769245454719324729911541760,
    46442321969866010154080665600, 3769950746504799231895205314560, 373247438222053952647191330816, 19370126534477849837977993216, 14067124118070134575625089843200, 601218927435524031509547712512,
    3770709843321154704685725122560, 601218927435524031509547712512, 626549092903687373605365088256, 373247438222053952647191330816, 18625121667767163305748070400, 1325975654754298850667541823488,
    139298009386731055907099115520, 1325975658835640976975780118528, 139298009386731055907099115520, 46550053929793955821183303680, 166853773023977813398058434560, 46563581296158088509574348800,
    109557654295871741769484861440, 109557732657640566887660126208, 80835844959692479610094616576, 5706127827909986550494003200, 5706131909252112858732298240, 2147052255635581414278168576,
    40660313287270593671987200, 13097555382540848467437158400, 139298009386731055907099115520, 13097594858573166205877616640, 40660313287270593671987200, 15167795866245477188379869184,
    593608343550063020112290512896, 593608561265454107060059766784, 15168013581636564136149123072, 46550053929793955821183303680
  ]
def negativeScales : Array ℕ := #[
    35, 32, 31, 33, 29, 36,
    27, 36, 27, 28, 30, 26,
    35, 35, 16, 47, 33, 50,
    36, 33, 51, 33, 33, 38,
    31, 36, 38, 47, 33, 31,
    33, 49, 36, 30, 52, 36,
    50, 36, 36, 36, 31, 39,
    30, 39, 30, 28, 30, 26,
    30, 30, 21, 31, 31, 6,
    18, 27, 30, 26, 18, 30,
    37, 35, 32, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35905426655792551, 32615018818011954, 31729195322302868, 33570924888058289, 29729614506121057, 36519434133194800,
    27403284219250004, 36519434584273050, 27403284219250004, 28232769496041627, 30074499061936313, 26233188679858471,
    35149429074108698, 35149430106004604, 16347707866780927, 47768549812854632, 33229426761062272, 50580390148293121,
    36725852587313210, 33229426761062272, 51580389803703640, 33229426761062272, 33229426761062272, 38602975548190189,
    31270068745559618, 36725852587313210, 38602975548190189, 47768549884947783, 33229426761062272, 31270068745559618,
    33229426761062272, 49572388521778549, 36236047110212490, 30967820049198493, 52472098355748579, 36923805186946815,
    50572678985777889, 36923805186946815, 36983342325380771, 36236047110212490, 31911236512127016, 39064897134071619,
    30814089394103419, 39064897138512223, 30814089394103419, 28232769496041627, 30074499061936313, 26233188679858471,
    30467605034135042, 30467606066030947, 21028981824554590, 31204570628301159, 31204571660197065, 6794415866926375,
    18071823703359091, 27403284219250004, 30814089394103419, 26403288567526348, 18071823703359091, 30614998110015639,
    37905426126661032, 35905426655792551, 32615018818011954, 28232769496041627
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
noncomputable def negativeCeiling : ℝ := 6455637213 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 593608561265454107060059766784, coefficient := (-593608561265454107060059766784) }, { argument := 15168013581636564136149123072, coefficient := (-15168013581636564136149123072) }, { argument := 525350608636246072839068712960, coefficient := (-525350608636246072839068712960) }, { argument := 1883064009842035322635230904320, coefficient := (-1883064009842035322635230904320) }, { argument := 525503274628069856036624793600, coefficient := (-525503274628069856036624793600) }, { argument := 227130174345589941557809643520, coefficient := (-227130174345589941557809643520) }, { argument := 13097555382540848467437158400, coefficient := (-13097555382540848467437158400) }, { argument := 227130245360942939321155977216, coefficient := (-227130245360942939321155977216) }, { argument := 13097555382540848467437158400, coefficient := (-13097555382540848467437158400) }, { argument := 46550053929793955821183303680, coefficient := (-46550053929793955821183303680) }, { argument := 166853773023977813398058434560, coefficient := (-166853773023977813398058434560) }, { argument := 46563581296158088509574348800, coefficient := (-46563581296158088509574348800) }, { argument := 175748737099627585755215298560, coefficient := (-175748737099627585755215298560) }, { argument := 175748862804965076048954785792, coefficient := (-175748862804965076048954785792) }, { argument := 3150649580575038415092842496, coefficient := (-3150649580575038415092842496) }, { argument := 134969652730981116670231183360, coefficient := (-134969652730981116670231183360) }, { argument := 46442321969866010154080665600, coefficient := (-46442321969866010154080665600) }, { argument := 3790918134658969416137231564800, coefficient := (-3790918134658969416137231564800) }, { argument := 524134776517059257453196083200, coefficient := (-524134776517059257453196083200) }, { argument := 46442321969866010154080665600, coefficient := (-46442321969866010154080665600) }, { argument := 3790917229193629162175410995200, coefficient := (-3790917229193629162175410995200) }, { argument := 46442321969866010154080665600, coefficient := (-46442321969866010154080665600) }, { argument := 46442321969866010154080665600, coefficient := (-46442321969866010154080665600) }, { argument := 1925365976522159449530601308160, coefficient := (-1925365976522159449530601308160) }, { argument := 47769245454719324729911541760, coefficient := (-47769245454719324729911541760) }, { argument := 524134776517059257453196083200, coefficient := (-524134776517059257453196083200) }, { argument := 1925365976522159449530601308160, coefficient := (-1925365976522159449530601308160) }, { argument := 134969659475571918620285992960, coefficient := (-134969659475571918620285992960) }, { argument := 46442321969866010154080665600, coefficient := (-46442321969866010154080665600) }, { argument := 47769245454719324729911541760, coefficient := (-47769245454719324729911541760) }, { argument := 46442321969866010154080665600, coefficient := (-46442321969866010154080665600) }, { argument := 3769950746504799231895205314560, coefficient := (-3769950746504799231895205314560) }, { argument := 373247438222053952647191330816, coefficient := (-373247438222053952647191330816) }, { argument := 19370126534477849837977993216, coefficient := (-19370126534477849837977993216) }, { argument := 14067124118070134575625089843200, coefficient := (-14067124118070134575625089843200) }, { argument := 601218927435524031509547712512, coefficient := (-601218927435524031509547712512) }, { argument := 3770709843321154704685725122560, coefficient := (-3770709843321154704685725122560) }, { argument := 601218927435524031509547712512, coefficient := (-601218927435524031509547712512) }, { argument := 626549092903687373605365088256, coefficient := (-626549092903687373605365088256) }, { argument := 373247438222053952647191330816, coefficient := (-373247438222053952647191330816) }, { argument := 18625121667767163305748070400, coefficient := (-18625121667767163305748070400) }, { argument := 1325975654754298850667541823488, coefficient := (-1325975654754298850667541823488) }, { argument := 139298009386731055907099115520, coefficient := (-139298009386731055907099115520) }, { argument := 1325975658835640976975780118528, coefficient := (-1325975658835640976975780118528) }, { argument := 139298009386731055907099115520, coefficient := (-139298009386731055907099115520) }, { argument := 46550053929793955821183303680, coefficient := (-46550053929793955821183303680) }, { argument := 166853773023977813398058434560, coefficient := (-166853773023977813398058434560) }, { argument := 46563581296158088509574348800, coefficient := (-46563581296158088509574348800) }, { argument := 109557654295871741769484861440, coefficient := (-109557654295871741769484861440) }, { argument := 109557732657640566887660126208, coefficient := (-109557732657640566887660126208) }, { argument := 80835844959692479610094616576, coefficient := (-80835844959692479610094616576) }, { argument := 5706127827909986550494003200, coefficient := (-5706127827909986550494003200) }, { argument := 5706131909252112858732298240, coefficient := (-5706131909252112858732298240) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 13097555382540848467437158400, coefficient := (-13097555382540848467437158400) }, { argument := 139298009386731055907099115520, coefficient := (-139298009386731055907099115520) }, { argument := 13097594858573166205877616640, coefficient := (-13097594858573166205877616640) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 15167795866245477188379869184, coefficient := (-15167795866245477188379869184) }, { argument := 593608343550063020112290512896, coefficient := (-593608343550063020112290512896) }, { argument := 593608561265454107060059766784, coefficient := (-593608561265454107060059766784) }, { argument := 15168013581636564136149123072, coefficient := (-15168013581636564136149123072) }, { argument := 46550053929793955821183303680, coefficient := (-46550053929793955821183303680) }] }

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

end TermShard2


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2366197073457773783384099852910592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1130645145, 78881775, 1713780549, 268282733199, 67070707899, 6855220593,
    13077051891, 46873317297, 3270213015, 75723937335, 75723991497, 81111969,
    290737323, 20283885, 2474638475, 2474640245, 9, 1020932289,
    159821223939, 39955320639, 4083787773, 3559914195, 12760138065, 890237175,
    1484783085, 1484784147, 13077051891, 46873317297, 3270213015, 1213067780445,
    1213068648099, 1929, 77703648115, 77703703693, 3489, 59746904260017,
    8272288053, 214650189, 440785141939721, 13324823271, 119521413428885, 13324823271,
    13886216073, 8272288053, 412788825, 98502027033, 88752755, 98502057831,
    88752755, 17117657, 75723937335, 75723991497, 1929, 57,
    50944725, 7975110975, 1993778475, 203781825, 315435435, 1130645145,
    78881775, 2474638475, 2474640245, 81111969
  ]
def negativeCoefficients : Array ℕ := #[
    166853773023977813398058434560, 46563581296158088509574348800, 15806835592952225917506158592, 618617864839656753301655912448, 618618091727691330901499707392, 15807062480986803517349953536,
    1929832235775172282758199246848, 6917280704508337349730936815616, 1930393041735011040782639431680, 174607511534045588445116497920, 174607636423114653477208326144, 47880055470645211701788540928,
    171621023681805750923717246976, 47893969333191176752705044480, 182596090493119569615808102400, 182596221096067611479433543680, 2785365088392105618523029504, 9416438325884738626243264512,
    368522651943719421408001916928, 368522787105319092487100301312, 9416573487484409705341648896, 525350608636246072839068712960, 1883064009842035322635230904320, 525503274628069856036624793600,
    109557654295871741769484861440, 109557732657640566887660126208, 1929832235775172282758199246848, 6917280704508337349730936815616, 1930393041735011040782639431680, 2797143861241475407052160368640,
    2797145861915385723350572597248, 37312286496585914848131416064, 179172413796373577685511700480, 179172541950516343764194164736, 67487074954167059048797569024, 134538067880976630627189129216,
    9537298788606004701563977728, 494949637732048148184956928, 496279950247544671008041467904, 15362475294221648291740778496, 134569148245280370653910794240, 15362475294221648291740778496,
    16009717128178942023982645248, 9537298788606004701563977728, 475913113203892450177843200, 227130210427421349733692604416, 13097594858573166205877616640, 227130281442774347497038938112,
    13097594858573166205877616640, 80835849682058962479739830272, 174607511534045588445116497920, 174607636423114653477208326144, 37312286496585914848131416064, 2205080694977083614664065024,
    469882151990256418475212800, 18389353889407156756886323200, 18389360633997958706941132800, 469888896581058368530022400, 46550053929793955821183303680, 166853773023977813398058434560,
    46563581296158088509574348800, 5706127827909986550494003200, 5706131909252112858732298240, 47880055470645211701788540928
  ]
def negativeScales : Array ℕ := #[
    30, 26, 30, 37, 35, 32,
    33, 35, 31, 36, 36, 26,
    28, 24, 31, 31, 3, 29,
    37, 35, 31, 31, 33, 29,
    30, 30, 33, 35, 31, 40,
    40, 10, 36, 36, 11, 45,
    32, 27, 48, 33, 46, 33,
    33, 32, 28, 36, 26, 36,
    26, 24, 36, 36, 10, 5,
    25, 32, 30, 27, 28, 30,
    26, 31, 31, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30074499061936313, 26233188679858471, 30674535237023781, 37964963262217206, 35964963791348797, 32674555945020111,
    33606318283170134, 35448047849058135, 31606737466987056, 36140030376106449, 36140031408002354, 26273411480538973,
    28115141046433659, 24273830664355817, 31204570628301159, 31204571660197065, 3169925001442313, 29927240046985554,
    37217668051766162, 35217668580897635, 31927260754984400, 31729195322302868, 33570924888058289, 29729614506121057,
    30467605034135042, 30467606066030947, 33606318283170134, 35448047849058135, 31606737466987056, 40141797302280637,
    40141798334176542, 10913637433615165, 36177263282305424, 36177264314201329, 11768597882530236, 45763929196733488,
    32945639286917943, 27677412202223753, 48647068922562541, 33633397347332170, 46764262443003045, 33633397347332170,
    33692934474356897, 32945639286917943, 28620828673825191, 36519434362380883, 26403288567526348, 36519434813459062,
    26403288567526348, 24028981908835697, 36140030376106449, 36140031408002354, 10913637433615165, 5832890015409720,
    25602429436510112, 32892857452186175, 30892857981317685, 27602450144506426, 28232769496041627, 30074499061936313,
    26233188679858471, 31204570628301159, 31204571660197065, 26273411480538973
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
noncomputable def negativeCeiling : ℝ := 15359678953 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 166853773023977813398058434560, coefficient := (-166853773023977813398058434560) }, { argument := 46563581296158088509574348800, coefficient := (-46563581296158088509574348800) }, { argument := 15806835592952225917506158592, coefficient := (-15806835592952225917506158592) }, { argument := 618617864839656753301655912448, coefficient := (-618617864839656753301655912448) }, { argument := 618618091727691330901499707392, coefficient := (-618618091727691330901499707392) }, { argument := 15807062480986803517349953536, coefficient := (-15807062480986803517349953536) }, { argument := 1929832235775172282758199246848, coefficient := (-1929832235775172282758199246848) }, { argument := 6917280704508337349730936815616, coefficient := (-6917280704508337349730936815616) }, { argument := 1930393041735011040782639431680, coefficient := (-1930393041735011040782639431680) }, { argument := 174607511534045588445116497920, coefficient := (-174607511534045588445116497920) }, { argument := 174607636423114653477208326144, coefficient := (-174607636423114653477208326144) }, { argument := 47880055470645211701788540928, coefficient := (-47880055470645211701788540928) }, { argument := 171621023681805750923717246976, coefficient := (-171621023681805750923717246976) }, { argument := 47893969333191176752705044480, coefficient := (-47893969333191176752705044480) }, { argument := 182596090493119569615808102400, coefficient := (-182596090493119569615808102400) }, { argument := 182596221096067611479433543680, coefficient := (-182596221096067611479433543680) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 9416438325884738626243264512, coefficient := (-9416438325884738626243264512) }, { argument := 368522651943719421408001916928, coefficient := (-368522651943719421408001916928) }, { argument := 368522787105319092487100301312, coefficient := (-368522787105319092487100301312) }, { argument := 9416573487484409705341648896, coefficient := (-9416573487484409705341648896) }, { argument := 525350608636246072839068712960, coefficient := (-525350608636246072839068712960) }, { argument := 1883064009842035322635230904320, coefficient := (-1883064009842035322635230904320) }, { argument := 525503274628069856036624793600, coefficient := (-525503274628069856036624793600) }, { argument := 109557654295871741769484861440, coefficient := (-109557654295871741769484861440) }, { argument := 109557732657640566887660126208, coefficient := (-109557732657640566887660126208) }, { argument := 1929832235775172282758199246848, coefficient := (-1929832235775172282758199246848) }, { argument := 6917280704508337349730936815616, coefficient := (-6917280704508337349730936815616) }, { argument := 1930393041735011040782639431680, coefficient := (-1930393041735011040782639431680) }, { argument := 2797143861241475407052160368640, coefficient := (-2797143861241475407052160368640) }, { argument := 2797145861915385723350572597248, coefficient := (-2797145861915385723350572597248) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 179172413796373577685511700480, coefficient := (-179172413796373577685511700480) }, { argument := 179172541950516343764194164736, coefficient := (-179172541950516343764194164736) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 134538067880976630627189129216, coefficient := (-134538067880976630627189129216) }, { argument := 9537298788606004701563977728, coefficient := (-9537298788606004701563977728) }, { argument := 494949637732048148184956928, coefficient := (-494949637732048148184956928) }, { argument := 496279950247544671008041467904, coefficient := (-496279950247544671008041467904) }, { argument := 15362475294221648291740778496, coefficient := (-15362475294221648291740778496) }, { argument := 134569148245280370653910794240, coefficient := (-134569148245280370653910794240) }, { argument := 15362475294221648291740778496, coefficient := (-15362475294221648291740778496) }, { argument := 16009717128178942023982645248, coefficient := (-16009717128178942023982645248) }, { argument := 9537298788606004701563977728, coefficient := (-9537298788606004701563977728) }, { argument := 475913113203892450177843200, coefficient := (-475913113203892450177843200) }, { argument := 227130210427421349733692604416, coefficient := (-227130210427421349733692604416) }, { argument := 13097594858573166205877616640, coefficient := (-13097594858573166205877616640) }, { argument := 227130281442774347497038938112, coefficient := (-227130281442774347497038938112) }, { argument := 13097594858573166205877616640, coefficient := (-13097594858573166205877616640) }, { argument := 80835849682058962479739830272, coefficient := (-80835849682058962479739830272) }, { argument := 174607511534045588445116497920, coefficient := (-174607511534045588445116497920) }, { argument := 174607636423114653477208326144, coefficient := (-174607636423114653477208326144) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 469882151990256418475212800, coefficient := (-469882151990256418475212800) }, { argument := 18389353889407156756886323200, coefficient := (-18389353889407156756886323200) }, { argument := 18389360633997958706941132800, coefficient := (-18389360633997958706941132800) }, { argument := 469888896581058368530022400, coefficient := (-469888896581058368530022400) }, { argument := 46550053929793955821183303680, coefficient := (-46550053929793955821183303680) }, { argument := 166853773023977813398058434560, coefficient := (-166853773023977813398058434560) }, { argument := 46563581296158088509574348800, coefficient := (-46563581296158088509574348800) }, { argument := 5706127827909986550494003200, coefficient := (-5706127827909986550494003200) }, { argument := 5706131909252112858732298240, coefficient := (-5706131909252112858732298240) }, { argument := 47880055470645211701788540928, coefficient := (-47880055470645211701788540928) }] }

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

end TermShard3


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
