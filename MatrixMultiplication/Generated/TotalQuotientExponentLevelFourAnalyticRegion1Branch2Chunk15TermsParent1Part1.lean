import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-92208620092496930157442535293714432)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4903, 1296848492357635, 170426298835324141, 23677357123, 1720502363408570879, 781586959,
    1820958671, 23677357123, 23663312323, 781586959, 292313979019, 11702697285,
    85213152898881479, 23677357123, 1820958671, 11702697285, 1820958671, 23677569923,
    23663312323, 1330858079224195, 777358009537825, 14488377211, 28652482560639711, 228001304531,
    6862915521, 14325612482839415, 6862915521, 6862915521, 587923096299, 6862915521,
    228001304531, 587923096299, 389307802969481, 6862915521, 6862915521, 14488377211,
    17031, 28385, 868581, 28385, 891289, 28385,
    868581, 493899, 891289, 13914327, 17031, 28385,
    868581, 28385, 17031, 28385, 437129, 493899,
    17031, 6758656099, 118268056361, 118268114367, 6758598093, 48190966675139275,
    9345, 525, 170981295654054045, 28385
  ]
def negativeCoefficients : Array ℕ := #[
    94837812697128429497350094848, 365030399183614657226667458560, 47970738495556162365311728746496, 1747080588759219555952935043072, 484278362671056093931305250586624, 922735014657402898995390447616,
    67181517145478542301354524672, 1747080588759219555952935043072, 1746044265434553812310789455872, 922735014657402898995390447616, 21568964640524785842317286178816, 1727013294307924876601044500480,
    47970740455308466229754040680448, 1747080588759219555952935043072, 67181517145478542301354524672, 1727013294307924876601044500480, 67181517145478542301354524672, 1747096290627775097523270582272,
    1746044265434553812310789455872, 374603246854818665393469521920, 14003636968352076581972004044800, 133631693227341385933141311488, 516157239133346550079098269466624, 1051470428288817747210769793024,
    126598446215376049831397031936, 516134584316557723338722215198720, 126598446215376049831397031936, 126598446215376049831397031936, 5422633446225274134444839534592, 126598446215376049831397031936,
    1051470428288817747210769793024, 5422633446225274134444839534592, 14026291811086248862020542660608, 126598446215376049831397031936, 126598446215376049831397031936, 133631693227341385933141311488,
    160853247139505855268913152, 4289419923720156140504350720, 4101757802057399309357285376, 134044372616254879390760960, 4208993300150403212869894144, 134044372616254879390760960,
    4101757802057399309357285376, 2332372083522834901399240704, 4208993300150403212869894144, 65708551456488141877351022592, 2573651954232093684302610432, 4289419923720156140504350720,
    4101757802057399309357285376, 134044372616254879390760960, 2573651954232093684302610432, 134044372616254879390760960, 4128566676580650285235437568, 2332372083522834901399240704,
    160853247139505855268913152, 31168799835117291646008426496, 1090830283893211994432563314688, 1090830818904130364230688833536, 31168532329658106746945667072, 13564551222548826840770176614400,
    2824352946074677409407303680, 158671513824420079180185600, 48126956212182650263405351403520, 4289419923720156140504350720
  ]
def negativeScales : Array ℕ := #[
    12, 50, 57, 34, 60, 29,
    30, 34, 34, 29, 38, 33,
    56, 34, 30, 33, 30, 34,
    34, 50, 49, 33, 54, 37,
    32, 53, 32, 32, 39, 32,
    37, 39, 48, 32, 32, 33,
    14, 14, 19, 14, 19, 14,
    19, 18, 19, 23, 14, 14,
    19, 14, 14, 14, 18, 18,
    14, 32, 36, 36, 32, 55,
    13, 9, 57, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12259449046285686, 50203931366206260, 57241925591088819, 34462789004573225, 60577535581843780, 29541831154831275,
    30762051033144354, 34462789004573225, 34461932981025526, 29541831154831275, 38088727867017701, 33446122035196083,
    56241925650027350, 34462789004573225, 30762051033144354, 33446122035196083, 30762051033144354, 34462801970721579,
    34461932981025526, 50241278155855431, 49465572508305474, 33754176962182354, 54669509663244670, 37730251122835716,
    32676174449975675, 53669446340081347, 32676174449975675, 32676174449975675, 39096836498407495, 32676174449975675,
    37730251122835716, 39096836498407495, 48467904589606067, 32676174449975675, 32676174449975675, 33754176962182354,
    14055875526996034, 14792841121720145, 19728300869106443, 14792841121720145, 19765533775481114, 14792841121720145,
    19728300869106443, 18913856527711209, 19765533775481114, 23730067795286271, 14055875526996034, 14792841121720145,
    19728300869106443, 14792841121720145, 14055875526996034, 14792841121720145, 18737699567141241, 18913856527711209,
    14055875526996034, 32654089261455790, 36783269505447589, 36783270213034671, 32654076879507888, 55419612258961168,
    13189978948632521, 9036173612553486, 57246616124494186, 14792841121720145
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
noncomputable def negativeCeiling : ℝ := 234957643121 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 94837812697128429497350094848, coefficient := (-94837812697128429497350094848) }, { argument := 365030399183614657226667458560, coefficient := (-365030399183614657226667458560) }, { argument := 47970738495556162365311728746496, coefficient := (-47970738495556162365311728746496) }, { argument := 1747080588759219555952935043072, coefficient := (-1747080588759219555952935043072) }, { argument := 484278362671056093931305250586624, coefficient := (-484278362671056093931305250586624) }, { argument := 922735014657402898995390447616, coefficient := (-922735014657402898995390447616) }, { argument := 67181517145478542301354524672, coefficient := (-67181517145478542301354524672) }, { argument := 1747080588759219555952935043072, coefficient := (-1747080588759219555952935043072) }, { argument := 1746044265434553812310789455872, coefficient := (-1746044265434553812310789455872) }, { argument := 922735014657402898995390447616, coefficient := (-922735014657402898995390447616) }, { argument := 21568964640524785842317286178816, coefficient := (-21568964640524785842317286178816) }, { argument := 1727013294307924876601044500480, coefficient := (-1727013294307924876601044500480) }, { argument := 47970740455308466229754040680448, coefficient := (-47970740455308466229754040680448) }, { argument := 1747080588759219555952935043072, coefficient := (-1747080588759219555952935043072) }, { argument := 67181517145478542301354524672, coefficient := (-67181517145478542301354524672) }, { argument := 1727013294307924876601044500480, coefficient := (-1727013294307924876601044500480) }, { argument := 67181517145478542301354524672, coefficient := (-67181517145478542301354524672) }, { argument := 1747096290627775097523270582272, coefficient := (-1747096290627775097523270582272) }, { argument := 1746044265434553812310789455872, coefficient := (-1746044265434553812310789455872) }, { argument := 374603246854818665393469521920, coefficient := (-374603246854818665393469521920) }, { argument := 14003636968352076581972004044800, coefficient := (-14003636968352076581972004044800) }, { argument := 133631693227341385933141311488, coefficient := (-133631693227341385933141311488) }, { argument := 516157239133346550079098269466624, coefficient := (-516157239133346550079098269466624) }, { argument := 1051470428288817747210769793024, coefficient := (-1051470428288817747210769793024) }, { argument := 126598446215376049831397031936, coefficient := (-126598446215376049831397031936) }, { argument := 516134584316557723338722215198720, coefficient := (-516134584316557723338722215198720) }, { argument := 126598446215376049831397031936, coefficient := (-126598446215376049831397031936) }, { argument := 126598446215376049831397031936, coefficient := (-126598446215376049831397031936) }, { argument := 5422633446225274134444839534592, coefficient := (-5422633446225274134444839534592) }, { argument := 126598446215376049831397031936, coefficient := (-126598446215376049831397031936) }, { argument := 1051470428288817747210769793024, coefficient := (-1051470428288817747210769793024) }, { argument := 5422633446225274134444839534592, coefficient := (-5422633446225274134444839534592) }, { argument := 14026291811086248862020542660608, coefficient := (-14026291811086248862020542660608) }, { argument := 126598446215376049831397031936, coefficient := (-126598446215376049831397031936) }, { argument := 126598446215376049831397031936, coefficient := (-126598446215376049831397031936) }, { argument := 133631693227341385933141311488, coefficient := (-133631693227341385933141311488) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 4208993300150403212869894144, coefficient := (-4208993300150403212869894144) }, { argument := 65708551456488141877351022592, coefficient := (-65708551456488141877351022592) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 2573651954232093684302610432, coefficient := (-2573651954232093684302610432) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 4128566676580650285235437568, coefficient := (-4128566676580650285235437568) }, { argument := 2332372083522834901399240704, coefficient := (-2332372083522834901399240704) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 31168799835117291646008426496, coefficient := (-31168799835117291646008426496) }, { argument := 1090830283893211994432563314688, coefficient := (-1090830283893211994432563314688) }, { argument := 1090830818904130364230688833536, coefficient := (-1090830818904130364230688833536) }, { argument := 31168532329658106746945667072, coefficient := (-31168532329658106746945667072) }, { argument := 13564551222548826840770176614400, coefficient := (-13564551222548826840770176614400) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 48126956212182650263405351403520, coefficient := (-48126956212182650263405351403520) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-102836836386161432550120014810710016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6023870725750163, 28385, 28385, 9345, 525, 203437809,
    3559908051, 3559909797, 203436063, 28263998007, 285957, 16065,
    47954836041, 868581, 28263998007, 868581, 868581, 285957,
    16065, 102240180487075, 102240156925021, 183536966658599, 6004455063401491, 13954957821,
    60534910589217457, 460181733, 1073410737, 13954957821, 13953183741, 460181733,
    172228510773, 6900059835, 12008910613355393, 13954957821, 1073410737, 6900059835,
    1073410737, 13954984701, 13953183741, 188553617040327, 777324540845345, 14488384317,
    28651224959195359, 228001416357, 6862918887, 458399479350465353, 6862918887, 6862918887,
    587923384653, 6862918887, 228001416357, 587923384653, 12457312673230007, 6862918887,
    6862918887, 14488384317, 485802151689877321, 9345, 525, 1725965231382206671,
    28385, 60725267790179837, 28385, 28385
  ]
def negativeCoefficients : Array ℕ := #[
    13564550977908236695198366695424, 4289419923720156140504350720, 4289419923720156140504350720, 2824352946074677409407303680, 158671513824420079180185600, 3752765197539205683131449344,
    131337425485470340466796920832, 131337489901500645860551163904, 3752732989524052986254327808, 521378737734965827971487629312, 2700787504683910272745734144, 151729635094601700716052480,
    1769221175090059932801813184512, 4101757802057399309357285376, 521378737734965827971487629312, 4101757802057399309357285376, 4101757802057399309357285376, 2700787504683910272745734144,
    151729635094601700716052480, 230224419371941613115382169600, 230224366314912805873629790208, 103322126831547200592714661888, 13520830793048921401006927904768, 514847070966797015612204777472,
    136312500386253015900375624974336, 271643348993508518441722576896, 19800933151410952124070100992, 514847070966797015612204777472, 514781618967344442329542950912, 271643348993508518441722576896,
    6354110520851318833138511118336, 509134551478110226245683773440, 13520831340858235619961032671232, 514847070966797015612204777472, 19800933151410952124070100992, 509134551478110226245683773440,
    19800933151410952124070100992, 514848062663758418237699653632, 514781618967344442329542950912, 106146249930271985257125249024, 14003034049988150559085407764480, 133631758768623079823178203136,
    516134584199761893020052546912256, 1051470943995218443871849545728, 126598508307116601937747771392, 516111931097396284887163335606272, 126598508307116601937747771392, 126598508307116601937747771392,
    5422636105821494449666862874624, 126598508307116601937747771392, 1051470943995218443871849545728, 5422636105821494449666862874624, 14025687178299104231647103418368, 126598508307116601937747771392,
    126598508307116601937747771392, 133631758768623079823178203136, 136741149332894792282740753432576, 88261029564833669043978240, 4958484807013127474380800, 485816023306708617019918359986176,
    134044372616254879390760960, 136741146695913748495655633944576, 134044372616254879390760960, 134044372616254879390760960
  ]
def negativeScales : Array ℕ := #[
    52, 14, 14, 13, 9, 27,
    31, 31, 27, 34, 18, 13,
    35, 19, 34, 19, 19, 18,
    13, 46, 46, 47, 52, 33,
    55, 28, 29, 33, 33, 28,
    37, 32, 53, 33, 29, 32,
    29, 33, 33, 47, 49, 33,
    54, 37, 32, 58, 32, 32,
    39, 32, 37, 39, 53, 32,
    32, 33, 58, 13, 9, 60,
    14, 55, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    52419612232941747, 14792841121720145, 14792841121720145, 13189978948632521, 9036173612553486, 27600012588682020,
    31729192832375999, 31729193539963075, 27600000206734123, 34718246501595563, 18125438696437810, 13971633375310864,
    35480957261104856, 19728300869106443, 34718246501595563, 19728300869106443, 19728300869106443, 18125438696437810,
    13971633375310864, 46538955616648427, 46538955284167966, 47383063997725072, 52414954742846336, 33700058712796449,
    55748616905567798, 28777628476154460, 29999555101629229, 33700058712796449, 33699875292741748, 28777628476154460,
    37325533030549743, 32683961726547270, 53414954801298496, 33700058712796449, 29999555101629229, 32683961726547270,
    29999555101629229, 33700061491708855, 33699875292741748, 47421968154511739, 49465510392580741, 33754177669769432,
    54669446339754880, 37730251830422793, 32676175157562751, 58669383018604375, 32676175157562751, 32676175157562751,
    39096837205994570, 32676175157562751, 37730251830422793, 39096837205994570, 53467842397863798, 32676175157562751,
    32676175157562751, 33754177669769432, 58753146493224534, 13189978948632521, 9036173612553486, 60582109110489511,
    14792841121720145, 55753146465402920, 14792841121720145, 14792841121720145
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
noncomputable def negativeCeiling : ℝ := 1394356239359 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13564550977908236695198366695424, coefficient := (-13564550977908236695198366695424) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 4289419923720156140504350720, coefficient := (-4289419923720156140504350720) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 3752765197539205683131449344, coefficient := (-3752765197539205683131449344) }, { argument := 131337425485470340466796920832, coefficient := (-131337425485470340466796920832) }, { argument := 131337489901500645860551163904, coefficient := (-131337489901500645860551163904) }, { argument := 3752732989524052986254327808, coefficient := (-3752732989524052986254327808) }, { argument := 521378737734965827971487629312, coefficient := (-521378737734965827971487629312) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 1769221175090059932801813184512, coefficient := (-1769221175090059932801813184512) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 521378737734965827971487629312, coefficient := (-521378737734965827971487629312) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 4101757802057399309357285376, coefficient := (-4101757802057399309357285376) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 230224419371941613115382169600, coefficient := (-230224419371941613115382169600) }, { argument := 230224366314912805873629790208, coefficient := (-230224366314912805873629790208) }, { argument := 103322126831547200592714661888, coefficient := (-103322126831547200592714661888) }, { argument := 13520830793048921401006927904768, coefficient := (-13520830793048921401006927904768) }, { argument := 514847070966797015612204777472, coefficient := (-514847070966797015612204777472) }, { argument := 136312500386253015900375624974336, coefficient := (-136312500386253015900375624974336) }, { argument := 271643348993508518441722576896, coefficient := (-271643348993508518441722576896) }, { argument := 19800933151410952124070100992, coefficient := (-19800933151410952124070100992) }, { argument := 514847070966797015612204777472, coefficient := (-514847070966797015612204777472) }, { argument := 514781618967344442329542950912, coefficient := (-514781618967344442329542950912) }, { argument := 271643348993508518441722576896, coefficient := (-271643348993508518441722576896) }, { argument := 6354110520851318833138511118336, coefficient := (-6354110520851318833138511118336) }, { argument := 509134551478110226245683773440, coefficient := (-509134551478110226245683773440) }, { argument := 13520831340858235619961032671232, coefficient := (-13520831340858235619961032671232) }, { argument := 514847070966797015612204777472, coefficient := (-514847070966797015612204777472) }, { argument := 19800933151410952124070100992, coefficient := (-19800933151410952124070100992) }, { argument := 509134551478110226245683773440, coefficient := (-509134551478110226245683773440) }, { argument := 19800933151410952124070100992, coefficient := (-19800933151410952124070100992) }, { argument := 514848062663758418237699653632, coefficient := (-514848062663758418237699653632) }, { argument := 514781618967344442329542950912, coefficient := (-514781618967344442329542950912) }, { argument := 106146249930271985257125249024, coefficient := (-106146249930271985257125249024) }, { argument := 14003034049988150559085407764480, coefficient := (-14003034049988150559085407764480) }, { argument := 133631758768623079823178203136, coefficient := (-133631758768623079823178203136) }, { argument := 516134584199761893020052546912256, coefficient := (-516134584199761893020052546912256) }, { argument := 1051470943995218443871849545728, coefficient := (-1051470943995218443871849545728) }, { argument := 126598508307116601937747771392, coefficient := (-126598508307116601937747771392) }, { argument := 516111931097396284887163335606272, coefficient := (-516111931097396284887163335606272) }, { argument := 126598508307116601937747771392, coefficient := (-126598508307116601937747771392) }, { argument := 126598508307116601937747771392, coefficient := (-126598508307116601937747771392) }, { argument := 5422636105821494449666862874624, coefficient := (-5422636105821494449666862874624) }, { argument := 126598508307116601937747771392, coefficient := (-126598508307116601937747771392) }, { argument := 1051470943995218443871849545728, coefficient := (-1051470943995218443871849545728) }, { argument := 5422636105821494449666862874624, coefficient := (-5422636105821494449666862874624) }, { argument := 14025687178299104231647103418368, coefficient := (-14025687178299104231647103418368) }, { argument := 126598508307116601937747771392, coefficient := (-126598508307116601937747771392) }, { argument := 126598508307116601937747771392, coefficient := (-126598508307116601937747771392) }, { argument := 133631758768623079823178203136, coefficient := (-133631758768623079823178203136) }, { argument := 136741149332894792282740753432576, coefficient := (-136741149332894792282740753432576) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 485816023306708617019918359986176, coefficient := (-485816023306708617019918359986176) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 136741146695913748495655633944576, coefficient := (-136741146695913748495655633944576) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }, { argument := 134044372616254879390760960, coefficient := (-134044372616254879390760960) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
