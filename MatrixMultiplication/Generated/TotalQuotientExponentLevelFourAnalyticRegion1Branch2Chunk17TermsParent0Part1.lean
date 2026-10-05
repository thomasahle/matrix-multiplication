import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 17, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

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
def constantNumerator : ℤ := (-9835230605419513609881969512939520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15261413601859, 865074465, 510914116340157, 13613540265, 409772115, 4087274153630251,
    409772115, 409772115, 35103811185, 409772115, 13613540265, 35103811185,
    122130085905877, 409772115, 409772115, 865074465, 5548905, 409772115,
    4270986225, 409772115, 5548905, 3527623827, 132541889389, 265063729931,
    7075296501, 114027301283565, 185040345, 10395525, 414153164562175, 562051385,
    28506823780485, 562051385, 562051385, 185040345, 10395525, 6997440211959,
    101399600815113, 5074340865, 47698804131, 563251836015, 39579858747, 50699788791675,
    563251836015, 5074340865, 39579858747, 39579858747, 39579858747, 39579858747,
    39579858747, 3498731721861, 47698804131, 52492678898279, 4100809992969747, 66544751273,
    143757900281606361, 2193783009, 5118827021, 66544751273, 66544751273, 2193783009,
    821206106369, 32906745135, 4100809992969747, 66544751273
  ]
def negativeCoefficients : Array ℕ := #[
    274925186441916846401709408256, 31915614521112421859202170880, 9203810495871429227076007231488, 251125493205595108839511818240, 30235845335790715445559951360, 9203723177625128912169885237248,
    30235845335790715445559951360, 30235845335790715445559951360, 1295102041883035644918151249920, 30235845335790715445559951360, 251125493205595108839511818240, 1295102041883035644918151249920,
    275012504688217161307831402496, 30235845335790715445559951360, 30235845335790715445559951360, 31915614521112421859202170880, 204718460848654599019560960, 30235845335790715445559951360,
    315143159339655518411449958400, 30235845335790715445559951360, 204718460848654599019560960, 65073173924988858558087954432, 2444966312604802653200658202624, 2444781394630011673439264309248,
    65258091899779838319481847808, 64191663946340826780826337280, 426673985940740107602493440, 23970448648356185820364800, 233147504699565379895794073600, 648001128460562223343861760,
    64191660477654320031234785280, 648001128460562223343861760, 648001128460562223343861760, 426673985940740107602493440, 23970448648356185820364800, 63027338262251753896125923328,
    913326408892919898532894212096, 46802533639710474952947793920, 54992977026659808069713657856, 649385154250982839972150640640, 1460239049558966818531971170304, 913326199639801518613541683200,
    649385154250982839972150640640, 46802533639710474952947793920, 45632470298717713079124099072, 45632470298717713079124099072, 45632470298717713079124099072, 1460239049558966818531971170304,
    45632470298717713079124099072, 63027547515370133815478452224, 54992977026659808069713657856, 118203004562984201451514888192, 9234203178127879455319844192256, 2455067992363377781462150414336,
    80928503267475916172895172165632, 1294980919048814653958057361408, 94425692013976068517775015936, 2455067992363377781462150414336, 2455067992363377781462150414336, 1294980919048814653958057361408,
    30297157751912892841560383684608, 2428089223216527476171357552640, 9234203178127879455319844192256, 2455067992363377781462150414336
  ]
def negativeScales : Array ℕ := #[
    43, 29, 48, 33, 28, 51,
    28, 28, 35, 28, 33, 35,
    46, 28, 28, 29, 22, 28,
    31, 28, 22, 31, 36, 37,
    32, 46, 27, 23, 48, 29,
    44, 29, 29, 27, 23, 42,
    46, 32, 35, 39, 35, 45,
    39, 32, 35, 35, 35, 35,
    35, 41, 35, 45, 51, 35,
    56, 31, 32, 35, 35, 31,
    39, 34, 51, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    43794953833377221, 29688249083420169, 48860074127859730, 33664323244150467, 28610246571371618, 51860060440680542,
    28610246571371618, 28610246571371618, 35030908619836850, 28610246571371618, 33664323244150467, 35030908619836850,
    46795411971109987, 28610246571371618, 28610246571371618, 29688249083420169, 22403771672871506, 28610246571371618,
    31991922119724051, 28610246571371618, 22403771672871506, 31716049579426571, 36947657444119108, 37947548325896033,
    32720143461630567, 46696372615255105, 27463264620032912, 23309459283953801, 48557157740808946, 29066126792562555,
    44696372537297054, 29066126792562555, 29066126792562555, 27463264620032912, 23309459283953801, 42669964393753724,
    46527045301246336, 32240573288588705, 35473234045379088, 39034989154938811, 35204047412563591, 45527044970709008,
    39034989154938811, 32240573288588705, 35204047412563591, 35204047412563591, 35204047412563591, 35204047412563591,
    35204047412563591, 41669969183547227, 35473234045379088, 45577181459104936, 51864830324949692, 35953605837792727,
    56996418877650905, 31030773687238140, 32253166108574588, 35953605837792727, 35953605837792727, 31030773687238140,
    39578953398920709, 34937664291297766, 51864830324949692, 35953605837792727
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
noncomputable def negativeCeiling : ℝ := 106354935281 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 274925186441916846401709408256, coefficient := (-274925186441916846401709408256) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 9203810495871429227076007231488, coefficient := (-9203810495871429227076007231488) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 9203723177625128912169885237248, coefficient := (-9203723177625128912169885237248) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 275012504688217161307831402496, coefficient := (-275012504688217161307831402496) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 65073173924988858558087954432, coefficient := (-65073173924988858558087954432) }, { argument := 2444966312604802653200658202624, coefficient := (-2444966312604802653200658202624) }, { argument := 2444781394630011673439264309248, coefficient := (-2444781394630011673439264309248) }, { argument := 65258091899779838319481847808, coefficient := (-65258091899779838319481847808) }, { argument := 64191663946340826780826337280, coefficient := (-64191663946340826780826337280) }, { argument := 426673985940740107602493440, coefficient := (-426673985940740107602493440) }, { argument := 23970448648356185820364800, coefficient := (-23970448648356185820364800) }, { argument := 233147504699565379895794073600, coefficient := (-233147504699565379895794073600) }, { argument := 648001128460562223343861760, coefficient := (-648001128460562223343861760) }, { argument := 64191660477654320031234785280, coefficient := (-64191660477654320031234785280) }, { argument := 648001128460562223343861760, coefficient := (-648001128460562223343861760) }, { argument := 648001128460562223343861760, coefficient := (-648001128460562223343861760) }, { argument := 426673985940740107602493440, coefficient := (-426673985940740107602493440) }, { argument := 23970448648356185820364800, coefficient := (-23970448648356185820364800) }, { argument := 63027338262251753896125923328, coefficient := (-63027338262251753896125923328) }, { argument := 913326408892919898532894212096, coefficient := (-913326408892919898532894212096) }, { argument := 46802533639710474952947793920, coefficient := (-46802533639710474952947793920) }, { argument := 54992977026659808069713657856, coefficient := (-54992977026659808069713657856) }, { argument := 649385154250982839972150640640, coefficient := (-649385154250982839972150640640) }, { argument := 1460239049558966818531971170304, coefficient := (-1460239049558966818531971170304) }, { argument := 913326199639801518613541683200, coefficient := (-913326199639801518613541683200) }, { argument := 649385154250982839972150640640, coefficient := (-649385154250982839972150640640) }, { argument := 46802533639710474952947793920, coefficient := (-46802533639710474952947793920) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 1460239049558966818531971170304, coefficient := (-1460239049558966818531971170304) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 63027547515370133815478452224, coefficient := (-63027547515370133815478452224) }, { argument := 54992977026659808069713657856, coefficient := (-54992977026659808069713657856) }, { argument := 118203004562984201451514888192, coefficient := (-118203004562984201451514888192) }, { argument := 9234203178127879455319844192256, coefficient := (-9234203178127879455319844192256) }, { argument := 2455067992363377781462150414336, coefficient := (-2455067992363377781462150414336) }, { argument := 80928503267475916172895172165632, coefficient := (-80928503267475916172895172165632) }, { argument := 1294980919048814653958057361408, coefficient := (-1294980919048814653958057361408) }, { argument := 94425692013976068517775015936, coefficient := (-94425692013976068517775015936) }, { argument := 2455067992363377781462150414336, coefficient := (-2455067992363377781462150414336) }, { argument := 2455067992363377781462150414336, coefficient := (-2455067992363377781462150414336) }, { argument := 1294980919048814653958057361408, coefficient := (-1294980919048814653958057361408) }, { argument := 30297157751912892841560383684608, coefficient := (-30297157751912892841560383684608) }, { argument := 2428089223216527476171357552640, coefficient := (-2428089223216527476171357552640) }, { argument := 9234203178127879455319844192256, coefficient := (-9234203178127879455319844192256) }, { argument := 2455067992363377781462150414336, coefficient := (-2455067992363377781462150414336) }] }

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
def constantNumerator : ℤ := (-11693928130693547932336913500864512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5118827021, 32906745135, 5118827021, 66544751273, 66544751273, 233922421921011,
    545726894280553, 9016526475, 17912653551681687, 141891653475, 4270986225, 143301182639065633,
    4270986225, 4270986225, 365881153275, 4270986225, 141891653475, 365881153275,
    4365860928632287, 4270986225, 4270986225, 9016526475, 5548905, 409772115,
    4270986225, 409772115, 5548905, 116295291, 4369512837, 8738364723,
    233251533, 1636355854326035, 15493268007, 870408315, 5902087796973825, 47060076231,
    409088834049915, 47060076231, 47060076231, 15493268007, 870408315, 271355679,
    10195529953, 20389517687, 544253577, 1294626555, 2354417925, 1294626555,
    2324491, 2324491, 562051385, 47060076231, 23530046631, 281017177,
    5548905, 409772115, 4270986225, 409772115, 5548905, 562051385,
    47060076231, 23530046631, 281017177, 475356195
  ]
def negativeCoefficients : Array ℕ := #[
    94425692013976068517775015936, 2428089223216527476171357552640, 94425692013976068517775015936, 2455067992363377781462150414336, 2455067992363377781462150414336, 131686616524633635586867986432,
    2457735437727956555577098764288, 332651112636303047212086067200, 80671419860570437286214607306752, 2617439017848805555695098265600, 315143159339655518411449958400, 80671394091880921921295268970496,
    315143159339655518411449958400, 315143159339655518411449958400, 13498631991715244705290439884800, 315143159339655518411449958400, 2617439017848805555695098265600, 13498631991715244705290439884800,
    2457761206417471920496437100544, 315143159339655518411449958400, 315143159339655518411449958400, 332651112636303047212086067200, 204718460848654599019560960, 30235845335790715445559951360,
    315143159339655518411449958400, 30235845335790715445559951360, 204718460848654599019560960, 34324311520873244074595844096, 1289652560494840959930017513472, 1289555021343302860715216338944,
    34421850672411343289397018624, 921186451973532607624165457920, 35725043723815130732810993664, 2007024928304220827686010880, 3322580050394908739898861158400, 54256573895157436375111827456,
    921186160294313935020931153920, 54256573895157436375111827456, 54256573895157436375111827456, 35725043723815130732810993664, 2007024928304220827686010880, 2502814381730340713772613632,
    94037165869415486661563777024, 94030053639615833593817858048, 2509926611529993781518532608, 47763289462226525758433525760, 173725379620117158273692467200, 47763289462226525758433525760,
    5488549194066072236214714368, 5488549194066072236214714368, 648001128460562223343861760, 54256573895157436375111827456, 54256593530563581334322675712, 647981493054417264133013504,
    204718460848654599019560960, 30235845335790715445559951360, 315143159339655518411449958400, 30235845335790715445559951360, 204718460848654599019560960, 648001128460562223343861760,
    54256573895157436375111827456, 54256593530563581334322675712, 647981493054417264133013504, 8768774073017371991337861120
  ]
def negativeScales : Array ℕ := #[
    32, 34, 32, 35, 35, 47,
    48, 33, 53, 37, 31, 56,
    31, 31, 38, 31, 37, 38,
    51, 31, 31, 33, 22, 28,
    31, 28, 22, 26, 32, 33,
    27, 50, 33, 29, 52, 35,
    48, 35, 35, 33, 29, 28,
    33, 34, 29, 30, 31, 30,
    21, 21, 29, 35, 34, 28,
    22, 28, 31, 28, 22, 29,
    35, 34, 28, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32253166108574588, 34937664291297766, 32253166108574588, 35953605837792727, 35953605837792727, 47733023482033128,
    48955172483541078, 33069924610922346, 53991828610647440, 37045998771676865, 31991922119724051, 56991828149810393,
    31991922119724051, 31991922119724051, 38412584147393805, 31991922119724051, 37045998771676865, 38412584147393805,
    51955187609730907, 31991922119724051, 31991922119724051, 33069924610922346, 22403771672871506, 28610246571371618,
    31991922119724051, 28610246571371618, 22403771672871506, 26793217440406159, 32024825294622351, 33024716176417771,
    27797311322649096, 50539407945090231, 33850922435642992, 29697117097868714, 52390146805164168, 35453784606409891,
    48539407488283438, 35453784606409891, 35453784606409891, 33850922435642992, 29697117097868714, 28015609861180364,
    33247217715958799, 34247108597754219, 29019703743374031, 30269888855413261, 31132723285156585, 30269888855413261,
    21148483409343020, 21148483409343020, 29066126792562555, 35453784606409891, 34453785128519857, 28066083076076542,
    22403771672871506, 28610246571371618, 31991922119724051, 28610246571371618, 22403771672871506, 29066126792562555,
    35453784606409891, 34453785128519857, 28066083076076542, 28824433722398829
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
noncomputable def negativeCeiling : ℝ := 134747886231 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 94425692013976068517775015936, coefficient := (-94425692013976068517775015936) }, { argument := 2428089223216527476171357552640, coefficient := (-2428089223216527476171357552640) }, { argument := 94425692013976068517775015936, coefficient := (-94425692013976068517775015936) }, { argument := 2455067992363377781462150414336, coefficient := (-2455067992363377781462150414336) }, { argument := 2455067992363377781462150414336, coefficient := (-2455067992363377781462150414336) }, { argument := 131686616524633635586867986432, coefficient := (-131686616524633635586867986432) }, { argument := 2457735437727956555577098764288, coefficient := (-2457735437727956555577098764288) }, { argument := 332651112636303047212086067200, coefficient := (-332651112636303047212086067200) }, { argument := 80671419860570437286214607306752, coefficient := (-80671419860570437286214607306752) }, { argument := 2617439017848805555695098265600, coefficient := (-2617439017848805555695098265600) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 80671394091880921921295268970496, coefficient := (-80671394091880921921295268970496) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 13498631991715244705290439884800, coefficient := (-13498631991715244705290439884800) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 2617439017848805555695098265600, coefficient := (-2617439017848805555695098265600) }, { argument := 13498631991715244705290439884800, coefficient := (-13498631991715244705290439884800) }, { argument := 2457761206417471920496437100544, coefficient := (-2457761206417471920496437100544) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 332651112636303047212086067200, coefficient := (-332651112636303047212086067200) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 34324311520873244074595844096, coefficient := (-34324311520873244074595844096) }, { argument := 1289652560494840959930017513472, coefficient := (-1289652560494840959930017513472) }, { argument := 1289555021343302860715216338944, coefficient := (-1289555021343302860715216338944) }, { argument := 34421850672411343289397018624, coefficient := (-34421850672411343289397018624) }, { argument := 921186451973532607624165457920, coefficient := (-921186451973532607624165457920) }, { argument := 35725043723815130732810993664, coefficient := (-35725043723815130732810993664) }, { argument := 2007024928304220827686010880, coefficient := (-2007024928304220827686010880) }, { argument := 3322580050394908739898861158400, coefficient := (-3322580050394908739898861158400) }, { argument := 54256573895157436375111827456, coefficient := (-54256573895157436375111827456) }, { argument := 921186160294313935020931153920, coefficient := (-921186160294313935020931153920) }, { argument := 54256573895157436375111827456, coefficient := (-54256573895157436375111827456) }, { argument := 54256573895157436375111827456, coefficient := (-54256573895157436375111827456) }, { argument := 35725043723815130732810993664, coefficient := (-35725043723815130732810993664) }, { argument := 2007024928304220827686010880, coefficient := (-2007024928304220827686010880) }, { argument := 2502814381730340713772613632, coefficient := (-2502814381730340713772613632) }, { argument := 94037165869415486661563777024, coefficient := (-94037165869415486661563777024) }, { argument := 94030053639615833593817858048, coefficient := (-94030053639615833593817858048) }, { argument := 2509926611529993781518532608, coefficient := (-2509926611529993781518532608) }, { argument := 47763289462226525758433525760, coefficient := (-47763289462226525758433525760) }, { argument := 173725379620117158273692467200, coefficient := (-173725379620117158273692467200) }, { argument := 47763289462226525758433525760, coefficient := (-47763289462226525758433525760) }, { argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 648001128460562223343861760, coefficient := (-648001128460562223343861760) }, { argument := 54256573895157436375111827456, coefficient := (-54256573895157436375111827456) }, { argument := 54256593530563581334322675712, coefficient := (-54256593530563581334322675712) }, { argument := 647981493054417264133013504, coefficient := (-647981493054417264133013504) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 648001128460562223343861760, coefficient := (-648001128460562223343861760) }, { argument := 54256573895157436375111827456, coefficient := (-54256573895157436375111827456) }, { argument := 54256593530563581334322675712, coefficient := (-54256593530563581334322675712) }, { argument := 647981493054417264133013504, coefficient := (-647981493054417264133013504) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
