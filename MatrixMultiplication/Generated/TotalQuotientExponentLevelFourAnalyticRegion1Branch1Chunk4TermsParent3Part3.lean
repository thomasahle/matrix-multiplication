import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1415079319948115529863313934516224)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    54164233035, 576059395923, 27082198143, 84074265, 1177371783, 184310949333,
    46077754233, 4709554731, 2747525, 1770072975, 18825470455, 885039155,
    2747525, 37007659017, 5793341461467, 1448335896567, 148032760869, 38552218451,
    138186372817, 9640855415, 1177371783, 184310949333, 46077754233, 4709554731,
    78459307199, 281229135733, 19620526835, 8598320125, 8598326275, 11810928293,
    491728505945, 5274115, 10060078999031, 205485, 342475, 10479735,
    342475, 205485, 167881245, 10753715, 491729325401, 10479735,
    342475, 10753715, 342475, 10479735, 342475, 11810928293,
    14484872808775, 5409495, 140660145144827, 61050015, 5409495, 281320368077507,
    5409495, 5409495, 224262207, 1391013, 61050015, 224262207,
    14485048668487, 5409495, 1391013, 5409495
  ]
def negativeCoefficients : Array ℕ := #[
    249788436186352342658596208640, 2656605061961826122417037115392, 249789189048706536948098924544, 775448224820118187797381120, 5429668990152024552565112832, 212496057020518699078420267008,
    212496134956859488996668997632, 5429746926492814470813843456, 810926248177901372860006400, 261216665292917482518793420800, 2778149084404524049586444042240, 261217452599954548442456391680,
    810926248177901372860006400, 170667703663427150125222330368, 6679267954455763433194669473792, 6679270404184529343327730925568, 170670153392193060258283782144, 88895363404917534978161508352,
    318636081728676678472810102784, 88921196246070944917167800320, 5429668990152024552565112832, 212496057020518699078420267008, 212496134956859488996668997632, 5429746926492814470813843456,
    90457422506281900608768180224, 324235118308573553014664593408, 90483709279148868869386403840, 9913188175606332566536192000, 9913195266073585898645094400, 106383384518508896799686656,
    17716386529130821816428789760, 778321996962501214569758720, 181226272125415055961047957504, 485187738366234523368161280, 25270194706574714758758400, 773267958021186271618007040,
    808646230610390872280268800, 485187738366234523368161280, 12387449445162925174743367680, 793484113786446043425013760, 17716416053144711788566151168, 773267958021186271618007040,
    25270194706574714758758400, 793484113786446043425013760, 25270194706574714758758400, 773267958021186271618007040, 808646230610390872280268800, 106383384518508896799686656,
    8154258473013514970385612800, 99787569833011450918993920, 316738488630061379657553412096, 1126174002401129231800074240, 99787569833011450918993920, 316738576211397825845283258368,
    99787569833011450918993920, 99787569833011450918993920, 4136907537934274722384576512, 102638643256811778088108032, 1126174002401129231800074240, 4136907537934274722384576512,
    8154357473230194055728594944, 99787569833011450918993920, 102638643256811778088108032, 99787569833011450918993920
  ]
def negativeScales : Array ℕ := #[
    35, 39, 34, 26, 30, 37,
    35, 32, 21, 30, 34, 29,
    21, 35, 42, 40, 37, 35,
    37, 33, 30, 37, 35, 32,
    36, 38, 34, 33, 33, 33,
    38, 22, 43, 17, 18, 23,
    18, 17, 27, 23, 38, 23,
    18, 23, 18, 23, 18, 33,
    43, 22, 46, 25, 22, 47,
    22, 22, 27, 20, 25, 27,
    43, 22, 20, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35656621441503757, 39067426615473308, 34656625789780103, 26325160925587658, 30132922811402374, 37423350823244004,
    35423351352375477, 32132943519398684, 21389701177782373, 30721161693791430, 34131966867668019, 29721166042067786,
    21389701177782373, 35107104827246643, 42397532839088262, 40397533368219735, 37107125535242953, 35166094829926207,
    37007824395820893, 33166514013743051, 30132922811402374, 37423350823244004, 35423351352375477, 32132943519398684,
    36191225545249889, 38032955111144575, 34191644729066733, 33001407678444764, 33001408710340669, 33459403308280779,
    38839071037080442, 22330497598266673, 43193706867810639, 17648673558313525, 18385639152459137, 23321098900264423,
    18385639152459137, 17648673558313525, 27322865826438611, 23358331806463399, 38839073441301756, 23321098900264423,
    18385639152459137, 23358331806463399, 18385639152459137, 23321098900264423, 18385639152459137, 33459403308280779,
    43719612250052681, 22367062487775201, 46999206962913704, 25863488316130512, 22367062487775201, 47999207361833299,
    22367062487775201, 22367062487775201, 27740611275079887, 20407704472272554, 25863488316130512, 27740611275079887,
    43719629765594465, 22367062487775201, 20407704472272554, 22367062487775201
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
noncomputable def negativeCeiling : ℝ := 10917898027 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 249788436186352342658596208640, coefficient := (-249788436186352342658596208640) }, { argument := 2656605061961826122417037115392, coefficient := (-2656605061961826122417037115392) }, { argument := 249789189048706536948098924544, coefficient := (-249789189048706536948098924544) }, { argument := 775448224820118187797381120, coefficient := (-775448224820118187797381120) }, { argument := 5429668990152024552565112832, coefficient := (-5429668990152024552565112832) }, { argument := 212496057020518699078420267008, coefficient := (-212496057020518699078420267008) }, { argument := 212496134956859488996668997632, coefficient := (-212496134956859488996668997632) }, { argument := 5429746926492814470813843456, coefficient := (-5429746926492814470813843456) }, { argument := 810926248177901372860006400, coefficient := (-810926248177901372860006400) }, { argument := 261216665292917482518793420800, coefficient := (-261216665292917482518793420800) }, { argument := 2778149084404524049586444042240, coefficient := (-2778149084404524049586444042240) }, { argument := 261217452599954548442456391680, coefficient := (-261217452599954548442456391680) }, { argument := 810926248177901372860006400, coefficient := (-810926248177901372860006400) }, { argument := 170667703663427150125222330368, coefficient := (-170667703663427150125222330368) }, { argument := 6679267954455763433194669473792, coefficient := (-6679267954455763433194669473792) }, { argument := 6679270404184529343327730925568, coefficient := (-6679270404184529343327730925568) }, { argument := 170670153392193060258283782144, coefficient := (-170670153392193060258283782144) }, { argument := 88895363404917534978161508352, coefficient := (-88895363404917534978161508352) }, { argument := 318636081728676678472810102784, coefficient := (-318636081728676678472810102784) }, { argument := 88921196246070944917167800320, coefficient := (-88921196246070944917167800320) }, { argument := 5429668990152024552565112832, coefficient := (-5429668990152024552565112832) }, { argument := 212496057020518699078420267008, coefficient := (-212496057020518699078420267008) }, { argument := 212496134956859488996668997632, coefficient := (-212496134956859488996668997632) }, { argument := 5429746926492814470813843456, coefficient := (-5429746926492814470813843456) }, { argument := 90457422506281900608768180224, coefficient := (-90457422506281900608768180224) }, { argument := 324235118308573553014664593408, coefficient := (-324235118308573553014664593408) }, { argument := 90483709279148868869386403840, coefficient := (-90483709279148868869386403840) }, { argument := 9913188175606332566536192000, coefficient := (-9913188175606332566536192000) }, { argument := 9913195266073585898645094400, coefficient := (-9913195266073585898645094400) }, { argument := 106383384518508896799686656, coefficient := (-106383384518508896799686656) }, { argument := 17716386529130821816428789760, coefficient := (-17716386529130821816428789760) }, { argument := 778321996962501214569758720, coefficient := (-778321996962501214569758720) }, { argument := 181226272125415055961047957504, coefficient := (-181226272125415055961047957504) }, { argument := 485187738366234523368161280, coefficient := (-485187738366234523368161280) }, { argument := 25270194706574714758758400, coefficient := (-25270194706574714758758400) }, { argument := 773267958021186271618007040, coefficient := (-773267958021186271618007040) }, { argument := 808646230610390872280268800, coefficient := (-808646230610390872280268800) }, { argument := 485187738366234523368161280, coefficient := (-485187738366234523368161280) }, { argument := 12387449445162925174743367680, coefficient := (-12387449445162925174743367680) }, { argument := 793484113786446043425013760, coefficient := (-793484113786446043425013760) }, { argument := 17716416053144711788566151168, coefficient := (-17716416053144711788566151168) }, { argument := 773267958021186271618007040, coefficient := (-773267958021186271618007040) }, { argument := 25270194706574714758758400, coefficient := (-25270194706574714758758400) }, { argument := 793484113786446043425013760, coefficient := (-793484113786446043425013760) }, { argument := 25270194706574714758758400, coefficient := (-25270194706574714758758400) }, { argument := 773267958021186271618007040, coefficient := (-773267958021186271618007040) }, { argument := 808646230610390872280268800, coefficient := (-808646230610390872280268800) }, { argument := 106383384518508896799686656, coefficient := (-106383384518508896799686656) }, { argument := 8154258473013514970385612800, coefficient := (-8154258473013514970385612800) }, { argument := 99787569833011450918993920, coefficient := (-99787569833011450918993920) }, { argument := 316738488630061379657553412096, coefficient := (-316738488630061379657553412096) }, { argument := 1126174002401129231800074240, coefficient := (-1126174002401129231800074240) }, { argument := 99787569833011450918993920, coefficient := (-99787569833011450918993920) }, { argument := 316738576211397825845283258368, coefficient := (-316738576211397825845283258368) }, { argument := 99787569833011450918993920, coefficient := (-99787569833011450918993920) }, { argument := 99787569833011450918993920, coefficient := (-99787569833011450918993920) }, { argument := 4136907537934274722384576512, coefficient := (-4136907537934274722384576512) }, { argument := 102638643256811778088108032, coefficient := (-102638643256811778088108032) }, { argument := 1126174002401129231800074240, coefficient := (-1126174002401129231800074240) }, { argument := 4136907537934274722384576512, coefficient := (-4136907537934274722384576512) }, { argument := 8154357473230194055728594944, coefficient := (-8154357473230194055728594944) }, { argument := 99787569833011450918993920, coefficient := (-99787569833011450918993920) }, { argument := 102638643256811778088108032, coefficient := (-102638643256811778088108032) }, { argument := 99787569833011450918993920, coefficient := (-99787569833011450918993920) }] }

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
def constantNumerator : ℤ := 55313238452954590868873491964231680
def positiveArguments : Array ℕ := #[
    6851, 1581, 1785, 765, 20145, 1785,
    765, 1785, 1785, 74001, 459, 20145,
    74001, 1581, 1785, 459, 1785, 6393,
    185397, 164087, 10655, 6393, 10655, 326043,
    10655, 6393, 5223081, 334567, 185397, 326043,
    10655, 334567, 10655, 326043, 10655, 6393,
    56917, 42385, 44807, 3633, 778673, 1408393,
    42385, 778673, 23009
  ]
def positiveCoefficients : Array ℕ := #[
    542792141385224976853369603751936, 61161975065943319206734856192, 69053842816387618459216773120, 59189008128332244393614376960, 779321940356374551182589296640, 69053842816387618459216773120,
    59189008128332244393614376960, 69053842816387618459216773120, 69053842816387618459216773120, 2862775026473669553837815365632, 71026809753998693272337252352, 779321940356374551182589296640,
    2862775026473669553837815365632, 61161975065943319206734856192, 69053842816387618459216773120, 71026809753998693272337252352, 69053842816387618459216773120, 247317208473482378044690661376,
    3586099522865494481648014589952, 6347808350819381036480393641984, 206097673727901981703908884480, 3957075335575718048715050582016, 206097673727901981703908884480, 6306588816073800640139611865088,
    6595125559292863414525084303360, 3957075335575718048715050582016, 101029079661417551431256135172096, 6471466955056122225502738972672, 3586099522865494481648014589952, 6306588816073800640139611865088,
    206097673727901981703908884480, 6471466955056122225502738972672, 206097673727901981703908884480, 6306588816073800640139611865088, 6595125559292863414525084303360, 247317208473482378044690661376,
    1100934894000093579788022710272, 819845133829856921118740316160, 866693427191563030896954048512, 1124359040680946634677129576448, 15061726315788514293695714951168, 27242282589832102836031285362688,
    819845133829856921118740316160, 15061726315788514293695714951168, 890117573872416085786060914688
  ]
def positiveScales : Array ℕ := #[
    12, 10, 10, 9, 14, 10,
    9, 10, 10, 16, 8, 14,
    16, 10, 10, 8, 10, 12,
    17, 17, 13, 12, 13, 18,
    13, 12, 22, 18, 17, 18,
    13, 18, 13, 18, 13, 12,
    15, 15, 15, 11, 19, 20,
    15, 19, 14
  ]
def negativeArguments : Array ℕ := #[
    94292140547, 679835991963, 188619832415, 95462577, 14944131027, 3736034127,
    381855789, 11701152565, 41941550855, 2926138225, 4269799945, 4269802999,
    3818270837, 13686190279, 954845105, 8598320125, 8598326275, 51,
    2131
  ]
def negativeCoefficients : Array ℕ := #[
    6794464784502970189969620992, 24493672960620946507834589184, 6795745655831035221083422720, 7043894906143166987111497728, 275670560459051285290923589632, 275670661565655553292975996928,
    7043996012747434989163905024, 107924083366992534478279147520, 386842527338329513800855715840, 107955445921747473062376243200, 9845488353919264929496432640, 9845495395963815068117762048,
    4402166558390484958982438912, 15779103088800282799771746304, 4403445820492331138070609920, 9913188175606332566536192000, 9913195266073585898645094400, 8081272576454962434541482934272,
    168835214317897303411842158166016
  ]
def negativeScales : Array ℕ := #[
    36, 39, 37, 26, 33, 31,
    28, 33, 35, 31, 31, 31,
    31, 33, 29, 33, 33, 5,
    11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12742098869766579, 10626621652357647, 10801708358875019, 9579315937579817, 14298134185035960, 10801708358875019,
    9579315937579817, 10801708358875019, 10801708358875019, 16175257146038239, 8842350343321225, 14298134185035960,
    16175257146038239, 10626621652357647, 10801708358875019, 8842350343321225, 10801708358875019, 12642277378502772,
    17500258373631414, 17324101418477604, 13379242972670065, 12642277378502772, 13379242972670065, 18314702720475354,
    13379242972670065, 12642277378502772, 22316469646649542, 18351935626674330, 17500258373631414, 18314702720475354,
    13379242972670065, 18351935626674330, 13379242972670065, 18314702720475354, 13379242972670065, 12642277378502772,
    15796572001334644, 15371266166639294, 15451436515323275, 11826945650346870, 19570658077022122, 20425618531167545,
    15371266166639294, 19570658077022122, 14489910663137901
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36456418473046478, 39306395787005659, 37456690419787348, 26508431946494939, 33798859958967373, 31798860488098854,
    28508452654491249, 33445931591324576, 35287661157219222, 31446350775141421, 31991521350796885, 31991522382693134,
    31830272294563334, 33672001859312080, 29830691478389925, 33001407678444764, 33001408710340669, 5672425342008812,
    11057314877782704
  ]

abbrev PositiveTerm := Fin 45
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 70028497991 / 500000000000
noncomputable def negativeCeiling : ℝ := 11768531423 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6794464784502970189969620992, coefficient := (-6794464784502970189969620992) }, { argument := 24493672960620946507834589184, coefficient := (-24493672960620946507834589184) }, { argument := 6795745655831035221083422720, coefficient := (-6795745655831035221083422720) }, { argument := 7043894906143166987111497728, coefficient := (-7043894906143166987111497728) }, { argument := 275670560459051285290923589632, coefficient := (-275670560459051285290923589632) }, { argument := 275670661565655553292975996928, coefficient := (-275670661565655553292975996928) }, { argument := 7043996012747434989163905024, coefficient := (-7043996012747434989163905024) }, { argument := 107924083366992534478279147520, coefficient := (-107924083366992534478279147520) }, { argument := 386842527338329513800855715840, coefficient := (-386842527338329513800855715840) }, { argument := 107955445921747473062376243200, coefficient := (-107955445921747473062376243200) }, { argument := 9845488353919264929496432640, coefficient := (-9845488353919264929496432640) }, { argument := 9845495395963815068117762048, coefficient := (-9845495395963815068117762048) }, { argument := 4402166558390484958982438912, coefficient := (-4402166558390484958982438912) }, { argument := 15779103088800282799771746304, coefficient := (-15779103088800282799771746304) }, { argument := 4403445820492331138070609920, coefficient := (-4403445820492331138070609920) }, { argument := 9913188175606332566536192000, coefficient := (-9913188175606332566536192000) }, { argument := 9913195266073585898645094400, coefficient := (-9913195266073585898645094400) }, { argument := 542792141385224976853369603751936, coefficient := 542792141385224976853369603751936 }, { argument := 61161975065943319206734856192, coefficient := 61161975065943319206734856192 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 779321940356374551182589296640, coefficient := 779321940356374551182589296640 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 2862775026473669553837815365632, coefficient := 2862775026473669553837815365632 }, { argument := 71026809753998693272337252352, coefficient := 71026809753998693272337252352 }, { argument := 779321940356374551182589296640, coefficient := 779321940356374551182589296640 }, { argument := 2862775026473669553837815365632, coefficient := 2862775026473669553837815365632 }, { argument := 61161975065943319206734856192, coefficient := 61161975065943319206734856192 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 71026809753998693272337252352, coefficient := 71026809753998693272337252352 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 8081272576454962434541482934272, coefficient := (-8081272576454962434541482934272) }, { argument := 247317208473482378044690661376, coefficient := 247317208473482378044690661376 }, { argument := 3586099522865494481648014589952, coefficient := 3586099522865494481648014589952 }, { argument := 6347808350819381036480393641984, coefficient := 6347808350819381036480393641984 }, { argument := 206097673727901981703908884480, coefficient := 206097673727901981703908884480 }, { argument := 3957075335575718048715050582016, coefficient := 3957075335575718048715050582016 }, { argument := 206097673727901981703908884480, coefficient := 206097673727901981703908884480 }, { argument := 6306588816073800640139611865088, coefficient := 6306588816073800640139611865088 }, { argument := 6595125559292863414525084303360, coefficient := 6595125559292863414525084303360 }, { argument := 3957075335575718048715050582016, coefficient := 3957075335575718048715050582016 }, { argument := 101029079661417551431256135172096, coefficient := 101029079661417551431256135172096 }, { argument := 6471466955056122225502738972672, coefficient := 6471466955056122225502738972672 }, { argument := 3586099522865494481648014589952, coefficient := 3586099522865494481648014589952 }, { argument := 6306588816073800640139611865088, coefficient := 6306588816073800640139611865088 }, { argument := 206097673727901981703908884480, coefficient := 206097673727901981703908884480 }, { argument := 6471466955056122225502738972672, coefficient := 6471466955056122225502738972672 }, { argument := 206097673727901981703908884480, coefficient := 206097673727901981703908884480 }, { argument := 6306588816073800640139611865088, coefficient := 6306588816073800640139611865088 }, { argument := 6595125559292863414525084303360, coefficient := 6595125559292863414525084303360 }, { argument := 247317208473482378044690661376, coefficient := 247317208473482378044690661376 }, { argument := 168835214317897303411842158166016, coefficient := (-168835214317897303411842158166016) }, { argument := 1100934894000093579788022710272, coefficient := 1100934894000093579788022710272 }, { argument := 819845133829856921118740316160, coefficient := 819845133829856921118740316160 }, { argument := 866693427191563030896954048512, coefficient := 866693427191563030896954048512 }, { argument := 1124359040680946634677129576448, coefficient := 1124359040680946634677129576448 }, { argument := 15061726315788514293695714951168, coefficient := 15061726315788514293695714951168 }, { argument := 27242282589832102836031285362688, coefficient := 27242282589832102836031285362688 }, { argument := 819845133829856921118740316160, coefficient := 819845133829856921118740316160 }, { argument := 15061726315788514293695714951168, coefficient := 15061726315788514293695714951168 }, { argument := 890117573872416085786060914688, coefficient := 890117573872416085786060914688 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
