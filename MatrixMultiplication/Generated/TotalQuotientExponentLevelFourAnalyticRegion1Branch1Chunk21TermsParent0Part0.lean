import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 21, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-15584720322737288503186088062353408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    19239051, 287, 1345052493, 3003, 133, 2690104323,
    133, 259, 4893, 259, 3003, 4893,
    76956471, 259, 259, 287, 36537151792416483, 4404018675,
    3649044045, 132897631360194435, 24536675475, 18268328354054349, 98272531005, 98272531005,
    70338469695, 3649044045, 4576089907683423, 1811500641, 4576090112614305, 1811500641,
    1811500641, 6493133547, 453006765, 4404018675, 4404019725, 37640031,
    3649044045, 3649044915, 287, 36537153467775261, 4404019725, 3649044915,
    132897637311637629, 24536681325, 18268329191735091, 98272554435, 98272554435, 70338486465,
    3649044915, 133176745327271765, 6493133547, 133176751149211819, 6493133547, 1312336129,
    24536675475, 24536681325, 3003, 133, 36608187837709747, 453006765,
    36608189477159501, 453006765, 2624671613, 133
  ]
def negativeCoefficients : Array ℕ := #[
    363415398418478922472812969984, 44411098909363017362006081536, 12703661621286916177414645088256, 464691742246749620690258755584, 41161506306238894140395880448, 12703658490357938034839868407808,
    41161506306238894140395880448, 40078308771864186399859146752, 1514310153055841421270353707008, 40078308771864186399859146752, 464691742246749620690258755584, 1514310153055841421270353707008,
    363416659290329848668085026816, 40078308771864186399859146752, 40078308771864186399859146752, 44411098909363017362006081536, 10284293949844132678620936142848, 162479610787124883685480857600,
    8414122701476110047998115840, 37407357692012075058868896399360, 226310886453495373704776908800, 10284154596000129084498942885888, 226601028615615239568500981760, 226601028615615239568500981760,
    162189468625005017821756784640, 8414122701476110047998115840, 10304438401528475631660149243904, 33416288713887804000206585856, 10304438862991797537613692272640, 33416288713887804000206585856,
    33416288713887804000206585856, 119777172777926930332177661952, 33425999430456342108658728960, 162479610787124883685480857600, 162479649525287438475539251200, 355500041617148829605038129152,
    8414122701476110047998115840, 8414124707559528063911854080, 44411098909363017362006081536, 10284294421415705698164031881216, 162479649525287438475539251200, 8414124707559528063911854080,
    37407359367194409484811054874624, 226310940410221789305215385600, 10284155067572463775329017659392, 226601082641516945445350277120, 226601082641516945445350277120, 162189507293992282335404359680,
    8414124707559528063911854080, 37485921289394785326150283427840, 119777172777926930332177661952, 37485922928125226436635618443264, 119777172777926930332177661952, 12394664299696990022690372845568,
    226310886453495373704776908800, 226310940410221789305215385600, 464691742246749620690258755584, 41161506306238894140395880448, 10304288819038671267786529964032, 33425999430456342108658728960,
    10304289280502752593227238342656, 33425999430456342108658728960, 12394661253770608571769210011648, 41161506306238894140395880448
  ]
def negativeScales : Array ℕ := #[
    24, 8, 30, 11, 7, 31,
    7, 8, 12, 8, 11, 12,
    26, 8, 8, 8, 55, 32,
    31, 56, 34, 54, 36, 36,
    36, 31, 52, 30, 52, 30,
    30, 32, 28, 32, 32, 25,
    31, 31, 8, 55, 32, 31,
    56, 34, 54, 36, 36, 36,
    31, 56, 32, 56, 32, 30,
    34, 34, 11, 7, 55, 28,
    55, 28, 31, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24197534301606378, 8164906926675688, 30325015331536182, 11552188759558571, 7055282435501190, 31325014975971275,
    7055282435501190, 8016808287686554, 12256503567433041, 8016808287686554, 11552188759558571, 12256503567433041,
    26197539307036579, 8016808287686554, 8016808287686554, 8164906926675688, 55020213693074211, 32036173440570824,
    31764871419063614, 56883093007932235, 34514220737375902, 54020194144190956, 36516069161768297, 36516069161768297,
    36033594896469048, 31764871419063614, 52023036820727172, 30754538170523837, 52023036885335335, 30754538170523837,
    30754538170523837, 32596267736175374, 28754957354342950, 32036173440570824, 32036173784536126, 25165764480469481,
    31764871419063614, 31764871763028918, 8164906926675688, 55020213759226924, 32036173784536126, 31764871763028918,
    56883093072539240, 34514221081341203, 54020194210344673, 36516069505733599, 36516069505733599, 36033595240434350,
    31764871763028918, 56886119804523368, 32596267736175374, 56886119867592070, 32596267736175374, 30289490139135293,
    34514220737375902, 34514221081341203, 11552188759558571, 7055282435501190, 55023015877957253, 28754957354342950,
    55023015942566460, 28754957354342950, 31289489784600203, 7055282435501190
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
noncomputable def negativeCeiling : ℝ := 177137542493 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 363415398418478922472812969984, coefficient := (-363415398418478922472812969984) }, { argument := 44411098909363017362006081536, coefficient := (-44411098909363017362006081536) }, { argument := 12703661621286916177414645088256, coefficient := (-12703661621286916177414645088256) }, { argument := 464691742246749620690258755584, coefficient := (-464691742246749620690258755584) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }, { argument := 12703658490357938034839868407808, coefficient := (-12703658490357938034839868407808) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 1514310153055841421270353707008, coefficient := (-1514310153055841421270353707008) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 464691742246749620690258755584, coefficient := (-464691742246749620690258755584) }, { argument := 1514310153055841421270353707008, coefficient := (-1514310153055841421270353707008) }, { argument := 363416659290329848668085026816, coefficient := (-363416659290329848668085026816) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 44411098909363017362006081536, coefficient := (-44411098909363017362006081536) }, { argument := 10284293949844132678620936142848, coefficient := (-10284293949844132678620936142848) }, { argument := 162479610787124883685480857600, coefficient := (-162479610787124883685480857600) }, { argument := 8414122701476110047998115840, coefficient := (-8414122701476110047998115840) }, { argument := 37407357692012075058868896399360, coefficient := (-37407357692012075058868896399360) }, { argument := 226310886453495373704776908800, coefficient := (-226310886453495373704776908800) }, { argument := 10284154596000129084498942885888, coefficient := (-10284154596000129084498942885888) }, { argument := 226601028615615239568500981760, coefficient := (-226601028615615239568500981760) }, { argument := 226601028615615239568500981760, coefficient := (-226601028615615239568500981760) }, { argument := 162189468625005017821756784640, coefficient := (-162189468625005017821756784640) }, { argument := 8414122701476110047998115840, coefficient := (-8414122701476110047998115840) }, { argument := 10304438401528475631660149243904, coefficient := (-10304438401528475631660149243904) }, { argument := 33416288713887804000206585856, coefficient := (-33416288713887804000206585856) }, { argument := 10304438862991797537613692272640, coefficient := (-10304438862991797537613692272640) }, { argument := 33416288713887804000206585856, coefficient := (-33416288713887804000206585856) }, { argument := 33416288713887804000206585856, coefficient := (-33416288713887804000206585856) }, { argument := 119777172777926930332177661952, coefficient := (-119777172777926930332177661952) }, { argument := 33425999430456342108658728960, coefficient := (-33425999430456342108658728960) }, { argument := 162479610787124883685480857600, coefficient := (-162479610787124883685480857600) }, { argument := 162479649525287438475539251200, coefficient := (-162479649525287438475539251200) }, { argument := 355500041617148829605038129152, coefficient := (-355500041617148829605038129152) }, { argument := 8414122701476110047998115840, coefficient := (-8414122701476110047998115840) }, { argument := 8414124707559528063911854080, coefficient := (-8414124707559528063911854080) }, { argument := 44411098909363017362006081536, coefficient := (-44411098909363017362006081536) }, { argument := 10284294421415705698164031881216, coefficient := (-10284294421415705698164031881216) }, { argument := 162479649525287438475539251200, coefficient := (-162479649525287438475539251200) }, { argument := 8414124707559528063911854080, coefficient := (-8414124707559528063911854080) }, { argument := 37407359367194409484811054874624, coefficient := (-37407359367194409484811054874624) }, { argument := 226310940410221789305215385600, coefficient := (-226310940410221789305215385600) }, { argument := 10284155067572463775329017659392, coefficient := (-10284155067572463775329017659392) }, { argument := 226601082641516945445350277120, coefficient := (-226601082641516945445350277120) }, { argument := 226601082641516945445350277120, coefficient := (-226601082641516945445350277120) }, { argument := 162189507293992282335404359680, coefficient := (-162189507293992282335404359680) }, { argument := 8414124707559528063911854080, coefficient := (-8414124707559528063911854080) }, { argument := 37485921289394785326150283427840, coefficient := (-37485921289394785326150283427840) }, { argument := 119777172777926930332177661952, coefficient := (-119777172777926930332177661952) }, { argument := 37485922928125226436635618443264, coefficient := (-37485922928125226436635618443264) }, { argument := 119777172777926930332177661952, coefficient := (-119777172777926930332177661952) }, { argument := 12394664299696990022690372845568, coefficient := (-12394664299696990022690372845568) }, { argument := 226310886453495373704776908800, coefficient := (-226310886453495373704776908800) }, { argument := 226310940410221789305215385600, coefficient := (-226310940410221789305215385600) }, { argument := 464691742246749620690258755584, coefficient := (-464691742246749620690258755584) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }, { argument := 10304288819038671267786529964032, coefficient := (-10304288819038671267786529964032) }, { argument := 33425999430456342108658728960, coefficient := (-33425999430456342108658728960) }, { argument := 10304289280502752593227238342656, coefficient := (-10304289280502752593227238342656) }, { argument := 33425999430456342108658728960, coefficient := (-33425999430456342108658728960) }, { argument := 12394661253770608571769210011648, coefficient := (-12394661253770608571769210011648) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 39850993927031097802322358785015808
def positiveArguments : Array ℕ := #[
    3751, 63, 287, 7, 3003, 133,
    7, 133, 259, 4893, 259, 3003,
    4893, 63, 259, 259, 287, 105,
    525, 435, 7815, 2925, 105, 11715,
    11715, 8385, 435, 549, 603, 549,
    603, 3, 377, 3117416373, 3117416523, 8741090937,
    15845976183, 8740976793
  ]
def positiveCoefficients : Array ℕ := #[
    297184837591005530313383357710336, 77990222474978957318644826112, 88822197818726034724012163072, 69324642199981295394350956544, 929383484493499241380517511168, 82323012612477788280791760896,
    69324642199981295394350956544, 82323012612477788280791760896, 80156617543728372799718293504, 3028620306111682842540707414016, 80156617543728372799718293504, 929383484493499241380517511168,
    3028620306111682842540707414016, 77990222474978957318644826112, 80156617543728372799718293504, 80156617543728372799718293504, 88822197818726034724012163072, 32495926031241232216102010880,
    649918520624824644322040217600, 33656494818071276223819939840, 604656337938452928021040988160, 905243653727434326019984588800, 32495926031241232216102010880, 906404222514264370027702517760,
    906404222514264370027702517760, 648757951837994600314322288640, 33656494818071276223819939840, 339814540783836885459809599488, 373238921844542152882085953536, 339814540783836885459809599488,
    373238921844542152882085953536, 475368975085586025561263702016, 59738034535755310545532138553344, 117772660744034048111015953956864, 117772666410873827554590210392064, 41278634864604421529843533873152,
    149661013629899751099773522804736, 41278095834804600857060261756928
  ]
def positiveScales : Array ℕ := #[
    11, 5, 8, 2, 11, 7,
    2, 7, 8, 12, 8, 11,
    12, 5, 8, 8, 8, 6,
    9, 8, 12, 11, 6, 13,
    13, 13, 8, 9, 9, 9,
    9, 1, 8, 31, 31, 33,
    33, 33
  ]
def negativeArguments : Array ℕ := #[
    1811500641, 6493133547, 453006765, 98272531005, 98272554435, 259,
    98272531005, 98272554435, 4893, 259, 70338469695, 70338486465,
    3003, 4893, 75280323, 3649044045, 3649044915, 259,
    259, 287, 7, 15, 9, 3,
    377, 2973
  ]
def negativeCoefficients : Array ℕ := #[
    33416288713887804000206585856, 119777172777926930332177661952, 33425999430456342108658728960, 226601028615615239568500981760, 226601082641516945445350277120, 40078308771864186399859146752,
    226601028615615239568500981760, 226601082641516945445350277120, 1514310153055841421270353707008, 40078308771864186399859146752, 162189468625005017821756784640, 162189507293992282335404359680,
    464691742246749620690258755584, 1514310153055841421270353707008, 355501274154800858582438903808, 8414122701476110047998115840, 8414124707559528063911854080, 40078308771864186399859146752,
    40078308771864186399859146752, 44411098909363017362006081536, 8873554201597605810476922437632, 4753689750855860255612637020160, 1426106925256758076683791106048, 475368975085586025561263702016,
    59738034535755310545532138553344, 235545327154907875665606164348928
  ]
def negativeScales : Array ℕ := #[
    30, 32, 28, 36, 36, 8,
    36, 36, 12, 8, 36, 36,
    11, 12, 26, 31, 31, 8,
    8, 8, 2, 3, 3, 1,
    8, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11873059547496154, 5977279922488012, 8164906926675687, 2807354922011143, 11552188759557060, 7055282435501189,
    2807354922011143, 7055282435501189, 8016808287686553, 12256503567433040, 8016808287686553, 11552188759557060,
    12256503567433040, 5977279922488012, 8016808287686553, 8016808287686553, 8164906926675687, 6714245517659862,
    9036173612553484, 8764871590716857, 12932030157413262, 11514220909358101, 6714245517659862, 13516069333750468,
    13516069333750468, 13033595068451708, 8764871590716857, 9100662339005198, 9236014191900084, 9100662339005198,
    9236014191900084, 1584962500720924, 8558420713268557, 31537703713198676, 31537703782616496, 33025166201352940,
    33883397487598147, 33025147362050256
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30754538170523837, 32596267736175374, 28754957354342950, 36516069161768297, 36516069505733599, 8016808287686554,
    36516069161768297, 36516069505733599, 12256503567433041, 8016808287686554, 36033594896469048, 36033595240434350,
    11552188759558571, 12256503567433041, 26165769482361654, 31764871419063614, 31764871763028918, 8016808287686554,
    8016808287686554, 8164906926675688, 2807354922807594, 3906890600547867, 3169925001442313, 1584962500724866,
    8558420713270378, 11537703747908557
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 116999869449 / 500000000000
noncomputable def negativeCeiling : ℝ := 2544579067 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33416288713887804000206585856, coefficient := (-33416288713887804000206585856) }, { argument := 119777172777926930332177661952, coefficient := (-119777172777926930332177661952) }, { argument := 33425999430456342108658728960, coefficient := (-33425999430456342108658728960) }, { argument := 226601028615615239568500981760, coefficient := (-226601028615615239568500981760) }, { argument := 226601082641516945445350277120, coefficient := (-226601082641516945445350277120) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 226601028615615239568500981760, coefficient := (-226601028615615239568500981760) }, { argument := 226601082641516945445350277120, coefficient := (-226601082641516945445350277120) }, { argument := 1514310153055841421270353707008, coefficient := (-1514310153055841421270353707008) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 162189468625005017821756784640, coefficient := (-162189468625005017821756784640) }, { argument := 162189507293992282335404359680, coefficient := (-162189507293992282335404359680) }, { argument := 464691742246749620690258755584, coefficient := (-464691742246749620690258755584) }, { argument := 1514310153055841421270353707008, coefficient := (-1514310153055841421270353707008) }, { argument := 355501274154800858582438903808, coefficient := (-355501274154800858582438903808) }, { argument := 8414122701476110047998115840, coefficient := (-8414122701476110047998115840) }, { argument := 8414124707559528063911854080, coefficient := (-8414124707559528063911854080) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 40078308771864186399859146752, coefficient := (-40078308771864186399859146752) }, { argument := 44411098909363017362006081536, coefficient := (-44411098909363017362006081536) }, { argument := 297184837591005530313383357710336, coefficient := 297184837591005530313383357710336 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 88822197818726034724012163072, coefficient := 88822197818726034724012163072 }, { argument := 69324642199981295394350956544, coefficient := 69324642199981295394350956544 }, { argument := 929383484493499241380517511168, coefficient := 929383484493499241380517511168 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 69324642199981295394350956544, coefficient := 69324642199981295394350956544 }, { argument := 82323012612477788280791760896, coefficient := 82323012612477788280791760896 }, { argument := 80156617543728372799718293504, coefficient := 80156617543728372799718293504 }, { argument := 3028620306111682842540707414016, coefficient := 3028620306111682842540707414016 }, { argument := 80156617543728372799718293504, coefficient := 80156617543728372799718293504 }, { argument := 929383484493499241380517511168, coefficient := 929383484493499241380517511168 }, { argument := 3028620306111682842540707414016, coefficient := 3028620306111682842540707414016 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 80156617543728372799718293504, coefficient := 80156617543728372799718293504 }, { argument := 80156617543728372799718293504, coefficient := 80156617543728372799718293504 }, { argument := 88822197818726034724012163072, coefficient := 88822197818726034724012163072 }, { argument := 8873554201597605810476922437632, coefficient := (-8873554201597605810476922437632) }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 649918520624824644322040217600, coefficient := 649918520624824644322040217600 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 604656337938452928021040988160, coefficient := 604656337938452928021040988160 }, { argument := 905243653727434326019984588800, coefficient := 905243653727434326019984588800 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 906404222514264370027702517760, coefficient := 906404222514264370027702517760 }, { argument := 906404222514264370027702517760, coefficient := 906404222514264370027702517760 }, { argument := 648757951837994600314322288640, coefficient := 648757951837994600314322288640 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 4753689750855860255612637020160, coefficient := (-4753689750855860255612637020160) }, { argument := 339814540783836885459809599488, coefficient := 339814540783836885459809599488 }, { argument := 373238921844542152882085953536, coefficient := 373238921844542152882085953536 }, { argument := 339814540783836885459809599488, coefficient := 339814540783836885459809599488 }, { argument := 373238921844542152882085953536, coefficient := 373238921844542152882085953536 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 59738034535755310545532138553344, coefficient := 59738034535755310545532138553344 }, { argument := 59738034535755310545532138553344, coefficient := (-59738034535755310545532138553344) }, { argument := 117772660744034048111015953956864, coefficient := 117772660744034048111015953956864 }, { argument := 117772666410873827554590210392064, coefficient := 117772666410873827554590210392064 }, { argument := 235545327154907875665606164348928, coefficient := (-235545327154907875665606164348928) }, { argument := 41278634864604421529843533873152, coefficient := 41278634864604421529843533873152 }, { argument := 149661013629899751099773522804736, coefficient := 149661013629899751099773522804736 }, { argument := 41278095834804600857060261756928, coefficient := 41278095834804600857060261756928 }] }

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


end Parent0

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-23452536565763612497725052013248512)
def positiveArguments : Array ℕ := #[
    67860597, 1325024295, 41406999, 67860861
  ]
def positiveCoefficients : Array ℕ := #[
    640925217560648794759206273024, 25029001278783924904710666977280, 25028995101928565311214727462912, 640927710970151749931879104512
  ]
def positiveScales : Array ℕ := #[
    26, 30, 25, 26
  ]
def negativeArguments : Array ℕ := #[
    2931, 81
  ]
def negativeCoefficients : Array ℕ := #[
    232217744329308773486677318434816, 51339849309243290760616479817728
  ]
def negativeScales : Array ℕ := #[
    11, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    26016070786349297, 30303371666458085, 25303371310418322, 26016076398895705
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11517177252690018, 6339850002884626
  ]

abbrev PositiveTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 17154376759 / 1000000000000
noncomputable def negativeCeiling : ℝ := 36110944109 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 232217744329308773486677318434816, coefficient := (-232217744329308773486677318434816) }, { argument := 640925217560648794759206273024, coefficient := 640925217560648794759206273024 }, { argument := 25029001278783924904710666977280, coefficient := 25029001278783924904710666977280 }, { argument := 25028995101928565311214727462912, coefficient := 25028995101928565311214727462912 }, { argument := 640927710970151749931879104512, coefficient := 640927710970151749931879104512 }, { argument := 51339849309243290760616479817728, coefficient := (-51339849309243290760616479817728) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
