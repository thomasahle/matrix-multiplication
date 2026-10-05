import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3

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
def constantNumerator : ℤ := (-123764431975789260094213007081472)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    41750613225, 496513815, 108471639, 6575948781, 295137, 65255782095,
    302853, 9645, 295137, 167823, 302853, 4727979,
    5787, 6575948781, 295137, 9645, 5787, 9645,
    148533, 167823, 108471639, 37709145, 3170933415, 1585466325,
    18854955, 80431243, 4498546537, 148257, 43588042915, 152133,
    4845, 148257, 84303, 152133, 2375019, 2907,
    4498546537, 148257, 4845, 2907, 4845, 74613,
    84303, 80431243, 238650497, 8574630527, 68597071479, 1909180809,
    371457267591, 157669191, 2089496359033, 213331437, 7423443, 213257709,
    158400873, 372299057031, 157669191, 902241, 1287137301565, 78679308086211,
    21566125, 19101425, 894069925, 243389125
  ]
def negativeCoefficients : Array ℕ := #[
    192540719270502095126947430400, 2289765818591542668699893760, 500237140972202968435654656, 60652422102464650048645890048, 2787490153309396958869192704, 601878355818111559286925557760,
    2860365712873041323806949376, 91094449454555456172195840, 2787490153309396958869192704, 1585043420509264937396207616, 2860365712873041323806949376, 44654499122623084615610400768,
    1749013429527464758506160128, 60652422102464650048645890048, 2787490153309396958869192704, 91094449454555456172195840, 1749013429527464758506160128, 91094449454555456172195840,
    2805709043200308050103631872, 1585043420509264937396207616, 500237140972202968435654656, 173902736763351042443182080, 14623349295319710055960412160, 14623345767379905959008665600,
    173906264703155139394928640, 370923638787835714361884672, 41491768335855688082989776896, 2800495550603219961787711488, 402028736163436929541807800320, 2873711120553630941180854272,
    91519462438013724241428480, 2800495550603219961787711488, 1592438646421438801800855552, 2873711120553630941180854272, 44862840487114327623148240896, 1757173678809863505435426816,
    41491768335855688082989776896, 2800495550603219961787711488, 91519462438013724241428480, 1757173678809863505435426816, 91519462438013724241428480, 2818799443090822706635997184,
    1592438646421438801800855552, 370923638787835714361884672, 4402324641222589126805553152, 158174014858186259418035781632, 158174077722384219610973995008, 4402271221757594673157767168,
    209111851488361277546299392, 363560401835728671533432832, 2352563755983256730931822592, 491908802651961570858369024, 17117294145846331872116736, 491738797458578263630675968,
    365247545660396165551620096, 209585736814399829858844672, 363560401835728671533432832, 16643408819807779559571456, 724593883962849967241953280, 44292512822353539046500728832,
    198912394268314701922304000, 176179549209078735988326400, 8246339545237846642550374400, 2244868449599551635980288000
  ]
def negativeScales : Array ℕ := #[
    35, 28, 26, 32, 18, 35,
    18, 13, 18, 17, 18, 22,
    12, 32, 18, 13, 12, 13,
    17, 17, 26, 25, 31, 30,
    24, 26, 32, 17, 35, 17,
    12, 17, 16, 17, 21, 11,
    32, 17, 12, 11, 12, 16,
    16, 26, 27, 32, 35, 30,
    38, 27, 40, 27, 22, 27,
    27, 38, 27, 19, 40, 46,
    24, 24, 29, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35281078336644010, 28887258622426125, 26692742644017880, 32614551916140023, 18171025270741756, 35925386695404267,
    18208258176940731, 13235565522936466, 18171025270741756, 17356580923897833, 18208258176940731, 22172792196915944,
    12498599928770519, 32614551916140023, 18171025270741756, 13235565522936466, 12498599928770519, 13235565522936466,
    17180423968744005, 17356580923897833, 26692742644017880, 25168411104050864, 31562260437245805, 30562260089189982,
    24168440371500750, 26261252680113903, 32066811801522684, 17177740698107733, 35343213377612344, 17214973604306709,
    12242280950302444, 17177740698107733, 16363296351263811, 17214973604306709, 21179507624281921, 11505315356136561,
    32066811801522684, 17177740698107733, 12242280950302444, 11505315356136561, 12242280950302444, 16187139396109983,
    16363296351263811, 26261252680113903, 27830324101151146, 32997427384922505, 35997427958302915, 30830306594839619,
    38434405296569274, 27232325540128637, 40926292390347037, 27668521339260892, 22823657035773748, 27668022653243586,
    27239005045711498, 38437671005858519, 27232325540128637, 19783153321970993, 40227303095642494, 46161049504001909,
    24362263640640428, 24187176934082336, 29735812427926609, 27858689468802668
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
noncomputable def negativeCeiling : ℝ := 200824259 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 192540719270502095126947430400, coefficient := (-192540719270502095126947430400) }, { argument := 2289765818591542668699893760, coefficient := (-2289765818591542668699893760) }, { argument := 500237140972202968435654656, coefficient := (-500237140972202968435654656) }, { argument := 60652422102464650048645890048, coefficient := (-60652422102464650048645890048) }, { argument := 2787490153309396958869192704, coefficient := (-2787490153309396958869192704) }, { argument := 601878355818111559286925557760, coefficient := (-601878355818111559286925557760) }, { argument := 2860365712873041323806949376, coefficient := (-2860365712873041323806949376) }, { argument := 91094449454555456172195840, coefficient := (-91094449454555456172195840) }, { argument := 2787490153309396958869192704, coefficient := (-2787490153309396958869192704) }, { argument := 1585043420509264937396207616, coefficient := (-1585043420509264937396207616) }, { argument := 2860365712873041323806949376, coefficient := (-2860365712873041323806949376) }, { argument := 44654499122623084615610400768, coefficient := (-44654499122623084615610400768) }, { argument := 1749013429527464758506160128, coefficient := (-1749013429527464758506160128) }, { argument := 60652422102464650048645890048, coefficient := (-60652422102464650048645890048) }, { argument := 2787490153309396958869192704, coefficient := (-2787490153309396958869192704) }, { argument := 91094449454555456172195840, coefficient := (-91094449454555456172195840) }, { argument := 1749013429527464758506160128, coefficient := (-1749013429527464758506160128) }, { argument := 91094449454555456172195840, coefficient := (-91094449454555456172195840) }, { argument := 2805709043200308050103631872, coefficient := (-2805709043200308050103631872) }, { argument := 1585043420509264937396207616, coefficient := (-1585043420509264937396207616) }, { argument := 500237140972202968435654656, coefficient := (-500237140972202968435654656) }, { argument := 173902736763351042443182080, coefficient := (-173902736763351042443182080) }, { argument := 14623349295319710055960412160, coefficient := (-14623349295319710055960412160) }, { argument := 14623345767379905959008665600, coefficient := (-14623345767379905959008665600) }, { argument := 173906264703155139394928640, coefficient := (-173906264703155139394928640) }, { argument := 370923638787835714361884672, coefficient := (-370923638787835714361884672) }, { argument := 41491768335855688082989776896, coefficient := (-41491768335855688082989776896) }, { argument := 2800495550603219961787711488, coefficient := (-2800495550603219961787711488) }, { argument := 402028736163436929541807800320, coefficient := (-402028736163436929541807800320) }, { argument := 2873711120553630941180854272, coefficient := (-2873711120553630941180854272) }, { argument := 91519462438013724241428480, coefficient := (-91519462438013724241428480) }, { argument := 2800495550603219961787711488, coefficient := (-2800495550603219961787711488) }, { argument := 1592438646421438801800855552, coefficient := (-1592438646421438801800855552) }, { argument := 2873711120553630941180854272, coefficient := (-2873711120553630941180854272) }, { argument := 44862840487114327623148240896, coefficient := (-44862840487114327623148240896) }, { argument := 1757173678809863505435426816, coefficient := (-1757173678809863505435426816) }, { argument := 41491768335855688082989776896, coefficient := (-41491768335855688082989776896) }, { argument := 2800495550603219961787711488, coefficient := (-2800495550603219961787711488) }, { argument := 91519462438013724241428480, coefficient := (-91519462438013724241428480) }, { argument := 1757173678809863505435426816, coefficient := (-1757173678809863505435426816) }, { argument := 91519462438013724241428480, coefficient := (-91519462438013724241428480) }, { argument := 2818799443090822706635997184, coefficient := (-2818799443090822706635997184) }, { argument := 1592438646421438801800855552, coefficient := (-1592438646421438801800855552) }, { argument := 370923638787835714361884672, coefficient := (-370923638787835714361884672) }, { argument := 4402324641222589126805553152, coefficient := (-4402324641222589126805553152) }, { argument := 158174014858186259418035781632, coefficient := (-158174014858186259418035781632) }, { argument := 158174077722384219610973995008, coefficient := (-158174077722384219610973995008) }, { argument := 4402271221757594673157767168, coefficient := (-4402271221757594673157767168) }, { argument := 209111851488361277546299392, coefficient := (-209111851488361277546299392) }, { argument := 363560401835728671533432832, coefficient := (-363560401835728671533432832) }, { argument := 2352563755983256730931822592, coefficient := (-2352563755983256730931822592) }, { argument := 491908802651961570858369024, coefficient := (-491908802651961570858369024) }, { argument := 17117294145846331872116736, coefficient := (-17117294145846331872116736) }, { argument := 491738797458578263630675968, coefficient := (-491738797458578263630675968) }, { argument := 365247545660396165551620096, coefficient := (-365247545660396165551620096) }, { argument := 209585736814399829858844672, coefficient := (-209585736814399829858844672) }, { argument := 363560401835728671533432832, coefficient := (-363560401835728671533432832) }, { argument := 16643408819807779559571456, coefficient := (-16643408819807779559571456) }, { argument := 724593883962849967241953280, coefficient := (-724593883962849967241953280) }, { argument := 44292512822353539046500728832, coefficient := (-44292512822353539046500728832) }, { argument := 198912394268314701922304000, coefficient := (-198912394268314701922304000) }, { argument := 176179549209078735988326400, coefficient := (-176179549209078735988326400) }, { argument := 8246339545237846642550374400, coefficient := (-8246339545237846642550374400) }, { argument := 2244868449599551635980288000, coefficient := (-2244868449599551635980288000) }] }

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
def constantNumerator : ℤ := (-76408764175977839457687710990336)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    39339659074851, 894069925, 21566125, 21566125, 9242625, 21566125,
    243389125, 9242625, 643563619037, 19101425, 372785424263, 39312570136789,
    14229, 419890185176695, 14601, 465, 14229, 8091,
    14601, 227943, 279, 19656298707155, 14229, 465,
    279, 465, 7161, 8091, 372785424263, 77932233,
    6553262391, 3276630405, 38966907, 79978629, 4250966343, 170289,
    40517219565, 174741, 5565, 170289, 96831, 174741,
    2727963, 3339, 4250966343, 170289, 5565, 3339,
    5565, 85701, 96831, 79978629, 255488383, 9184841089,
    73478757769, 2043882103, 457971, 25175649, 14229, 242609355,
    14601, 465, 14229, 8091
  ]
def negativeCoefficients : Array ℕ := #[
    44292518487595328752293249024, 8246339545237846642550374400, 198912394268314701922304000, 198912394268314701922304000, 170496337944269744504832000, 198912394268314701922304000,
    2244868449599551635980288000, 170496337944269744504832000, 724588218721060261449433088, 176179549209078735988326400, 209859537224999882306093056, 22131009527377428670387847168,
    134389105369504363491360768, 236377160187286520642498723840, 137902546032759379530350592, 4391800829068770048737280, 134389105369504363491360768, 76417334425796598848028672,
    137902546032759379530350592, 2152860766409511077891014656, 84322575918120384935755776, 22131024883256605069247774720, 134389105369504363491360768, 4391800829068770048737280,
    84322575918120384935755776, 4391800829068770048737280, 135267465535318117501108224, 76417334425796598848028672, 209859537224999882306093056, 179699494655462743857954816,
    15110794271830367057825759232, 15110790626292569490975621120, 179703140193260310708092928, 368836325132291220613103616, 39208244097637007538618630144, 3216668264005556055180312576,
    373705389946926223431586283520, 3300764166332498697145810944, 105119877908678302456872960, 3216668264005556055180312576, 1829085875611002462749589504, 3300764166332498697145810944,
    51529764150834103864359124992, 2018301655846623407171960832, 39208244097637007538618630144, 3216668264005556055180312576, 105119877908678302456872960, 2018301655846623407171960832,
    105119877908678302456872960, 3237692239587291715671687168, 1829085875611002462749589504, 368836325132291220613103616, 4712928815006886154026876928, 169430412926474734334403149824,
    169430479927355053056708313088, 4712871258859533171012141056, 16896147660361674126262272, 1857635015970167197727195136, 134389105369504363491360768, 17901410726290987099587870720,
    137902546032759379530350592, 4391800829068770048737280, 134389105369504363491360768, 76417334425796598848028672
  ]
def negativeScales : Array ℕ := #[
    45, 29, 24, 24, 23, 24,
    27, 23, 39, 24, 38, 45,
    13, 48, 13, 8, 13, 12,
    13, 17, 8, 44, 13, 8,
    8, 8, 12, 12, 38, 26,
    32, 31, 25, 26, 31, 17,
    35, 17, 12, 17, 16, 17,
    21, 11, 31, 17, 12, 11,
    12, 16, 16, 26, 27, 33,
    36, 30, 18, 24, 13, 27,
    13, 8, 13, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    45161049688530065, 29735812427926609, 24362263640640428, 24362263640640428, 23139871219303979, 24362263640640428,
    27858689468802668, 23139871219303979, 39227291815878246, 24187176934082336, 38439554496149721, 45160055919413995,
    13796546654402698, 48577005394373668, 13833779561266426, 8861086908132560, 13796546654402698, 12982102324703674,
    13833779561266426, 17798313580599046, 8124121311829188, 44160056920445738, 13796546654402698, 8861086908132560,
    8124121311829188, 8861086908132560, 12805945352531863, 12982102324703674, 38439554496149721, 26215716818829221,
    32609566152029595, 31609565803973772, 25215746086279107, 26253111214778760, 31985143709125029, 17377625720034614,
    35237816123569972, 17414858626233599, 12442165972229357, 17377625720034614, 16563181373192661, 17414858626233599,
    21379392646208802, 11705200378144884, 31985143709125029, 17377625720034614, 12442165972229357, 11705200378144884,
    12442165972229357, 16387024418036865, 16563181373192661, 26253111214778760, 27928682459969980, 33096607614833513,
    36096608185343948, 30928664841098771, 18804896720894461, 24585525633987105, 13796546654402698, 27854059942722514,
    13833779561266426, 8861086908132560, 13796546654402698, 12982102324703674
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
noncomputable def negativeCeiling : ℝ := 70218819 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 44292518487595328752293249024, coefficient := (-44292518487595328752293249024) }, { argument := 8246339545237846642550374400, coefficient := (-8246339545237846642550374400) }, { argument := 198912394268314701922304000, coefficient := (-198912394268314701922304000) }, { argument := 198912394268314701922304000, coefficient := (-198912394268314701922304000) }, { argument := 170496337944269744504832000, coefficient := (-170496337944269744504832000) }, { argument := 198912394268314701922304000, coefficient := (-198912394268314701922304000) }, { argument := 2244868449599551635980288000, coefficient := (-2244868449599551635980288000) }, { argument := 170496337944269744504832000, coefficient := (-170496337944269744504832000) }, { argument := 724588218721060261449433088, coefficient := (-724588218721060261449433088) }, { argument := 176179549209078735988326400, coefficient := (-176179549209078735988326400) }, { argument := 209859537224999882306093056, coefficient := (-209859537224999882306093056) }, { argument := 22131009527377428670387847168, coefficient := (-22131009527377428670387847168) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 236377160187286520642498723840, coefficient := (-236377160187286520642498723840) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 22131024883256605069247774720, coefficient := (-22131024883256605069247774720) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 209859537224999882306093056, coefficient := (-209859537224999882306093056) }, { argument := 179699494655462743857954816, coefficient := (-179699494655462743857954816) }, { argument := 15110794271830367057825759232, coefficient := (-15110794271830367057825759232) }, { argument := 15110790626292569490975621120, coefficient := (-15110790626292569490975621120) }, { argument := 179703140193260310708092928, coefficient := (-179703140193260310708092928) }, { argument := 368836325132291220613103616, coefficient := (-368836325132291220613103616) }, { argument := 39208244097637007538618630144, coefficient := (-39208244097637007538618630144) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 373705389946926223431586283520, coefficient := (-373705389946926223431586283520) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 51529764150834103864359124992, coefficient := (-51529764150834103864359124992) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }, { argument := 39208244097637007538618630144, coefficient := (-39208244097637007538618630144) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 3237692239587291715671687168, coefficient := (-3237692239587291715671687168) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 368836325132291220613103616, coefficient := (-368836325132291220613103616) }, { argument := 4712928815006886154026876928, coefficient := (-4712928815006886154026876928) }, { argument := 169430412926474734334403149824, coefficient := (-169430412926474734334403149824) }, { argument := 169430479927355053056708313088, coefficient := (-169430479927355053056708313088) }, { argument := 4712871258859533171012141056, coefficient := (-4712871258859533171012141056) }, { argument := 16896147660361674126262272, coefficient := (-16896147660361674126262272) }, { argument := 1857635015970167197727195136, coefficient := (-1857635015970167197727195136) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 17901410726290987099587870720, coefficient := (-17901410726290987099587870720) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
