import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 19, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

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
def constantNumerator : ℤ := (-17611148992279379788696848168910848)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    575981838735, 15893175921, 46282812485, 79440401339, 46282812485, 133671765331,
    709206097, 33417938839, 709206097, 1393128135, 2391182649, 1393128135,
    181298833625, 181298747175, 5212787, 112526470241829, 5874762285, 3811213916024283,
    92450206485, 2782782135, 60977944876964031, 2782782135, 2782782135, 238391669565,
    2782782135, 92450206485, 238391669565, 1801901303293761, 2782782135, 2782782135,
    5874762285, 60939127605337597, 180908110155, 10163376975, 220969341019016549, 549499915115,
    30469560585528911, 549499915115, 549499915115, 180908110155, 10163376975, 4526120306299,
    7644532875, 4526120303449, 7644532875, 1393128135, 2391182649, 1393128135,
    5976884625, 5976881775, 69760397, 13946064125, 13946057475, 15,
    6764123, 709206097, 7644532875, 354603319, 6764123, 1986673449,
    71997703383, 575981838735, 15893175921, 1393128135
  ]
def negativeCoefficients : Array ℕ := #[
    664061848140574494507254415360, 18323584295820630930694864896, 853767196922284195796756725760, 2930833505226613157785552027648, 853767196922284195796756725760, 2465808844941918150267183824896,
    6541271683436715706601701376, 2465808660935646015014406455296, 6541271683436715706601701376, 102794712672917160697937264640, 352876274876782855117992886272, 102794712672917160697937264640,
    836093296185605683750633472000, 836092897505349390702949171200, 24616690611138609264566730752, 1013548338900836582632999354368, 108370236365276133877937602560, 34328363144072419505547547508736,
    852702649295199053407982714880, 102666539714472126831730360320, 34327531228214231946144012828672, 102666539714472126831730360320, 102666539714472126831730360320, 4397550117769889432625783767040,
    102666539714472126831730360320, 852702649295199053407982714880, 4397550117769889432625783767040, 1014380254759024142036534034432, 102666539714472126831730360320, 102666539714472126831730360320,
    108370236365276133877937602560, 34305679046960188509942934667264, 417145701110967625402873282560, 23435151747807169966453555200, 124394680234193373369176097292288, 633530268915720494759794442240,
    34305675424782688874003079102464, 633530268915720494759794442240, 633530268915720494759794442240, 417145701110967625402873282560, 23435151747807169966453555200, 20873045734279384698342967607296,
    70508370754092045265010688000, 20873045721136079545824912080896, 70508370754092045265010688000, 102794712672917160697937264640, 352876274876782855117992886272, 102794712672917160697937264640,
    441016244141857943077257216000, 441016033848975502788368793600, 329434160624480149356582797312, 32157434468677141682716672000, 32157419134821130411651891200, 18569100589280704123486863360,
    62388022932046236702736384, 6541271683436715706601701376, 70508370754092045265010688000, 6541276673280987645035413504, 62388022932046236702736384, 18323828335868432566601121792,
    664061604100526692871348158464, 664061848140574494507254415360, 18323584295820630930694864896, 102794712672917160697937264640
  ]
def negativeScales : Array ℕ := #[
    39, 33, 35, 36, 35, 36,
    29, 34, 29, 30, 31, 30,
    37, 37, 22, 46, 32, 51,
    36, 31, 55, 31, 31, 37,
    31, 36, 37, 50, 31, 31,
    32, 55, 37, 33, 57, 38,
    54, 38, 38, 37, 33, 42,
    32, 42, 32, 30, 31, 30,
    32, 32, 26, 33, 33, 3,
    22, 29, 32, 28, 22, 30,
    36, 39, 33, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39067232366574370, 33887688398494696, 35429757484772722, 36209153860364312, 35429757484772722, 36959903822035651,
    29401629698146921, 34959903714377265, 29401629698146921, 30375680812016910, 31155077187608519, 30375680812016910,
    37399578687382274, 37399577999451671, 22313623480414478, 46677257743192877, 32451883329972020, 51759172009674139,
    36427957490726510, 31373880817970699, 55759137046881761, 31373880817970699, 31373880817970699, 37794542867021193,
    31373880817970699, 36427957490726510, 37794542867021193, 50678441415000028, 31373880817970699, 31373880817970699,
    32451883329972020, 55758218365250770, 37396466129542853, 33242660793463812, 57616623826022104, 38999328325496655,
    54758218212923284, 38999328325496655, 38999328325496655, 37396466129542853, 33242660793463812, 42041412071241270,
    32831781202505402, 42041412070332836, 32831781202505402, 30375680812016910, 31155077187608519, 30375680812016910,
    32476746547904850, 32476745859974246, 26055904914594460, 33699138969312111, 33699138281381506, 3906890600547867,
    22689471463586864, 29401629698146921, 32831781202505402, 28401630798670059, 22689471463586864, 30887707612696403,
    36067231836389670, 39067232366574370, 33887688398494696, 30375680812016910
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
noncomputable def negativeCeiling : ℝ := 52964426731 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 664061848140574494507254415360, coefficient := (-664061848140574494507254415360) }, { argument := 18323584295820630930694864896, coefficient := (-18323584295820630930694864896) }, { argument := 853767196922284195796756725760, coefficient := (-853767196922284195796756725760) }, { argument := 2930833505226613157785552027648, coefficient := (-2930833505226613157785552027648) }, { argument := 853767196922284195796756725760, coefficient := (-853767196922284195796756725760) }, { argument := 2465808844941918150267183824896, coefficient := (-2465808844941918150267183824896) }, { argument := 6541271683436715706601701376, coefficient := (-6541271683436715706601701376) }, { argument := 2465808660935646015014406455296, coefficient := (-2465808660935646015014406455296) }, { argument := 6541271683436715706601701376, coefficient := (-6541271683436715706601701376) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 352876274876782855117992886272, coefficient := (-352876274876782855117992886272) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 836093296185605683750633472000, coefficient := (-836093296185605683750633472000) }, { argument := 836092897505349390702949171200, coefficient := (-836092897505349390702949171200) }, { argument := 24616690611138609264566730752, coefficient := (-24616690611138609264566730752) }, { argument := 1013548338900836582632999354368, coefficient := (-1013548338900836582632999354368) }, { argument := 108370236365276133877937602560, coefficient := (-108370236365276133877937602560) }, { argument := 34328363144072419505547547508736, coefficient := (-34328363144072419505547547508736) }, { argument := 852702649295199053407982714880, coefficient := (-852702649295199053407982714880) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 34327531228214231946144012828672, coefficient := (-34327531228214231946144012828672) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 4397550117769889432625783767040, coefficient := (-4397550117769889432625783767040) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 852702649295199053407982714880, coefficient := (-852702649295199053407982714880) }, { argument := 4397550117769889432625783767040, coefficient := (-4397550117769889432625783767040) }, { argument := 1014380254759024142036534034432, coefficient := (-1014380254759024142036534034432) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 108370236365276133877937602560, coefficient := (-108370236365276133877937602560) }, { argument := 34305679046960188509942934667264, coefficient := (-34305679046960188509942934667264) }, { argument := 417145701110967625402873282560, coefficient := (-417145701110967625402873282560) }, { argument := 23435151747807169966453555200, coefficient := (-23435151747807169966453555200) }, { argument := 124394680234193373369176097292288, coefficient := (-124394680234193373369176097292288) }, { argument := 633530268915720494759794442240, coefficient := (-633530268915720494759794442240) }, { argument := 34305675424782688874003079102464, coefficient := (-34305675424782688874003079102464) }, { argument := 633530268915720494759794442240, coefficient := (-633530268915720494759794442240) }, { argument := 633530268915720494759794442240, coefficient := (-633530268915720494759794442240) }, { argument := 417145701110967625402873282560, coefficient := (-417145701110967625402873282560) }, { argument := 23435151747807169966453555200, coefficient := (-23435151747807169966453555200) }, { argument := 20873045734279384698342967607296, coefficient := (-20873045734279384698342967607296) }, { argument := 70508370754092045265010688000, coefficient := (-70508370754092045265010688000) }, { argument := 20873045721136079545824912080896, coefficient := (-20873045721136079545824912080896) }, { argument := 70508370754092045265010688000, coefficient := (-70508370754092045265010688000) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 352876274876782855117992886272, coefficient := (-352876274876782855117992886272) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 441016244141857943077257216000, coefficient := (-441016244141857943077257216000) }, { argument := 441016033848975502788368793600, coefficient := (-441016033848975502788368793600) }, { argument := 329434160624480149356582797312, coefficient := (-329434160624480149356582797312) }, { argument := 32157434468677141682716672000, coefficient := (-32157434468677141682716672000) }, { argument := 32157419134821130411651891200, coefficient := (-32157419134821130411651891200) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 6541271683436715706601701376, coefficient := (-6541271683436715706601701376) }, { argument := 70508370754092045265010688000, coefficient := (-70508370754092045265010688000) }, { argument := 6541276673280987645035413504, coefficient := (-6541276673280987645035413504) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 18323828335868432566601121792, coefficient := (-18323828335868432566601121792) }, { argument := 664061604100526692871348158464, coefficient := (-664061604100526692871348158464) }, { argument := 664061848140574494507254415360, coefficient := (-664061848140574494507254415360) }, { argument := 18323584295820630930694864896, coefficient := (-18323584295820630930694864896) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }] }

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
def constantNumerator : ℤ := (-6173013041091056840207948406849536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2391182649, 1393128135, 1986673449, 71997703383, 575981838735, 15893175921,
    119344643565, 204844646931, 119344643565, 181298833625, 181298747175, 1393128135,
    2391182649, 1393128135, 181298833625, 181298747175, 141, 654058953,
    23703312951, 189626573295, 5232401937, 46282812485, 79440401339, 46282812485,
    5976884625, 5976881775, 119344643565, 204844646931, 119344643565, 2237347144625,
    2237346077775, 1665, 89653269375, 89653226625, 117, 1801065541591555,
    4991831733, 280439985, 6500813253653147, 15162455189, 900532684921265, 15162455189,
    15162455189, 4991831733, 280439985, 267343531145, 354603319, 267343511195,
    354603319, 34880193, 181298833625, 181298747175, 1665, 15,
    36744885, 1331646795, 10653178275, 293955165, 1393128135, 2391182649,
    1393128135, 13946064125, 13946057475, 1393128135
  ]
def negativeCoefficients : Array ℕ := #[
    352876274876782855117992886272, 102794712672917160697937264640, 18323828335868432566601121792, 664061604100526692871348158464, 664061848140574494507254415360, 18323584295820630930694864896,
    4403040192823285049894979502080, 15114867107222198960887361961984, 4403040192823285049894979502080, 836093296185605683750633472000, 836092897505349390702949171200, 102794712672917160697937264640,
    352876274876782855117992886272, 102794712672917160697937264640, 836093296185605683750633472000, 836092897505349390702949171200, 21818693192404827345097064448, 12065258115109424156060418048,
    437248947706142113431935778816, 437249108393423896506626211840, 12065097427827641081369985024, 853767196922284195796756725760, 2930833505226613157785552027648, 853767196922284195796756725760,
    441016244141857943077257216000, 441016033848975502788368793600, 4403040192823285049894979502080, 15114867107222198960887361961984, 4403040192823285049894979502080, 10317942545235551459911663616000,
    10317937625258322700652878233600, 257646270676269769713380229120, 826905457765983643269857280000, 826905063466829067728191488000, 579355938385557968652790136832, 1013909762747695957905936220160,
    11510380304709128847743778816, 646650578916243193693470720, 3659632518344686815475205668864, 17481120650035774336180158464, 1013909666061590334000185999360, 17481120650035774336180158464,
    17481120650035774336180158464, 11510380304709128847743778816, 646650578916243193693470720, 2465808849396806844068040540160, 6541276673280987645035413504, 2465808665390534708815263170560,
    6541276673280987645035413504, 329434108678448837790485446656, 836093296185605683750633472000, 836092897505349390702949171200, 257646270676269769713380229120, 18569100589280704123486863360,
    677823489612888997531484160, 24564547623940568170333470720, 24564556651315949241945292800, 677814462237507925919662080, 102794712672917160697937264640, 352876274876782855117992886272,
    102794712672917160697937264640, 32157434468677141682716672000, 32157419134821130411651891200, 102794712672917160697937264640
  ]
def negativeScales : Array ℕ := #[
    31, 30, 30, 36, 39, 33,
    36, 37, 36, 37, 37, 30,
    31, 30, 37, 37, 7, 29,
    34, 37, 32, 35, 36, 35,
    32, 32, 36, 37, 36, 41,
    41, 10, 36, 36, 6, 50,
    32, 28, 52, 33, 49, 33,
    33, 32, 28, 37, 28, 37,
    28, 25, 37, 37, 10, 3,
    25, 30, 33, 28, 30, 31,
    30, 33, 33, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31155077187608519, 30375680812016910, 30887707612696403, 36067231836389670, 39067232366574370, 33887688398494696,
    36796342861089136, 37575739236084089, 36796342861089136, 37399578687382274, 37399577999451671, 30375680812016910,
    31155077187608519, 30375680812016910, 37399578687382274, 37399577999451671, 7139551352398794, 29284845436668778,
    34464369663860030, 37464370194044730, 32284826222468295, 35429757484772722, 36209153860364312, 35429757484772722,
    32476746547904850, 32476745859974246, 36796342861089136, 37575739236084089, 36796342861089136, 41024926259584173,
    41024925571653569, 10701306462033270, 36383637143513249, 36383636455582646, 6870364722125690, 50677772105879000,
    32216922157966491, 28063116821887456, 52529541634316953, 33819784331458095, 49677771968304063, 33819784331458095,
    33819784331458095, 32216922157966491, 28063116821887456, 37959903824642117, 28401630798670059, 37959903716983731,
    28401630798670059, 25055904687106553, 37399578687382274, 37399577999451671, 10701306462033270, 3906890600547867,
    25131040100589743, 30310564327780916, 33310564857965616, 28131020886389259, 30375680812016910, 31155077187608519,
    30375680812016910, 33699138969312111, 33699138281381506, 30375680812016910
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
noncomputable def negativeCeiling : ℝ := 11177795437 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 352876274876782855117992886272, coefficient := (-352876274876782855117992886272) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 18323828335868432566601121792, coefficient := (-18323828335868432566601121792) }, { argument := 664061604100526692871348158464, coefficient := (-664061604100526692871348158464) }, { argument := 664061848140574494507254415360, coefficient := (-664061848140574494507254415360) }, { argument := 18323584295820630930694864896, coefficient := (-18323584295820630930694864896) }, { argument := 4403040192823285049894979502080, coefficient := (-4403040192823285049894979502080) }, { argument := 15114867107222198960887361961984, coefficient := (-15114867107222198960887361961984) }, { argument := 4403040192823285049894979502080, coefficient := (-4403040192823285049894979502080) }, { argument := 836093296185605683750633472000, coefficient := (-836093296185605683750633472000) }, { argument := 836092897505349390702949171200, coefficient := (-836092897505349390702949171200) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 352876274876782855117992886272, coefficient := (-352876274876782855117992886272) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 836093296185605683750633472000, coefficient := (-836093296185605683750633472000) }, { argument := 836092897505349390702949171200, coefficient := (-836092897505349390702949171200) }, { argument := 21818693192404827345097064448, coefficient := (-21818693192404827345097064448) }, { argument := 12065258115109424156060418048, coefficient := (-12065258115109424156060418048) }, { argument := 437248947706142113431935778816, coefficient := (-437248947706142113431935778816) }, { argument := 437249108393423896506626211840, coefficient := (-437249108393423896506626211840) }, { argument := 12065097427827641081369985024, coefficient := (-12065097427827641081369985024) }, { argument := 853767196922284195796756725760, coefficient := (-853767196922284195796756725760) }, { argument := 2930833505226613157785552027648, coefficient := (-2930833505226613157785552027648) }, { argument := 853767196922284195796756725760, coefficient := (-853767196922284195796756725760) }, { argument := 441016244141857943077257216000, coefficient := (-441016244141857943077257216000) }, { argument := 441016033848975502788368793600, coefficient := (-441016033848975502788368793600) }, { argument := 4403040192823285049894979502080, coefficient := (-4403040192823285049894979502080) }, { argument := 15114867107222198960887361961984, coefficient := (-15114867107222198960887361961984) }, { argument := 4403040192823285049894979502080, coefficient := (-4403040192823285049894979502080) }, { argument := 10317942545235551459911663616000, coefficient := (-10317942545235551459911663616000) }, { argument := 10317937625258322700652878233600, coefficient := (-10317937625258322700652878233600) }, { argument := 257646270676269769713380229120, coefficient := (-257646270676269769713380229120) }, { argument := 826905457765983643269857280000, coefficient := (-826905457765983643269857280000) }, { argument := 826905063466829067728191488000, coefficient := (-826905063466829067728191488000) }, { argument := 579355938385557968652790136832, coefficient := (-579355938385557968652790136832) }, { argument := 1013909762747695957905936220160, coefficient := (-1013909762747695957905936220160) }, { argument := 11510380304709128847743778816, coefficient := (-11510380304709128847743778816) }, { argument := 646650578916243193693470720, coefficient := (-646650578916243193693470720) }, { argument := 3659632518344686815475205668864, coefficient := (-3659632518344686815475205668864) }, { argument := 17481120650035774336180158464, coefficient := (-17481120650035774336180158464) }, { argument := 1013909666061590334000185999360, coefficient := (-1013909666061590334000185999360) }, { argument := 17481120650035774336180158464, coefficient := (-17481120650035774336180158464) }, { argument := 17481120650035774336180158464, coefficient := (-17481120650035774336180158464) }, { argument := 11510380304709128847743778816, coefficient := (-11510380304709128847743778816) }, { argument := 646650578916243193693470720, coefficient := (-646650578916243193693470720) }, { argument := 2465808849396806844068040540160, coefficient := (-2465808849396806844068040540160) }, { argument := 6541276673280987645035413504, coefficient := (-6541276673280987645035413504) }, { argument := 2465808665390534708815263170560, coefficient := (-2465808665390534708815263170560) }, { argument := 6541276673280987645035413504, coefficient := (-6541276673280987645035413504) }, { argument := 329434108678448837790485446656, coefficient := (-329434108678448837790485446656) }, { argument := 836093296185605683750633472000, coefficient := (-836093296185605683750633472000) }, { argument := 836092897505349390702949171200, coefficient := (-836092897505349390702949171200) }, { argument := 257646270676269769713380229120, coefficient := (-257646270676269769713380229120) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 677823489612888997531484160, coefficient := (-677823489612888997531484160) }, { argument := 24564547623940568170333470720, coefficient := (-24564547623940568170333470720) }, { argument := 24564556651315949241945292800, coefficient := (-24564556651315949241945292800) }, { argument := 677814462237507925919662080, coefficient := (-677814462237507925919662080) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 352876274876782855117992886272, coefficient := (-352876274876782855117992886272) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 32157434468677141682716672000, coefficient := (-32157434468677141682716672000) }, { argument := 32157419134821130411651891200, coefficient := (-32157419134821130411651891200) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
