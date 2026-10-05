import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7568602091573686090830639915859968)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5212787, 69760397, 15, 141, 1665, 117,
    34880193, 1665, 15, 117, 117, 117,
    117, 117, 2606399, 141, 7853580277, 266904234725,
    91221939445, 1127952665377, 3007316685, 7017072265, 91221939445, 91221939445,
    3007316685, 1125738879085, 45109750275, 33363029401, 91221939445, 7017072265,
    45109750275, 7017072265, 91221939445, 91221939445, 2213932089, 900211847783283,
    5874762285, 30489714553748621, 92450206485, 2782782135, 30488975663792417, 2782782135,
    2782782135, 238391669565, 2782782135, 92450206485, 238391669565, 900950737739487,
    2782782135, 2782782135, 5874762285, 6764123, 709206097, 7644532875,
    354603319, 6764123, 654058953, 23703312951, 189626573295, 5232401937,
    899795737959611, 623987277, 35055465, 3247769731270481
  ]
def negativeCoefficients : Array ℕ := #[
    24616690611138609264566730752, 329434160624480149356582797312, 18569100589280704123486863360, 21818693192404827345097064448, 257646270676269769713380229120, 579355938385557968652790136832,
    329434108678448837790485446656, 257646270676269769713380229120, 18569100589280704123486863360, 18104873074548686520399691776, 18104873074548686520399691776, 18104873074548686520399691776,
    579355938385557968652790136832, 18104873074548686520399691776, 24616742557169920830664081408, 21818693192404827345097064448, 36218246358037992199482769408, 2461757055080688432995683532800,
    841373885424672667016426946560, 20807054145468067697010757599232, 443801609894332835349324103680, 32360534054795102577554882560, 841373885424672667016426946560, 841373885424672667016426946560,
    443801609894332835349324103680, 10383108498152828627026895175680, 832128018551874066279982694400, 2461757059535577126796540248064, 841373885424672667016426946560, 32360534054795102577554882560,
    832128018551874066279982694400, 32360534054795102577554882560, 841373885424672667016426946560, 841373885424672667016426946560, 40839838642356157588464205824, 1013548435557824746097939054592,
    108370236365276133877937602560, 34328366775723769567667504021504, 852702649295199053407982714880, 102666539714472126831730360320, 34327534859590912533540223582208, 102666539714472126831730360320,
    102666539714472126831730360320, 4397550117769889432625783767040, 102666539714472126831730360320, 852702649295199053407982714880, 4397550117769889432625783767040, 1014380351690681780225219493888,
    102666539714472126831730360320, 102666539714472126831730360320, 108370236365276133877937602560, 62388022932046236702736384, 6541271683436715706601701376, 70508370754092045265010688000,
    6541276673280987645035413504, 62388022932046236702736384, 12065258115109424156060418048, 437248947706142113431935778816, 437249108393423896506626211840, 12065097427827641081369985024,
    1013079937546116140599045259264, 11510533604069910401758789632, 646659191239882606840381440, 3656663637883728540516843782144
  ]
def negativeScales : Array ℕ := #[
    22, 26, 3, 7, 10, 6,
    25, 10, 3, 6, 6, 6,
    6, 6, 21, 7, 32, 37,
    36, 40, 31, 32, 36, 36,
    31, 40, 35, 34, 36, 32,
    35, 32, 36, 36, 31, 49,
    32, 54, 36, 31, 54, 31,
    31, 37, 31, 36, 37, 49,
    31, 31, 32, 22, 29, 32,
    28, 22, 29, 34, 37, 32,
    49, 29, 25, 51
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22313623480414478, 26055904914594460, 3906890600547867, 7139551352398794, 10701306462033270, 6870364722125690,
    25055904687106553, 10701306462033270, 3906890600547867, 6870364722125690, 6870364722125690, 6870364722125690,
    6870364722125690, 6870364722125690, 21313626524779940, 7139551352398794, 32870703353903226, 37957531251174189,
    36408661792144715, 40036843664843628, 31485829652667334, 32708222074091343, 36408661792144715, 36408661792144715,
    31485829652667334, 40034009364346611, 35392720248275689, 34957531253784945, 36408661792144715, 32708222074091343,
    35392720248275689, 32708222074091343, 36408661792144715, 36408661792144715, 31043963823004749, 49677257880775413,
    32451883329972020, 54759172162299101, 36427957490726510, 31373880817970699, 54759137199498879, 31373880817970699,
    31373880817970699, 37794542867021193, 31373880817970699, 36427957490726510, 37794542867021193, 49678441552860376,
    31373880817970699, 31373880817970699, 32451883329972020, 22689471463586864, 29401629698146921, 32831781202505402,
    28401630798670059, 22689471463586864, 29284845436668778, 34464369663860030, 37464370194044730, 32284826222468295,
    49676590861819343, 29216941372166975, 25063136036087939, 51528370771557505
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
noncomputable def negativeCeiling : ℝ := 3029494193 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24616690611138609264566730752, coefficient := (-24616690611138609264566730752) }, { argument := 329434160624480149356582797312, coefficient := (-329434160624480149356582797312) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 21818693192404827345097064448, coefficient := (-21818693192404827345097064448) }, { argument := 257646270676269769713380229120, coefficient := (-257646270676269769713380229120) }, { argument := 579355938385557968652790136832, coefficient := (-579355938385557968652790136832) }, { argument := 329434108678448837790485446656, coefficient := (-329434108678448837790485446656) }, { argument := 257646270676269769713380229120, coefficient := (-257646270676269769713380229120) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 579355938385557968652790136832, coefficient := (-579355938385557968652790136832) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 24616742557169920830664081408, coefficient := (-24616742557169920830664081408) }, { argument := 21818693192404827345097064448, coefficient := (-21818693192404827345097064448) }, { argument := 36218246358037992199482769408, coefficient := (-36218246358037992199482769408) }, { argument := 2461757055080688432995683532800, coefficient := (-2461757055080688432995683532800) }, { argument := 841373885424672667016426946560, coefficient := (-841373885424672667016426946560) }, { argument := 20807054145468067697010757599232, coefficient := (-20807054145468067697010757599232) }, { argument := 443801609894332835349324103680, coefficient := (-443801609894332835349324103680) }, { argument := 32360534054795102577554882560, coefficient := (-32360534054795102577554882560) }, { argument := 841373885424672667016426946560, coefficient := (-841373885424672667016426946560) }, { argument := 841373885424672667016426946560, coefficient := (-841373885424672667016426946560) }, { argument := 443801609894332835349324103680, coefficient := (-443801609894332835349324103680) }, { argument := 10383108498152828627026895175680, coefficient := (-10383108498152828627026895175680) }, { argument := 832128018551874066279982694400, coefficient := (-832128018551874066279982694400) }, { argument := 2461757059535577126796540248064, coefficient := (-2461757059535577126796540248064) }, { argument := 841373885424672667016426946560, coefficient := (-841373885424672667016426946560) }, { argument := 32360534054795102577554882560, coefficient := (-32360534054795102577554882560) }, { argument := 832128018551874066279982694400, coefficient := (-832128018551874066279982694400) }, { argument := 32360534054795102577554882560, coefficient := (-32360534054795102577554882560) }, { argument := 841373885424672667016426946560, coefficient := (-841373885424672667016426946560) }, { argument := 841373885424672667016426946560, coefficient := (-841373885424672667016426946560) }, { argument := 40839838642356157588464205824, coefficient := (-40839838642356157588464205824) }, { argument := 1013548435557824746097939054592, coefficient := (-1013548435557824746097939054592) }, { argument := 108370236365276133877937602560, coefficient := (-108370236365276133877937602560) }, { argument := 34328366775723769567667504021504, coefficient := (-34328366775723769567667504021504) }, { argument := 852702649295199053407982714880, coefficient := (-852702649295199053407982714880) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 34327534859590912533540223582208, coefficient := (-34327534859590912533540223582208) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 4397550117769889432625783767040, coefficient := (-4397550117769889432625783767040) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 852702649295199053407982714880, coefficient := (-852702649295199053407982714880) }, { argument := 4397550117769889432625783767040, coefficient := (-4397550117769889432625783767040) }, { argument := 1014380351690681780225219493888, coefficient := (-1014380351690681780225219493888) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 102666539714472126831730360320, coefficient := (-102666539714472126831730360320) }, { argument := 108370236365276133877937602560, coefficient := (-108370236365276133877937602560) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 6541271683436715706601701376, coefficient := (-6541271683436715706601701376) }, { argument := 70508370754092045265010688000, coefficient := (-70508370754092045265010688000) }, { argument := 6541276673280987645035413504, coefficient := (-6541276673280987645035413504) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 12065258115109424156060418048, coefficient := (-12065258115109424156060418048) }, { argument := 437248947706142113431935778816, coefficient := (-437248947706142113431935778816) }, { argument := 437249108393423896506626211840, coefficient := (-437249108393423896506626211840) }, { argument := 12065097427827641081369985024, coefficient := (-12065097427827641081369985024) }, { argument := 1013079937546116140599045259264, coefficient := (-1013079937546116140599045259264) }, { argument := 11510533604069910401758789632, coefficient := (-11510533604069910401758789632) }, { argument := 646659191239882606840381440, coefficient := (-646659191239882606840381440) }, { argument := 3656663637883728540516843782144, coefficient := (-3656663637883728540516843782144) }] }

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
def constantNumerator : ℤ := (-28090518066576577281279175017103360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1895332141, 224948913082109, 1895332141, 1895332141, 623987277, 35055465,
    36744885, 1331646795, 10653178275, 293955165, 2941048285, 5048052259,
    2941048285, 15662573531, 6764123, 15662568781, 6764123, 7853577887,
    266904214649, 91221895947, 281988166165, 3007315251, 7017068919, 91221895947,
    91221895947, 3007315251, 1125738342291, 45109728765, 66726053783, 91221895947,
    7017068919, 45109728765, 7017068919, 91221895947, 91221895947, 553482843,
    3249602369014629, 10083515859, 110568702723847323, 158682696939, 4776402249, 221132118378347775,
    4776402249, 4776402249, 409178459331, 4776402249, 158682696939, 409178459331,
    6504491807376129, 4776402249, 4776402249, 10083515859, 30470300835504965, 22613505459,
    1270421655, 110487307405064367, 68687464147, 7617574404530435, 68687464147, 68687464147,
    22613505459, 1270421655, 1986673449, 71997703383
  ]
def negativeCoefficients : Array ℕ := #[
    17481353469851493138251644928, 1013079841133984185274612056064, 17481353469851493138251644928, 17481353469851493138251644928, 11510533604069910401758789632, 646659191239882606840381440,
    677823489612888997531484160, 24564547623940568170333470720, 24564556651315949241945292800, 677814462237507925919662080, 108505530043634780736711557120, 372480512369937458180103602176,
    108505530043634780736711557120, 36115435682751792015329984512, 62388022932046236702736384, 36115424729997498250283712512, 62388022932046236702736384, 36218235336108408158025678848,
    2461756869912271421099204411392, 841373484226435807907388850176, 20807054132241752196161009090560, 443801398273284821753347964928, 32360518624093684919514955776, 841373484226435807907388850176,
    841373484226435807907388850176, 443801398273284821753347964928, 10383103547102059475604370096128, 832127621762409040787527434240, 2461756874367160114900061126656, 841373484226435807907388850176,
    32360518624093684919514955776, 832127621762409040787527434240, 32360518624093684919514955776, 841373484226435807907388850176, 841373484226435807907388850176, 40839825416040656738715697152,
    3658727004549141050313456746496, 372016072828329057359430156288, 124489292096489487488030764695552, 2927179099359747056591305703424, 352436279521574896445775937536, 124486315741046931212123032780800,
    352436279521574896445775937536, 352436279521574896445775937536, 15096020639507458064427402657792, 352436279521574896445775937536, 2927179099359747056591305703424, 15096020639507458064427402657792,
    3661703359991697326221188661248, 352436279521574896445775937536, 352436279521574896445775937536, 372016072828329057359430156288, 34306508872161768327249825628160, 417145547811606843848858271744,
    23435143135483530553306644480, 124397649114654331644134459179008, 633530036095904775957722955776, 34306505249710295022728653045760, 633530036095904775957722955776, 633530036095904775957722955776,
    417145547811606843848858271744, 23435143135483530553306644480, 18323828335868432566601121792, 664061604100526692871348158464
  ]
def negativeScales : Array ℕ := #[
    30, 47, 30, 30, 29, 25,
    25, 30, 33, 28, 31, 32,
    31, 33, 22, 33, 22, 32,
    37, 36, 38, 31, 32, 36,
    36, 31, 40, 35, 35, 36,
    32, 35, 32, 36, 36, 29,
    51, 33, 56, 37, 32, 57,
    32, 32, 38, 32, 37, 38,
    52, 32, 32, 33, 54, 34,
    30, 56, 35, 52, 35, 35,
    34, 30, 30, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30819803545658945, 47676590724521874, 30819803545658945, 30819803545658945, 29216941372166975, 25063136036087939,
    25131040100589743, 30310564327780916, 33310564857965616, 28131020886389259, 31453683324018234, 32233079699609792,
    31453683324018234, 33866602233819392, 22689471463586864, 33866601796292138, 22689471463586864, 32870702914862468,
    37957531142657542, 36408661104214112, 38036843663926557, 31485828964736730, 32708221386160738, 36408661104214112,
    36408661104214112, 31485828964736730, 40034008676416008, 35392719560345086, 35957531145268299, 36408661104214112,
    32708221386160738, 35392719560345086, 32708221386160738, 36408661104214112, 36408661104214112, 29043963355776094,
    51529184619807103, 33231279705563582, 56617720691118508, 37207353866318102, 32153277193562309, 57617686197994660,
    32153277193562309, 32153277193562309, 38573939242037734, 32153277193562309, 37207353866318102, 38573939242037734,
    52530357767630325, 32153277193562309, 32153277193562309, 33231279705563582, 54758253262395037, 34396465599358154,
    30242660263279113, 56616658257864359, 35999327795311758, 52758253110059714, 35999327795311758, 35999327795311758,
    34396465599358154, 30242660263279113, 30887707612696403, 36067231836389670
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
noncomputable def negativeCeiling : ℝ := 34510175737 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17481353469851493138251644928, coefficient := (-17481353469851493138251644928) }, { argument := 1013079841133984185274612056064, coefficient := (-1013079841133984185274612056064) }, { argument := 17481353469851493138251644928, coefficient := (-17481353469851493138251644928) }, { argument := 17481353469851493138251644928, coefficient := (-17481353469851493138251644928) }, { argument := 11510533604069910401758789632, coefficient := (-11510533604069910401758789632) }, { argument := 646659191239882606840381440, coefficient := (-646659191239882606840381440) }, { argument := 677823489612888997531484160, coefficient := (-677823489612888997531484160) }, { argument := 24564547623940568170333470720, coefficient := (-24564547623940568170333470720) }, { argument := 24564556651315949241945292800, coefficient := (-24564556651315949241945292800) }, { argument := 677814462237507925919662080, coefficient := (-677814462237507925919662080) }, { argument := 108505530043634780736711557120, coefficient := (-108505530043634780736711557120) }, { argument := 372480512369937458180103602176, coefficient := (-372480512369937458180103602176) }, { argument := 108505530043634780736711557120, coefficient := (-108505530043634780736711557120) }, { argument := 36115435682751792015329984512, coefficient := (-36115435682751792015329984512) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 36115424729997498250283712512, coefficient := (-36115424729997498250283712512) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 36218235336108408158025678848, coefficient := (-36218235336108408158025678848) }, { argument := 2461756869912271421099204411392, coefficient := (-2461756869912271421099204411392) }, { argument := 841373484226435807907388850176, coefficient := (-841373484226435807907388850176) }, { argument := 20807054132241752196161009090560, coefficient := (-20807054132241752196161009090560) }, { argument := 443801398273284821753347964928, coefficient := (-443801398273284821753347964928) }, { argument := 32360518624093684919514955776, coefficient := (-32360518624093684919514955776) }, { argument := 841373484226435807907388850176, coefficient := (-841373484226435807907388850176) }, { argument := 841373484226435807907388850176, coefficient := (-841373484226435807907388850176) }, { argument := 443801398273284821753347964928, coefficient := (-443801398273284821753347964928) }, { argument := 10383103547102059475604370096128, coefficient := (-10383103547102059475604370096128) }, { argument := 832127621762409040787527434240, coefficient := (-832127621762409040787527434240) }, { argument := 2461756874367160114900061126656, coefficient := (-2461756874367160114900061126656) }, { argument := 841373484226435807907388850176, coefficient := (-841373484226435807907388850176) }, { argument := 32360518624093684919514955776, coefficient := (-32360518624093684919514955776) }, { argument := 832127621762409040787527434240, coefficient := (-832127621762409040787527434240) }, { argument := 32360518624093684919514955776, coefficient := (-32360518624093684919514955776) }, { argument := 841373484226435807907388850176, coefficient := (-841373484226435807907388850176) }, { argument := 841373484226435807907388850176, coefficient := (-841373484226435807907388850176) }, { argument := 40839825416040656738715697152, coefficient := (-40839825416040656738715697152) }, { argument := 3658727004549141050313456746496, coefficient := (-3658727004549141050313456746496) }, { argument := 372016072828329057359430156288, coefficient := (-372016072828329057359430156288) }, { argument := 124489292096489487488030764695552, coefficient := (-124489292096489487488030764695552) }, { argument := 2927179099359747056591305703424, coefficient := (-2927179099359747056591305703424) }, { argument := 352436279521574896445775937536, coefficient := (-352436279521574896445775937536) }, { argument := 124486315741046931212123032780800, coefficient := (-124486315741046931212123032780800) }, { argument := 352436279521574896445775937536, coefficient := (-352436279521574896445775937536) }, { argument := 352436279521574896445775937536, coefficient := (-352436279521574896445775937536) }, { argument := 15096020639507458064427402657792, coefficient := (-15096020639507458064427402657792) }, { argument := 352436279521574896445775937536, coefficient := (-352436279521574896445775937536) }, { argument := 2927179099359747056591305703424, coefficient := (-2927179099359747056591305703424) }, { argument := 15096020639507458064427402657792, coefficient := (-15096020639507458064427402657792) }, { argument := 3661703359991697326221188661248, coefficient := (-3661703359991697326221188661248) }, { argument := 352436279521574896445775937536, coefficient := (-352436279521574896445775937536) }, { argument := 352436279521574896445775937536, coefficient := (-352436279521574896445775937536) }, { argument := 372016072828329057359430156288, coefficient := (-372016072828329057359430156288) }, { argument := 34306508872161768327249825628160, coefficient := (-34306508872161768327249825628160) }, { argument := 417145547811606843848858271744, coefficient := (-417145547811606843848858271744) }, { argument := 23435143135483530553306644480, coefficient := (-23435143135483530553306644480) }, { argument := 124397649114654331644134459179008, coefficient := (-124397649114654331644134459179008) }, { argument := 633530036095904775957722955776, coefficient := (-633530036095904775957722955776) }, { argument := 34306505249710295022728653045760, coefficient := (-34306505249710295022728653045760) }, { argument := 633530036095904775957722955776, coefficient := (-633530036095904775957722955776) }, { argument := 633530036095904775957722955776, coefficient := (-633530036095904775957722955776) }, { argument := 417145547811606843848858271744, coefficient := (-417145547811606843848858271744) }, { argument := 23435143135483530553306644480, coefficient := (-23435143135483530553306644480) }, { argument := 18323828335868432566601121792, coefficient := (-18323828335868432566601121792) }, { argument := 664061604100526692871348158464, coefficient := (-664061604100526692871348158464) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
