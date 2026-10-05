import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 16, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3034466314508407615936702162403328)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    316080783, 25287309, 25287309, 53384319, 347908527, 1952977761,
    756466185, 847518651, 163186821, 3384810513, 1700301393, 347908527,
    1952977761, 163186821, 20990933883, 19779993061, 1163859915, 10940283201,
    129188450565, 9078107337, 4944998055, 129188450565, 1163859915, 9078107337,
    9078107337, 9078107337, 9078107337, 9078107337, 5247733681, 10940283201,
    19910076633, 84161270319, 362088727455, 5989437597, 11936991015, 27852979035,
    362088727455, 362088727455, 11936991015, 4468413636615, 179054865225, 84161270319,
    362088727455, 27852979035, 179054865225, 27852979035, 362088727455, 362088727455,
    5972267979, 12865473, 1081847871, 540923805, 6432867, 1886451,
    301166607, 12020759373, 301166607, 7544943, 132405061, 4489046913,
    40583230383, 70643422473, 2126390643, 40583222123
  ]
def negativeCoefficients : Array ℕ := #[
    2915330655309362394682097664, 233234258717906103982620672, 233234258717906103982620672, 246191717535567554203877376, 802222444828783691069128704, 18013040469406649539664805888,
    13954338115110423309016104960, 15633959652692563751407190016, 752566380797312851387613184, 15609683317828134304588234752, 15682512322421422645045100544, 802222444828783691069128704,
    18013040469406649539664805888, 752566380797312851387613184, 96803596301964819129257951232, 91219117444004450873475334144, 85877703958617409913943490560, 100906302151375456648883601408,
    1191553142425816562555965931520, 2679384363508863189315036905472, 91219113565576509376042106880, 1191553142425816562555965931520, 85877703958617409913943490560, 83730761359651974666094903296,
    83730761359651974666094903296, 83730761359651974666094903296, 2679384363508863189315036905472, 83730761359651974666094903296, 96803600180392760626691178496, 100906302151375456648883601408,
    45909511017111971657328623616, 776250707246440417323229642752, 1669839521834388566479019704320, 110485622497312927706882506752, 880794473055501661439482920960, 64224596993630329479962296320,
    1669839521834388566479019704320, 1669839521834388566479019704320, 880794473055501661439482920960, 20606920692527674287427902504960, 1651489636979065615199030476800, 776250707246440417323229642752,
    1669839521834388566479019704320, 64224596993630329479962296320, 1651489636979065615199030476800, 64224596993630329479962296320, 1669839521834388566479019704320, 1669839521834388566479019704320,
    55084449474111785431342252032, 237326087818220246157754368, 19956570803024545488134209536, 19956565988424342249941237760, 237330902418423484350726144, 556782060873495317688877056,
    88888693166023417018913390592, 886975486901505181870637187072, 88888693166023417018913390592, 556718530286905461993111552, 19539538194647213423993028608, 20702074884746726785104740352,
    93578558069949333332469743616, 162892641856296613388060983296, 19612491996075846427993964544, 93578539023686077227357700096
  ]
def negativeScales : Array ℕ := #[
    28, 24, 24, 25, 28, 30,
    29, 29, 27, 31, 30, 28,
    30, 27, 34, 34, 30, 33,
    36, 33, 32, 36, 30, 33,
    33, 33, 33, 33, 32, 33,
    34, 36, 38, 32, 33, 34,
    38, 38, 33, 42, 37, 36,
    38, 34, 37, 34, 38, 38,
    32, 23, 30, 29, 22, 20,
    28, 33, 28, 22, 26, 32,
    35, 36, 30, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28235718084397083, 24591910182082417, 24591910182082417, 25669912694114257, 28374132797958565, 30863028377225982,
    29494700352680383, 29658669876529723, 27281949308775457, 31656427925741600, 30663143353112169, 28374132797958565,
    30863028377225982, 27281949308775457, 34289047302183142, 34203322868860302, 30116270276410350, 33348931033200626,
    36910686148043776, 33079744400385236, 32203322807520212, 36910686148043776, 30116270276410350, 33079744400385236,
    33079744400385236, 33079744400385236, 33079744400385236, 33079744400385236, 32289047359984596, 33348931033200626,
    34212779722811814, 36292437429514895, 38397552307297219, 32479773395546094, 33474720167819787, 34697112589223745,
    38397552307297219, 38397552307297219, 33474720167819787, 42022899879499118, 37381610763428195, 36292437429514895,
    38397552307297219, 34697112589223745, 37381610763428195, 34697112589223745, 38397552307297219, 38397552307297219,
    32475631755443509, 23617001163049725, 30010850496233756, 29010850148177933, 22617030430499618, 20847243198030246,
    28165986573643116, 33484808985443419, 28165986573643116, 22847078572585184, 26980383044573830, 32063762027272199,
    35240164655566164, 36039836188026718, 30985759534103589, 35240164361931031
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
noncomputable def negativeCeiling : ℝ := 698575983 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2915330655309362394682097664, coefficient := (-2915330655309362394682097664) }, { argument := 233234258717906103982620672, coefficient := (-233234258717906103982620672) }, { argument := 233234258717906103982620672, coefficient := (-233234258717906103982620672) }, { argument := 246191717535567554203877376, coefficient := (-246191717535567554203877376) }, { argument := 802222444828783691069128704, coefficient := (-802222444828783691069128704) }, { argument := 18013040469406649539664805888, coefficient := (-18013040469406649539664805888) }, { argument := 13954338115110423309016104960, coefficient := (-13954338115110423309016104960) }, { argument := 15633959652692563751407190016, coefficient := (-15633959652692563751407190016) }, { argument := 752566380797312851387613184, coefficient := (-752566380797312851387613184) }, { argument := 15609683317828134304588234752, coefficient := (-15609683317828134304588234752) }, { argument := 15682512322421422645045100544, coefficient := (-15682512322421422645045100544) }, { argument := 802222444828783691069128704, coefficient := (-802222444828783691069128704) }, { argument := 18013040469406649539664805888, coefficient := (-18013040469406649539664805888) }, { argument := 752566380797312851387613184, coefficient := (-752566380797312851387613184) }, { argument := 96803596301964819129257951232, coefficient := (-96803596301964819129257951232) }, { argument := 91219117444004450873475334144, coefficient := (-91219117444004450873475334144) }, { argument := 85877703958617409913943490560, coefficient := (-85877703958617409913943490560) }, { argument := 100906302151375456648883601408, coefficient := (-100906302151375456648883601408) }, { argument := 1191553142425816562555965931520, coefficient := (-1191553142425816562555965931520) }, { argument := 2679384363508863189315036905472, coefficient := (-2679384363508863189315036905472) }, { argument := 91219113565576509376042106880, coefficient := (-91219113565576509376042106880) }, { argument := 1191553142425816562555965931520, coefficient := (-1191553142425816562555965931520) }, { argument := 85877703958617409913943490560, coefficient := (-85877703958617409913943490560) }, { argument := 83730761359651974666094903296, coefficient := (-83730761359651974666094903296) }, { argument := 83730761359651974666094903296, coefficient := (-83730761359651974666094903296) }, { argument := 83730761359651974666094903296, coefficient := (-83730761359651974666094903296) }, { argument := 2679384363508863189315036905472, coefficient := (-2679384363508863189315036905472) }, { argument := 83730761359651974666094903296, coefficient := (-83730761359651974666094903296) }, { argument := 96803600180392760626691178496, coefficient := (-96803600180392760626691178496) }, { argument := 100906302151375456648883601408, coefficient := (-100906302151375456648883601408) }, { argument := 45909511017111971657328623616, coefficient := (-45909511017111971657328623616) }, { argument := 776250707246440417323229642752, coefficient := (-776250707246440417323229642752) }, { argument := 1669839521834388566479019704320, coefficient := (-1669839521834388566479019704320) }, { argument := 110485622497312927706882506752, coefficient := (-110485622497312927706882506752) }, { argument := 880794473055501661439482920960, coefficient := (-880794473055501661439482920960) }, { argument := 64224596993630329479962296320, coefficient := (-64224596993630329479962296320) }, { argument := 1669839521834388566479019704320, coefficient := (-1669839521834388566479019704320) }, { argument := 1669839521834388566479019704320, coefficient := (-1669839521834388566479019704320) }, { argument := 880794473055501661439482920960, coefficient := (-880794473055501661439482920960) }, { argument := 20606920692527674287427902504960, coefficient := (-20606920692527674287427902504960) }, { argument := 1651489636979065615199030476800, coefficient := (-1651489636979065615199030476800) }, { argument := 776250707246440417323229642752, coefficient := (-776250707246440417323229642752) }, { argument := 1669839521834388566479019704320, coefficient := (-1669839521834388566479019704320) }, { argument := 64224596993630329479962296320, coefficient := (-64224596993630329479962296320) }, { argument := 1651489636979065615199030476800, coefficient := (-1651489636979065615199030476800) }, { argument := 64224596993630329479962296320, coefficient := (-64224596993630329479962296320) }, { argument := 1669839521834388566479019704320, coefficient := (-1669839521834388566479019704320) }, { argument := 1669839521834388566479019704320, coefficient := (-1669839521834388566479019704320) }, { argument := 55084449474111785431342252032, coefficient := (-55084449474111785431342252032) }, { argument := 237326087818220246157754368, coefficient := (-237326087818220246157754368) }, { argument := 19956570803024545488134209536, coefficient := (-19956570803024545488134209536) }, { argument := 19956565988424342249941237760, coefficient := (-19956565988424342249941237760) }, { argument := 237330902418423484350726144, coefficient := (-237330902418423484350726144) }, { argument := 556782060873495317688877056, coefficient := (-556782060873495317688877056) }, { argument := 88888693166023417018913390592, coefficient := (-88888693166023417018913390592) }, { argument := 886975486901505181870637187072, coefficient := (-886975486901505181870637187072) }, { argument := 88888693166023417018913390592, coefficient := (-88888693166023417018913390592) }, { argument := 556718530286905461993111552, coefficient := (-556718530286905461993111552) }, { argument := 19539538194647213423993028608, coefficient := (-19539538194647213423993028608) }, { argument := 20702074884746726785104740352, coefficient := (-20702074884746726785104740352) }, { argument := 93578558069949333332469743616, coefficient := (-93578558069949333332469743616) }, { argument := 162892641856296613388060983296, coefficient := (-162892641856296613388060983296) }, { argument := 19612491996075846427993964544, coefficient := (-19612491996075846427993964544) }, { argument := 93578539023686077227357700096, coefficient := (-93578539023686077227357700096) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-523928086111711452180825864404992)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2126390643, 2126390643, 182160798417, 2126390643, 70643422473, 182160798417,
    2118483041, 2126390643, 2126390643, 4489046913, 4401719, 702722083,
    28048438537, 702722083, 17604867, 4077785, 150587175, 1204697105,
    32622575, 695817271, 383320953, 21534885, 377137389, 1164319449,
    347908527, 1164319449, 1164319449, 383320953, 21534885, 1164319449,
    5638841639, 1164319449, 12865473, 1081847871, 540923805, 6432867,
    1164319449, 5638841639, 1164319449, 1102142187, 92678300949, 46339139295,
    551082273, 57222347, 9135387079, 364629700981, 9135387079, 228863271,
    12865473, 1081847871, 540923805, 6432867, 57222347, 9135387079,
    364629700981, 9135387079, 228863271, 38331179, 1415519445, 11324152787,
    306652205, 383320953, 1856437383, 383320953
  ]
def negativeCoefficients : Array ℕ := #[
    19612491996075846427993964544, 19612491996075846427993964544, 840068407165248755332408147968, 19612491996075846427993964544, 162892641856296613388060983296, 840068407165248755332408147968,
    19539557240910469529105072128, 19612491996075846427993964544, 19612491996075846427993964544, 20702074884746726785104740352, 40598691938692366914813952, 6481467210022540824295768064,
    64675295919901419511400628224, 6481467210022540824295768064, 40594059500086856603664384, 2407099401043574525966417920, 88890978496253220747843993600, 88890956729095213770573086720,
    2407121168201581503237324800, 802222695012750190754922496, 883877939760180946330976256, 49656064031470839681515520, 3478478447755021920409485312, 1342368930984095032723636224,
    802222444828783691069128704, 1342368930984095032723636224, 1342368930984095032723636224, 883877939760180946330976256, 49656064031470839681515520, 1342368930984095032723636224,
    13002283573351238105540067328, 1342368930984095032723636224, 237326087818220246157754368, 19956570803024545488134209536, 19956565988424342249941237760, 237330902418423484350726144,
    1342368930984095032723636224, 13002283573351238105540067328, 1342368930984095032723636224, 10165467428213767210423812096, 854806449396218031741748641792, 854806243170842659705816350720,
    10165673653589139246356103168, 1055565990406001539785162752, 168518147460586061431689969664, 1681557693917436907296416333824, 168518147460586061431689969664, 1055445547002258271695273984,
    237326087818220246157754368, 19956570803024545488134209536, 19956565988424342249941237760, 237330902418423484350726144, 1055565990406001539785162752, 168518147460586061431689969664,
    1681557693917436907296416333824, 168518147460586061431689969664, 1055445547002258271695273984, 2828341796226200068010541056, 104446899733097534378716692480, 104446874156686876180423376896,
    2828367372636858266303856640, 883877939760180946330976256, 8561306323267029776027615232, 883877939760180946330976256
  ]
def negativeScales : Array ℕ := #[
    30, 30, 37, 30, 36, 37,
    30, 30, 30, 32, 22, 29,
    34, 29, 24, 21, 27, 30,
    24, 29, 28, 24, 28, 30,
    28, 30, 30, 28, 24, 30,
    32, 30, 23, 30, 29, 22,
    30, 32, 30, 30, 36, 35,
    29, 25, 33, 38, 33, 27,
    23, 30, 29, 22, 25, 33,
    38, 33, 27, 25, 30, 33,
    28, 28, 30, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30985759534103589, 30985759534103589, 37406421563743656, 30985759534103589, 36039836188026718, 37406421563743656,
    30980384450847796, 30985759534103589, 30985759534103589, 32063762027272199, 22069635617723515, 29388378994979568,
    34707201406865376, 29388378994979568, 24069470992283627, 21959354293214660, 27166023664887111, 30166023311607450,
    24959367339304617, 29374133247882541, 28513977619651006, 24360172283571542, 28490514943922275, 30116839792180295,
    28374132797958565, 30116839792180295, 30116839792180295, 28513977619651006, 24360172283571542, 30116839792180295,
    32392751680917429, 30116839792180295, 23617001163049725, 30010850496233756, 29010850148177933, 22617030430499618,
    30116839792180295, 32392751680917429, 30116839792180295, 30037663211513457, 36431512544706501, 35431512196650678,
    29037692478963342, 25770075336211188, 33088818713120656, 38407641124920806, 33088818713120656, 27769910710770090,
    23617001163049725, 30010850496233756, 29010850148177933, 22617030430499618, 25770075336211188, 33088818713120656,
    38407641124920806, 33088818713120656, 27769910710770090, 25192015037807678, 30398684421677392, 33398684068397731,
    28192028083894976, 28513977619651006, 30789889508912656, 28513977619651006
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
noncomputable def negativeCeiling : ℝ := 3675021271 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19612491996075846427993964544, coefficient := (-19612491996075846427993964544) }, { argument := 19612491996075846427993964544, coefficient := (-19612491996075846427993964544) }, { argument := 840068407165248755332408147968, coefficient := (-840068407165248755332408147968) }, { argument := 19612491996075846427993964544, coefficient := (-19612491996075846427993964544) }, { argument := 162892641856296613388060983296, coefficient := (-162892641856296613388060983296) }, { argument := 840068407165248755332408147968, coefficient := (-840068407165248755332408147968) }, { argument := 19539557240910469529105072128, coefficient := (-19539557240910469529105072128) }, { argument := 19612491996075846427993964544, coefficient := (-19612491996075846427993964544) }, { argument := 19612491996075846427993964544, coefficient := (-19612491996075846427993964544) }, { argument := 20702074884746726785104740352, coefficient := (-20702074884746726785104740352) }, { argument := 40598691938692366914813952, coefficient := (-40598691938692366914813952) }, { argument := 6481467210022540824295768064, coefficient := (-6481467210022540824295768064) }, { argument := 64675295919901419511400628224, coefficient := (-64675295919901419511400628224) }, { argument := 6481467210022540824295768064, coefficient := (-6481467210022540824295768064) }, { argument := 40594059500086856603664384, coefficient := (-40594059500086856603664384) }, { argument := 2407099401043574525966417920, coefficient := (-2407099401043574525966417920) }, { argument := 88890978496253220747843993600, coefficient := (-88890978496253220747843993600) }, { argument := 88890956729095213770573086720, coefficient := (-88890956729095213770573086720) }, { argument := 2407121168201581503237324800, coefficient := (-2407121168201581503237324800) }, { argument := 802222695012750190754922496, coefficient := (-802222695012750190754922496) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 3478478447755021920409485312, coefficient := (-3478478447755021920409485312) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 802222444828783691069128704, coefficient := (-802222444828783691069128704) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 13002283573351238105540067328, coefficient := (-13002283573351238105540067328) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 237326087818220246157754368, coefficient := (-237326087818220246157754368) }, { argument := 19956570803024545488134209536, coefficient := (-19956570803024545488134209536) }, { argument := 19956565988424342249941237760, coefficient := (-19956565988424342249941237760) }, { argument := 237330902418423484350726144, coefficient := (-237330902418423484350726144) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 13002283573351238105540067328, coefficient := (-13002283573351238105540067328) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 10165467428213767210423812096, coefficient := (-10165467428213767210423812096) }, { argument := 854806449396218031741748641792, coefficient := (-854806449396218031741748641792) }, { argument := 854806243170842659705816350720, coefficient := (-854806243170842659705816350720) }, { argument := 10165673653589139246356103168, coefficient := (-10165673653589139246356103168) }, { argument := 1055565990406001539785162752, coefficient := (-1055565990406001539785162752) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1681557693917436907296416333824, coefficient := (-1681557693917436907296416333824) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1055445547002258271695273984, coefficient := (-1055445547002258271695273984) }, { argument := 237326087818220246157754368, coefficient := (-237326087818220246157754368) }, { argument := 19956570803024545488134209536, coefficient := (-19956570803024545488134209536) }, { argument := 19956565988424342249941237760, coefficient := (-19956565988424342249941237760) }, { argument := 237330902418423484350726144, coefficient := (-237330902418423484350726144) }, { argument := 1055565990406001539785162752, coefficient := (-1055565990406001539785162752) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1681557693917436907296416333824, coefficient := (-1681557693917436907296416333824) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1055445547002258271695273984, coefficient := (-1055445547002258271695273984) }, { argument := 2828341796226200068010541056, coefficient := (-2828341796226200068010541056) }, { argument := 104446899733097534378716692480, coefficient := (-104446899733097534378716692480) }, { argument := 104446874156686876180423376896, coefficient := (-104446874156686876180423376896) }, { argument := 2828367372636858266303856640, coefficient := (-2828367372636858266303856640) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }, { argument := 8561306323267029776027615232, coefficient := (-8561306323267029776027615232) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16
