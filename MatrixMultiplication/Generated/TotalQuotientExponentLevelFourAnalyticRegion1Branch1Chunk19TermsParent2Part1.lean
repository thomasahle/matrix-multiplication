import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 19, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 126188816301017763653496847000928256
def positiveArguments : Array ℕ := #[
    8351, 3, 87, 77, 5, 3,
    5, 153, 5, 3, 2451, 157,
    87, 153, 5, 157, 5, 153,
    5, 3, 741, 11115
  ]
def positiveCoefficients : Array ℕ := #[
    1323268770313242966487371058511872, 232113757366008801543585792, 3365649481807127622381993984, 5957586439060892572952035328, 193428131138340667952988160, 3713820117856140824697372672,
    193428131138340667952988160, 5918900812833224439361437696, 6189700196426901374495621120, 3713820117856140824697372672, 94818469884014595430554796032, 6073643317743896973723828224,
    3365649481807127622381993984, 5918900812833224439361437696, 193428131138340667952988160, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696,
    6189700196426901374495621120, 232113757366008801543585792, 28666049034702086990632845312, 429990735520531304859492679680
  ]
def positiveScales : Array ℕ := #[
    13, 1, 6, 6, 2, 1,
    2, 7, 2, 1, 11, 7,
    6, 7, 2, 7, 2, 7,
    2, 1, 9, 13
  ]
def negativeArguments : Array ℕ := #[
    80388040047, 58655970175, 210246156725, 14668253875, 1518681799887, 1518682161969,
    19745, 80388020881, 80388040047, 4907, 41982954325, 150483484775,
    10498788625, 932066512377, 932066734599, 781, 1518681799887, 1518682161969,
    302903, 19377, 1565344563742903, 68574835, 1565344529004361, 68574835,
    246361977, 19745, 2178006575, 7806835525, 544659875, 80388020881,
    80388040047, 749, 80388020881, 80388040047, 19377, 749,
    89078617733, 89078638971, 19745, 2469, 405615, 1
  ]
def negativeCoefficients : Array ℕ := #[
    92681100083382709697088847872, 135251458776670682650089881600, 484794630698387917648376627200, 135290762620161708057952256000, 3501841811489509055631326183424, 3501842646393757517744059711488,
    381923844932653648873175121920, 92681077986489152402259705856, 92681100083382709697088847872, 379660735798335063058125160448, 96806101736439067351344742400, 346991291370549098547301580800,
    96834233424674001029955584000, 1074599525843347199474849021952, 1074599782047869796217597722624, 241707792670470498674054004736, 3501841811489509055631326183424, 3501842646393757517744059711488,
    5858996120619680334496397262848, 374805689706762712292505157632, 1762421298494742393546417897472, 1264982431141860339991183360, 1762421259382621191897836683264, 1264982431141860339991183360,
    2326823085676604856269468073984, 381923844932653648873175121920, 5022141234985211007493734400, 18001337119402368260951244800, 5023600660671817584738304000, 92681077986489152402259705856,
    92681100083382709697088847872, 14487767022261716029678813184, 92681077986489152402259705856, 92681100083382709697088847872, 374805689706762712292505157632, 14487767022261716029678813184,
    102700653985028520229531025408, 102700678470775435069747101696, 381923844932653648873175121920, 382059244624450487340742213632, 30647402895186738293652848640, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    36, 35, 37, 33, 40, 40,
    14, 36, 36, 12, 35, 37,
    33, 39, 39, 9, 40, 40,
    18, 14, 50, 26, 50, 26,
    27, 14, 31, 32, 29, 36,
    36, 9, 36, 36, 14, 9,
    36, 36, 14, 11, 18, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13027733249752832, 1584962500720924, 6442943495848725, 6266786540694901, 2321928094887362, 1584962500720924,
    2321928094887362, 7257387842692651, 2321928094887362, 1584962500720924, 11259154768866839, 7294620748891626,
    6442943495848725, 7257387842692651, 2321928094887362, 7294620748891626, 2321928094887362, 7257387842692651,
    2321928094887362, 1584962500720924, 9533329732305783, 13440220327914349
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36226261825298145, 35771558906649874, 37613288472195029, 33771978090469910, 40465956761079413, 40465957105044715,
    14269199747347712, 36226261481332843, 36226261825298145, 12260625556068228, 35289084640993420, 37130814206888106,
    33289503824810264, 39761641953492865, 39761642297458169, 9609178738149255, 40465956761079413, 40465957105044715,
    18208496341324438, 14242057605609547, 50475401681547204, 26031175909976768, 50475401649530532, 26031175909976768,
    27876204372564923, 14269199747347712, 31020361163277801, 32862090731350385, 29020780347094645, 36226261481332843,
    36226261825298145, 9548821908460035, 36226261481332843, 36226261825298145, 14242057605609547, 9548821908460035,
    36374360120321979, 36374360464287281, 14269199747347712, 11269711121142782, 18629751479910673, 0
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 25949880489 / 125000000000
noncomputable def negativeCeiling : ℝ := 6740732027 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 92681100083382709697088847872, coefficient := (-92681100083382709697088847872) }, { argument := 135251458776670682650089881600, coefficient := (-135251458776670682650089881600) }, { argument := 484794630698387917648376627200, coefficient := (-484794630698387917648376627200) }, { argument := 135290762620161708057952256000, coefficient := (-135290762620161708057952256000) }, { argument := 3501841811489509055631326183424, coefficient := (-3501841811489509055631326183424) }, { argument := 3501842646393757517744059711488, coefficient := (-3501842646393757517744059711488) }, { argument := 381923844932653648873175121920, coefficient := (-381923844932653648873175121920) }, { argument := 92681077986489152402259705856, coefficient := (-92681077986489152402259705856) }, { argument := 92681100083382709697088847872, coefficient := (-92681100083382709697088847872) }, { argument := 379660735798335063058125160448, coefficient := (-379660735798335063058125160448) }, { argument := 96806101736439067351344742400, coefficient := (-96806101736439067351344742400) }, { argument := 346991291370549098547301580800, coefficient := (-346991291370549098547301580800) }, { argument := 96834233424674001029955584000, coefficient := (-96834233424674001029955584000) }, { argument := 1074599525843347199474849021952, coefficient := (-1074599525843347199474849021952) }, { argument := 1074599782047869796217597722624, coefficient := (-1074599782047869796217597722624) }, { argument := 241707792670470498674054004736, coefficient := (-241707792670470498674054004736) }, { argument := 3501841811489509055631326183424, coefficient := (-3501841811489509055631326183424) }, { argument := 3501842646393757517744059711488, coefficient := (-3501842646393757517744059711488) }, { argument := 5858996120619680334496397262848, coefficient := (-5858996120619680334496397262848) }, { argument := 374805689706762712292505157632, coefficient := (-374805689706762712292505157632) }, { argument := 1762421298494742393546417897472, coefficient := (-1762421298494742393546417897472) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 1762421259382621191897836683264, coefficient := (-1762421259382621191897836683264) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 2326823085676604856269468073984, coefficient := (-2326823085676604856269468073984) }, { argument := 381923844932653648873175121920, coefficient := (-381923844932653648873175121920) }, { argument := 5022141234985211007493734400, coefficient := (-5022141234985211007493734400) }, { argument := 18001337119402368260951244800, coefficient := (-18001337119402368260951244800) }, { argument := 5023600660671817584738304000, coefficient := (-5023600660671817584738304000) }, { argument := 92681077986489152402259705856, coefficient := (-92681077986489152402259705856) }, { argument := 92681100083382709697088847872, coefficient := (-92681100083382709697088847872) }, { argument := 14487767022261716029678813184, coefficient := (-14487767022261716029678813184) }, { argument := 92681077986489152402259705856, coefficient := (-92681077986489152402259705856) }, { argument := 92681100083382709697088847872, coefficient := (-92681100083382709697088847872) }, { argument := 374805689706762712292505157632, coefficient := (-374805689706762712292505157632) }, { argument := 14487767022261716029678813184, coefficient := (-14487767022261716029678813184) }, { argument := 102700653985028520229531025408, coefficient := (-102700653985028520229531025408) }, { argument := 102700678470775435069747101696, coefficient := (-102700678470775435069747101696) }, { argument := 381923844932653648873175121920, coefficient := (-381923844932653648873175121920) }, { argument := 382059244624450487340742213632, coefficient := (-382059244624450487340742213632) }, { argument := 30647402895186738293652848640, coefficient := (-30647402895186738293652848640) }, { argument := 1323268770313242966487371058511872, coefficient := 1323268770313242966487371058511872 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 429990735520531304859492679680, coefficient := 429990735520531304859492679680 }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-29189588475170704019260883846823936)
def positiveArguments : Array ℕ := #[
    19513, 741, 6175, 741, 19513, 38779,
    6175, 598481, 38285, 11115, 19513, 741,
    38285, 741, 19513, 19513, 741, 585,
    2665, 65, 27885, 1235, 65, 1235,
    2405, 45435, 2405, 27885, 45435, 585,
    2405, 2405, 2665, 175, 875, 725,
    13025, 4875, 175, 19525, 19525, 13975,
    725, 305, 335, 305, 335, 1,
    27, 61102621173, 61102620171, 790878271, 45928430807, 12653575993,
    1418351805, 55406081937
  ]
def positiveCoefficients : Array ℕ := #[
    754872624580488290753331593216, 28666049034702086990632845312, 477767483911701449843880755200, 28666049034702086990632845312, 754872624580488290753331593216, 750094949741371276254892785664,
    477767483911701449843880755200, 11576306135180526129717230698496, 740539600063137247258015170560, 429990735520531304859492679680, 754872624580488290753331593216, 28666049034702086990632845312,
    740539600063137247258015170560, 28666049034702086990632845312, 754872624580488290753331593216, 754872624580488290753331593216, 28666049034702086990632845312, 362097461490973730407993835520,
    412388775586942304075770757120, 321864410214198871473772298240, 4314994749434103620695259873280, 382213987129361159875104604160, 321864410214198871473772298240, 382213987129361159875104604160,
    372155724310167445141549219840, 14061451421232813197510427279360, 372155724310167445141549219840, 4314994749434103620695259873280, 14061451421232813197510427279360, 362097461490973730407993835520,
    372155724310167445141549219840, 372155724310167445141549219840, 412388775586942304075770757120, 54159876718735387026836684800, 1083197534374707740536733696000, 56094158030118793706366566400,
    1007760563230754880035068313600, 1508739422879057210033307648000, 54159876718735387026836684800, 1510673704190440616712837529600, 1510673704190440616712837529600, 1081263253063324333857203814400,
    56094158030118793706366566400, 188785855991020491922116444160, 207354956580301196045603307520, 188785855991020491922116444160, 207354956580301196045603307520, 158456325028528675187087900672,
    68453132412324387680821973090304, 288548970242856325433379319185408, 288548965511045109597994815062016, 239028290496018951999444351975424, 867563529015097803991501858930688, 239019292631148753697804241600512,
    6697977024849662868555332321280, 261647824286418069600160450609152
  ]
def positiveScales : Array ℕ := #[
    14, 9, 12, 9, 14, 15,
    12, 19, 15, 13, 14, 9,
    15, 9, 14, 14, 9, 9,
    11, 6, 14, 10, 6, 10,
    11, 15, 11, 14, 15, 9,
    11, 11, 11, 7, 9, 9,
    13, 12, 7, 14, 14, 13,
    9, 8, 8, 8, 8, 0,
    4, 35, 35, 29, 35, 33,
    30, 35
  ]
def negativeArguments : Array ℕ := #[
    247, 65, 25, 5, 1, 27,
    1821, 2123
  ]
def negativeCoefficients : Array ℕ := #[
    19569356141023291385605355732992, 41198644507417455548642854174720, 7922816251426433759354395033600, 792281625142643375935439503360, 158456325028528675187087900672, 68453132412324387680821973090304,
    577097935753901435031374134247424, 1345611112142265509688750452506624
  ]
def negativeScales : Array ℕ := #[
    7, 6, 4, 2, 0, 4,
    10, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14252147979761780, 9533329732305783, 12592223421359118, 9533329732305783, 14252147979761780, 15242987980476304,
    12592223421359118, 19190945921036023, 15224491636858914, 13440220327914349, 14252147979761780, 9533329732305783,
    15224491636858914, 9533329732305783, 14252147979761780, 14252147979761780, 9533329732305783, 9192292814470766,
    11379919817646537, 6022367813028454, 14767201650507785, 10270295326472039, 6022367813028454, 10270295326472039,
    11231821178657404, 15471516458403884, 11231821178657404, 14767201650507785, 15471516458403884, 9192292814470766,
    11231821178657404, 11231821178657404, 11379919817646537, 7451211111832325, 9773139206696762, 9501837184902278,
    13668995752051101, 12251186503524335, 7451211111832325, 14253034927916703, 14253034927916703, 13770560662596204,
    9501837184902278, 8252665432450248, 8388017285345134, 8252665432450248, 8388017285345134, 0,
    4754887502147955, 35830515218732371, 35830515195074131, 29558880416705636, 35418668442085591, 33558826107572042,
    30401568273995402, 35689325298768216
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7948367241724988, 6022367813028455, 4643856189792934, 2321928094887363, 0, 4754887502413606,
    10830515208165348, 11051888655905378
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 931726888593 / 1000000000000
noncomputable def negativeCeiling : ℝ := 52697268559 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 754872624580488290753331593216, coefficient := 754872624580488290753331593216 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 477767483911701449843880755200, coefficient := 477767483911701449843880755200 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 754872624580488290753331593216, coefficient := 754872624580488290753331593216 }, { argument := 750094949741371276254892785664, coefficient := 750094949741371276254892785664 }, { argument := 477767483911701449843880755200, coefficient := 477767483911701449843880755200 }, { argument := 11576306135180526129717230698496, coefficient := 11576306135180526129717230698496 }, { argument := 740539600063137247258015170560, coefficient := 740539600063137247258015170560 }, { argument := 429990735520531304859492679680, coefficient := 429990735520531304859492679680 }, { argument := 754872624580488290753331593216, coefficient := 754872624580488290753331593216 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 740539600063137247258015170560, coefficient := 740539600063137247258015170560 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 754872624580488290753331593216, coefficient := 754872624580488290753331593216 }, { argument := 754872624580488290753331593216, coefficient := 754872624580488290753331593216 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 19569356141023291385605355732992, coefficient := (-19569356141023291385605355732992) }, { argument := 362097461490973730407993835520, coefficient := 362097461490973730407993835520 }, { argument := 412388775586942304075770757120, coefficient := 412388775586942304075770757120 }, { argument := 321864410214198871473772298240, coefficient := 321864410214198871473772298240 }, { argument := 4314994749434103620695259873280, coefficient := 4314994749434103620695259873280 }, { argument := 382213987129361159875104604160, coefficient := 382213987129361159875104604160 }, { argument := 321864410214198871473772298240, coefficient := 321864410214198871473772298240 }, { argument := 382213987129361159875104604160, coefficient := 382213987129361159875104604160 }, { argument := 372155724310167445141549219840, coefficient := 372155724310167445141549219840 }, { argument := 14061451421232813197510427279360, coefficient := 14061451421232813197510427279360 }, { argument := 372155724310167445141549219840, coefficient := 372155724310167445141549219840 }, { argument := 4314994749434103620695259873280, coefficient := 4314994749434103620695259873280 }, { argument := 14061451421232813197510427279360, coefficient := 14061451421232813197510427279360 }, { argument := 362097461490973730407993835520, coefficient := 362097461490973730407993835520 }, { argument := 372155724310167445141549219840, coefficient := 372155724310167445141549219840 }, { argument := 372155724310167445141549219840, coefficient := 372155724310167445141549219840 }, { argument := 412388775586942304075770757120, coefficient := 412388775586942304075770757120 }, { argument := 41198644507417455548642854174720, coefficient := (-41198644507417455548642854174720) }, { argument := 54159876718735387026836684800, coefficient := 54159876718735387026836684800 }, { argument := 1083197534374707740536733696000, coefficient := 1083197534374707740536733696000 }, { argument := 56094158030118793706366566400, coefficient := 56094158030118793706366566400 }, { argument := 1007760563230754880035068313600, coefficient := 1007760563230754880035068313600 }, { argument := 1508739422879057210033307648000, coefficient := 1508739422879057210033307648000 }, { argument := 54159876718735387026836684800, coefficient := 54159876718735387026836684800 }, { argument := 1510673704190440616712837529600, coefficient := 1510673704190440616712837529600 }, { argument := 1510673704190440616712837529600, coefficient := 1510673704190440616712837529600 }, { argument := 1081263253063324333857203814400, coefficient := 1081263253063324333857203814400 }, { argument := 56094158030118793706366566400, coefficient := 56094158030118793706366566400 }, { argument := 7922816251426433759354395033600, coefficient := (-7922816251426433759354395033600) }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 68453132412324387680821973090304, coefficient := 68453132412324387680821973090304 }, { argument := 68453132412324387680821973090304, coefficient := (-68453132412324387680821973090304) }, { argument := 288548970242856325433379319185408, coefficient := 288548970242856325433379319185408 }, { argument := 288548965511045109597994815062016, coefficient := 288548965511045109597994815062016 }, { argument := 577097935753901435031374134247424, coefficient := (-577097935753901435031374134247424) }, { argument := 239028290496018951999444351975424, coefficient := 239028290496018951999444351975424 }, { argument := 867563529015097803991501858930688, coefficient := 867563529015097803991501858930688 }, { argument := 239019292631148753697804241600512, coefficient := 239019292631148753697804241600512 }, { argument := 1345611112142265509688750452506624, coefficient := (-1345611112142265509688750452506624) }, { argument := 6697977024849662868555332321280, coefficient := 6697977024849662868555332321280 }, { argument := 261647824286418069600160450609152, coefficient := 261647824286418069600160450609152 }] }

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


end Parent2

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-33858199475451866210759912019984384)
def positiveArguments : Array ℕ := #[
    55406071207, 1418356235, 849831, 221603521, 4282557957, 443207489,
    849831
  ]
def positiveCoefficients : Array ℕ := #[
    261647773615425708408867307651072, 6697997944933181981083628994560, 32105707444028747692803883008, 4185972160225198253503324094464, 40447616314167006607361540358144, 4185976382020833938966145138688,
    32105707444028747692803883008
  ]
def positiveScales : Array ℕ := #[
    35, 30, 19, 27, 31, 28,
    19
  ]
def negativeArguments : Array ℕ := #[
    3387, 617
  ]
def negativeCoefficients : Array ℕ := #[
    536691572871626622858666719576064, 48883776271301096295216617357312
  ]
def negativeScales : Array ℕ := #[
    11, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    35689325019374352, 30401572780020654, 19696816445443864, 27723405563262053, 31995825623439201, 28723407018302918,
    19696816445443864
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11725792271625417, 9269126679149419
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
noncomputable def positiveFloor : ℝ := 66645401309 / 500000000000
noncomputable def negativeCeiling : ℝ := 2537654877 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 261647773615425708408867307651072, coefficient := 261647773615425708408867307651072 }, { argument := 6697997944933181981083628994560, coefficient := 6697997944933181981083628994560 }, { argument := 536691572871626622858666719576064, coefficient := (-536691572871626622858666719576064) }, { argument := 32105707444028747692803883008, coefficient := 32105707444028747692803883008 }, { argument := 4185972160225198253503324094464, coefficient := 4185972160225198253503324094464 }, { argument := 40447616314167006607361540358144, coefficient := 40447616314167006607361540358144 }, { argument := 4185976382020833938966145138688, coefficient := 4185976382020833938966145138688 }, { argument := 32105707444028747692803883008, coefficient := 32105707444028747692803883008 }, { argument := 48883776271301096295216617357312, coefficient := (-48883776271301096295216617357312) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19
