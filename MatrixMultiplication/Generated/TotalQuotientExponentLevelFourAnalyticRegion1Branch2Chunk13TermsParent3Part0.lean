import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 13, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-59645577321615324841298500125720576)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    167920715, 1175, 2946502931, 29075, 925, 11785974601,
    475, 475, 16075, 875, 29075, 16075,
    335880149, 925, 875, 1175, 141984035396927669, 665,
    217, 241716123840792943, 2191, 141984030795770989, 4389, 1967,
    665, 217, 17760719852091603, 1531098977, 17760639966223149, 773069621,
    1531098977, 5477405499, 382774617, 665, 665, 168144741,
    217, 217, 141, 141983430159785803, 665, 217,
    241715023892031121, 2191, 141983425558631315, 4389, 1967, 665,
    217, 120947961547661765, 5477405499, 120947380792170043, 2765605527, 2952595335,
    2191, 2191, 3489, 111, 35521438558088341, 382774617,
    35521278786351979, 193267341, 5905172111, 57
  ]
def negativeCoefficients : Array ℕ := #[
    1585966312591012152160320225280, 22727805408755028484476108800, 55657866732126283652341541371904, 562392291284725492073313075200, 17892102130296511785651404800, 55657691423715340082502273335296,
    18375672458142363455533875200, 18375672458142363455533875200, 310935720804882623734428467200, 16924961474604808445886464000, 562392291284725492073313075200, 310935720804882623734428467200,
    1586149157898862381953349320704, 17892102130296511785651404800, 16924961474604808445886464000, 22727805408755028484476108800, 39964953056635172764549973540864, 51451882882798617675494850560,
    2098695222850996247289921536, 136074080657354470312193835401216, 42380103532410440348499705856, 39964951761524703419470691958784, 42447803378308859582283251712, 38047313394911609386352771072,
    51451882882798617675494850560, 2098695222850996247289921536, 39993585653855757051476305772544, 3530473872529688384298287104, 39993405766872056250045617405952, 3565154362436659782965264384,
    3530473872529688384298287104, 12630037178497794918787842048, 3530472698855596694528065536, 51451882882798617675494850560, 51451882882798617675494850560, 1588082178338394862437607145472,
    2098695222850996247289921536, 2098695222850996247289921536, 21818693192404827345097064448, 39964782697524761608198467616768, 51451882882798617675494850560, 2098695222850996247289921536,
    136073461441250236787486728650752, 42380103532410440348499705856, 39964781402414909256268135792640, 42447803378308859582283251712, 38047313394911609386352771072, 51451882882798617675494850560,
    2098695222850996247289921536, 136175298639317650884431037071360, 12630037178497794918787842048, 136174644766763622742337448312832, 12754104341351407835475345408, 55772948989925087484255550832640,
    42380103532410440348499705856, 42380103532410440348499705856, 539896599633336472390380552192, 17176418045084651314225348608, 39993584363467655315166576246784, 3530472698855596694528065536,
    39993404476484569255085023952896, 3565153177233353047126573056, 55772773705125976328764508864512, 17640645559816668917312520192
  ]
def negativeScales : Array ℕ := #[
    27, 10, 31, 14, 9, 33,
    8, 8, 13, 9, 14, 13,
    28, 9, 9, 10, 56, 9,
    7, 57, 11, 56, 12, 10,
    9, 7, 53, 30, 53, 29,
    30, 32, 28, 9, 9, 27,
    7, 7, 7, 56, 9, 7,
    57, 11, 56, 12, 10, 9,
    7, 56, 32, 56, 31, 31,
    11, 11, 11, 6, 54, 28,
    54, 27, 32, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27323204973795143, 10198445041452363, 31456356555280901, 14827491572368013, 9853309557248504, 33456352011143868,
    8891783706984896, 8891783706984896, 13972531132277330, 9773139207089529, 14827491572368013, 13972531132277330,
    28323371291838500, 9853309557248504, 9773139207089529, 10198445041452363, 56978506352871961, 9377210530388555,
    7761551232733342, 57746091325572932, 11097373768990223, 56978506306119748, 12099676554859644, 10941781251345720,
    9377210530388555, 7761551232733342, 53979539591343644, 30511920402018066, 53979533102235183, 29526023105136479,
    30511920402018066, 32350845542777270, 28511919922407075, 9377210530388555, 9377210530388555, 27325128416037325,
    7761551232733342, 7761551232733342, 7139551352398794, 56978500203062791, 9377210530388555, 7761551232733342,
    57746084760457554, 11097373768990223, 56978500156310401, 12099676554859644, 10941781251345720, 9377210530388555,
    7761551232733342, 56747164067691957, 32350845542777270, 56747157140290514, 31364948245895453, 31459336496880979,
    11097373768990223, 11097373768990223, 11768597882530236, 6794415866926375, 54979539544795253, 28511919922407075,
    54979533055686605, 27526022625525488, 32459331962731138, 5832890015409720
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
noncomputable def negativeCeiling : ℝ := 678240563737 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1585966312591012152160320225280, coefficient := (-1585966312591012152160320225280) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 55657866732126283652341541371904, coefficient := (-55657866732126283652341541371904) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 55657691423715340082502273335296, coefficient := (-55657691423715340082502273335296) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 562392291284725492073313075200, coefficient := (-562392291284725492073313075200) }, { argument := 310935720804882623734428467200, coefficient := (-310935720804882623734428467200) }, { argument := 1586149157898862381953349320704, coefficient := (-1586149157898862381953349320704) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 16924961474604808445886464000, coefficient := (-16924961474604808445886464000) }, { argument := 22727805408755028484476108800, coefficient := (-22727805408755028484476108800) }, { argument := 39964953056635172764549973540864, coefficient := (-39964953056635172764549973540864) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 136074080657354470312193835401216, coefficient := (-136074080657354470312193835401216) }, { argument := 42380103532410440348499705856, coefficient := (-42380103532410440348499705856) }, { argument := 39964951761524703419470691958784, coefficient := (-39964951761524703419470691958784) }, { argument := 42447803378308859582283251712, coefficient := (-42447803378308859582283251712) }, { argument := 38047313394911609386352771072, coefficient := (-38047313394911609386352771072) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 39993585653855757051476305772544, coefficient := (-39993585653855757051476305772544) }, { argument := 3530473872529688384298287104, coefficient := (-3530473872529688384298287104) }, { argument := 39993405766872056250045617405952, coefficient := (-39993405766872056250045617405952) }, { argument := 3565154362436659782965264384, coefficient := (-3565154362436659782965264384) }, { argument := 3530473872529688384298287104, coefficient := (-3530473872529688384298287104) }, { argument := 12630037178497794918787842048, coefficient := (-12630037178497794918787842048) }, { argument := 3530472698855596694528065536, coefficient := (-3530472698855596694528065536) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 1588082178338394862437607145472, coefficient := (-1588082178338394862437607145472) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 21818693192404827345097064448, coefficient := (-21818693192404827345097064448) }, { argument := 39964782697524761608198467616768, coefficient := (-39964782697524761608198467616768) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 136073461441250236787486728650752, coefficient := (-136073461441250236787486728650752) }, { argument := 42380103532410440348499705856, coefficient := (-42380103532410440348499705856) }, { argument := 39964781402414909256268135792640, coefficient := (-39964781402414909256268135792640) }, { argument := 42447803378308859582283251712, coefficient := (-42447803378308859582283251712) }, { argument := 38047313394911609386352771072, coefficient := (-38047313394911609386352771072) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 136175298639317650884431037071360, coefficient := (-136175298639317650884431037071360) }, { argument := 12630037178497794918787842048, coefficient := (-12630037178497794918787842048) }, { argument := 136174644766763622742337448312832, coefficient := (-136174644766763622742337448312832) }, { argument := 12754104341351407835475345408, coefficient := (-12754104341351407835475345408) }, { argument := 55772948989925087484255550832640, coefficient := (-55772948989925087484255550832640) }, { argument := 42380103532410440348499705856, coefficient := (-42380103532410440348499705856) }, { argument := 42380103532410440348499705856, coefficient := (-42380103532410440348499705856) }, { argument := 539896599633336472390380552192, coefficient := (-539896599633336472390380552192) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 39993584363467655315166576246784, coefficient := (-39993584363467655315166576246784) }, { argument := 3530472698855596694528065536, coefficient := (-3530472698855596694528065536) }, { argument := 39993404476484569255085023952896, coefficient := (-39993404476484569255085023952896) }, { argument := 3565153177233353047126573056, coefficient := (-3565153177233353047126573056) }, { argument := 55772773705125976328764508864512, coefficient := (-55772773705125976328764508864512) }, { argument := 17640645559816668917312520192, coefficient := (-17640645559816668917312520192) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 57914605287319349088349719726391296
def positiveArguments : Array ℕ := #[
    6931, 735, 91612205121, 509, 91611787199, 257,
    33866689299, 665, 217, 57656289041, 2191, 33866688203,
    4389, 1967, 665, 217, 21004091, 2303,
    2949549133, 56987, 1813, 23596318823, 931, 931,
    31507, 1715, 56987, 31507, 672208337, 1813,
    1715, 2303
  ]
def positiveCoefficients : Array ℕ := #[
    1098260788772732247721706239557632, 232930797791937152525019213987840, 432626406885189270021613830537216, 39381967499766159995228389376, 432624433304344016173746832277504, 39768823762042841331134365696,
    159930918431357680370604891439104, 205807531531194470701979402240, 8394780891403984989159686144, 544548253787725679131957575811072, 169520414129641761393998823424, 159930913255644015145473737228288,
    169791213513235438329133006848, 152189253579646437545411084288, 205807531531194470701979402240, 8394780891403984989159686144, 3174048490929407014597927370752, 44546498601159855829573173248,
    111430815722051371136597092204544, 1102288890918061964463693627392, 35068520175381163099876753408, 111430465128841316411266782199808, 36016318017959032372846395392, 36016318017959032372846395392,
    609434012777569942519479795712, 33172924490225424553937469440, 1102288890918061964463693627392, 609434012777569942519479795712, 3174414120154343196878597783552, 35068520175381163099876753408,
    33172924490225424553937469440, 44546498601159855829573173248
  ]
def positiveScales : Array ℕ := #[
    12, 9, 36, 8, 36, 8,
    34, 9, 7, 35, 11, 34,
    12, 10, 9, 7, 24, 11,
    31, 15, 10, 34, 9, 9,
    14, 10, 15, 14, 29, 10,
    10, 11
  ]
def negativeArguments : Array ℕ := #[
    773069621, 2765605527, 193267341, 4389, 4389, 57,
    1967, 1967, 1929, 105, 665, 665,
    3489, 1929, 84082047, 217, 217, 111,
    105, 141, 735, 5461, 5461, 735
  ]
def negativeCoefficients : Array ℕ := #[
    3565154362436659782965264384, 12754104341351407835475345408, 3565153177233353047126573056, 42447803378308859582283251712, 42447803378308859582283251712, 17640645559816668917312520192,
    38047313394911609386352771072, 38047313394911609386352771072, 298498291972687318785051328512, 16247963015620616108051005440, 51451882882798617675494850560, 51451882882798617675494850560,
    539896599633336472390380552192, 298498291972687318785051328512, 1588264962255480814925248462848, 2098695222850996247289921536, 2098695222850996247289921536, 17176418045084651314225348608,
    16247963015620616108051005440, 21818693192404827345097064448, 232930797791937152525019213987840, 865329990980795095196687025569792, 865329990980795095196687025569792, 232930797791937152525019213987840
  ]
def negativeScales : Array ℕ := #[
    29, 31, 27, 12, 12, 5,
    10, 10, 10, 6, 9, 9,
    11, 10, 26, 7, 7, 6,
    6, 7, 9, 12, 12, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12758847803091420, 9521600439723692, 36414820764385242, 8991521844801183, 36414814182998283, 8005624549193878,
    34979147908227087, 9377210530388551, 7761551232426566, 35746758931818379, 11097373768990222, 34979147861538326,
    12099676554859642, 10941781241718677, 9377210530388551, 7761551232426566, 24324167015464727, 11169298695792845,
    31457847295478606, 15798345225549727, 10824163209679199, 34457842756340326, 9862637357422660, 9862637357422660,
    14943384770867824, 10743992861047947, 15798345225549727, 14943384770867824, 29324333194743874, 10824163209679199,
    10743992861047947, 11169298695792845
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29526023105136479, 31364948245895453, 27526022625525488, 12099676554859644, 12099676554859644, 5832890015409720,
    10941781251345720, 10941781251345720, 10913637433615165, 6714245517766967, 9377210530388555, 9377210530388555,
    11768597882530236, 10913637433615165, 26325294456737131, 7761551232733342, 7761551232733342, 6794415866926375,
    6714245517766967, 7139551352398794, 9521600439724276, 12414949441474276, 12414949441474276, 9521600439724276
  ]

abbrev PositiveTerm := Fin 32
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 1034880418149 / 1000000000000
noncomputable def negativeCeiling : ℝ := 31272936587 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3565154362436659782965264384, coefficient := (-3565154362436659782965264384) }, { argument := 12754104341351407835475345408, coefficient := (-12754104341351407835475345408) }, { argument := 3565153177233353047126573056, coefficient := (-3565153177233353047126573056) }, { argument := 42447803378308859582283251712, coefficient := (-42447803378308859582283251712) }, { argument := 42447803378308859582283251712, coefficient := (-42447803378308859582283251712) }, { argument := 17640645559816668917312520192, coefficient := (-17640645559816668917312520192) }, { argument := 38047313394911609386352771072, coefficient := (-38047313394911609386352771072) }, { argument := 38047313394911609386352771072, coefficient := (-38047313394911609386352771072) }, { argument := 298498291972687318785051328512, coefficient := (-298498291972687318785051328512) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 51451882882798617675494850560, coefficient := (-51451882882798617675494850560) }, { argument := 539896599633336472390380552192, coefficient := (-539896599633336472390380552192) }, { argument := 298498291972687318785051328512, coefficient := (-298498291972687318785051328512) }, { argument := 1588264962255480814925248462848, coefficient := (-1588264962255480814925248462848) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 16247963015620616108051005440, coefficient := (-16247963015620616108051005440) }, { argument := 21818693192404827345097064448, coefficient := (-21818693192404827345097064448) }, { argument := 1098260788772732247721706239557632, coefficient := 1098260788772732247721706239557632 }, { argument := 232930797791937152525019213987840, coefficient := 232930797791937152525019213987840 }, { argument := 232930797791937152525019213987840, coefficient := (-232930797791937152525019213987840) }, { argument := 432626406885189270021613830537216, coefficient := 432626406885189270021613830537216 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 432624433304344016173746832277504, coefficient := 432624433304344016173746832277504 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 865329990980795095196687025569792, coefficient := (-865329990980795095196687025569792) }, { argument := 159930918431357680370604891439104, coefficient := 159930918431357680370604891439104 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 544548253787725679131957575811072, coefficient := 544548253787725679131957575811072 }, { argument := 169520414129641761393998823424, coefficient := 169520414129641761393998823424 }, { argument := 159930913255644015145473737228288, coefficient := 159930913255644015145473737228288 }, { argument := 169791213513235438329133006848, coefficient := 169791213513235438329133006848 }, { argument := 152189253579646437545411084288, coefficient := 152189253579646437545411084288 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 865329990980795095196687025569792, coefficient := (-865329990980795095196687025569792) }, { argument := 3174048490929407014597927370752, coefficient := 3174048490929407014597927370752 }, { argument := 44546498601159855829573173248, coefficient := 44546498601159855829573173248 }, { argument := 111430815722051371136597092204544, coefficient := 111430815722051371136597092204544 }, { argument := 1102288890918061964463693627392, coefficient := 1102288890918061964463693627392 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 111430465128841316411266782199808, coefficient := 111430465128841316411266782199808 }, { argument := 36016318017959032372846395392, coefficient := 36016318017959032372846395392 }, { argument := 36016318017959032372846395392, coefficient := 36016318017959032372846395392 }, { argument := 609434012777569942519479795712, coefficient := 609434012777569942519479795712 }, { argument := 33172924490225424553937469440, coefficient := 33172924490225424553937469440 }, { argument := 1102288890918061964463693627392, coefficient := 1102288890918061964463693627392 }, { argument := 609434012777569942519479795712, coefficient := 609434012777569942519479795712 }, { argument := 3174414120154343196878597783552, coefficient := 3174414120154343196878597783552 }, { argument := 35068520175381163099876753408, coefficient := 35068520175381163099876753408 }, { argument := 33172924490225424553937469440, coefficient := 33172924490225424553937469440 }, { argument := 44546498601159855829573173248, coefficient := 44546498601159855829573173248 }, { argument := 232930797791937152525019213987840, coefficient := (-232930797791937152525019213987840) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
