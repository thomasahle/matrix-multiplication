import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-161723488227489023497733765332992)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7807, 40075, 40919, 9283973, 634063801, 25055787169,
    2536256103, 9283973, 79069, 59089, 62419, 40367,
    1081177, 1923371, 58275, 1081177, 7807, 31635,
    62419, 61605, 1923371, 61605, 79069, 40367,
    2468035, 1844431, 1948365, 1260001, 33747399, 60028245,
    1818845, 33747399, 243645, 987373, 1948365, 1922779,
    60028245, 1922779, 2468035, 1260001, 94220623, 6441530663,
    254610599447, 25766131729, 94220623, 79069, 59089, 62419,
    40367, 1081177, 1923371, 58275, 1081177, 7807,
    31635, 62419, 61605, 1923371, 61605, 79069,
    40367, 190288227, 12989456787, 513228039603
  ]
def negativeCoefficients : Array ℕ := #[
    294940121054106561466597376, 378497673602002063877734400, 386469028225086024998453248, 21407384239778685880631296, 2924103165862625616911663104, 28887355841992410850807250944,
    2924104202339058258467094528, 21407384239778685880631296, 373392795434019977401729024, 279039913106284466032082944, 294765393494240384593690624, 381255535627997936682532864,
    5105714026849554403208200192, 9082862744523472384311689216, 275195906789228574828134400, 5105714026849554403208200192, 294940121054106561466597376, 298784127371162452670545920,
    294765393494240384593690624, 290921387177184493389742080, 9082862744523472384311689216, 290921387177184493389742080, 373392795434019977401729024, 381255535627997936682532864,
    11654965762549184824984207360, 8710079134365742591142526976, 9200893572396316296782807040, 11900372981564471677804347392, 159367585921628582015039176704, 283475372213487365950820843520,
    8589252665535039848704901120, 159367585921628582015039176704, 9204647853750197664727695360, 9325474322580900407165321216, 9200893572396316296782807040, 9080067103565613554345181184,
    283475372213487365950820843520, 9080067103565613554345181184, 11654965762549184824984207360, 11900372981564471677804347392, 434515929736617968577544192, 59412633791656804445222600704,
    587092070806572961239918444544, 59412654721793799077922603008, 434515929736617968577544192, 373392795434019977401729024, 279039913106284466032082944, 294765393494240384593690624,
    381255535627997936682532864, 5105714026849554403208200192, 9082862744523472384311689216, 275195906789228574828134400, 5105714026849554403208200192, 294940121054106561466597376,
    298784127371162452670545920, 294765393494240384593690624, 290921387177184493389742080, 9082862744523472384311689216, 290921387177184493389742080, 373392795434019977401729024,
    381255535627997936682532864, 438774777963618486246703104, 59903296251574640876294504448, 591711643625513206743488790528
  ]
def negativeScales : Array ℕ := #[
    12, 15, 15, 23, 29, 34,
    31, 23, 16, 15, 15, 15,
    20, 20, 15, 20, 12, 14,
    15, 15, 20, 15, 16, 15,
    21, 20, 20, 20, 25, 25,
    20, 25, 17, 19, 20, 20,
    25, 20, 21, 20, 26, 32,
    37, 34, 26, 16, 15, 15,
    15, 20, 20, 15, 20, 12,
    14, 15, 15, 20, 15, 16,
    15, 27, 33, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12930552561813914, 15290414899929273, 15320483267724837, 23146310896312608, 29240052774156383, 34544424812005373,
    31240053285533397, 23146310896312608, 16270824558288761, 15850601964792316, 15929697631284590, 15300888751952558,
    20044171296021888, 20875205643797866, 15830589480093830, 20044171296021888, 12930552561813914, 14949233985692235,
    15929697631284590, 15910759832877788, 20875205643797866, 15910759832877788, 16270824558288761, 15300888751952558,
    21234931423280060, 20814744389142979, 20893832545500574, 20264993448044976, 25008272978392689, 25839138155224452,
    20794591173222159, 25008272978392689, 17894421094723376, 19913235674669191, 20893832545500574, 20874761524086105,
    25839138155224452, 20874761524086105, 21234931423280060, 20264993448044976, 26489539535551450, 32584756402194486,
    37889501527302741, 34584756910433182, 26489539535551450, 16270824558288761, 15850601964792316, 15929697631284590,
    15300888751952558, 20044171296021888, 20875205643797866, 15830589480093830, 20044171296021888, 12930552561813914,
    14949233985692235, 15929697631284590, 15910759832877788, 20875205643797866, 15910759832877788, 16270824558288761,
    15300888751952558, 27503611064935386, 33596622048095066, 38900809040699353
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
noncomputable def negativeCeiling : ℝ := 949132887 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 294940121054106561466597376, coefficient := (-294940121054106561466597376) }, { argument := 378497673602002063877734400, coefficient := (-378497673602002063877734400) }, { argument := 386469028225086024998453248, coefficient := (-386469028225086024998453248) }, { argument := 21407384239778685880631296, coefficient := (-21407384239778685880631296) }, { argument := 2924103165862625616911663104, coefficient := (-2924103165862625616911663104) }, { argument := 28887355841992410850807250944, coefficient := (-28887355841992410850807250944) }, { argument := 2924104202339058258467094528, coefficient := (-2924104202339058258467094528) }, { argument := 21407384239778685880631296, coefficient := (-21407384239778685880631296) }, { argument := 373392795434019977401729024, coefficient := (-373392795434019977401729024) }, { argument := 279039913106284466032082944, coefficient := (-279039913106284466032082944) }, { argument := 294765393494240384593690624, coefficient := (-294765393494240384593690624) }, { argument := 381255535627997936682532864, coefficient := (-381255535627997936682532864) }, { argument := 5105714026849554403208200192, coefficient := (-5105714026849554403208200192) }, { argument := 9082862744523472384311689216, coefficient := (-9082862744523472384311689216) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 5105714026849554403208200192, coefficient := (-5105714026849554403208200192) }, { argument := 294940121054106561466597376, coefficient := (-294940121054106561466597376) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 294765393494240384593690624, coefficient := (-294765393494240384593690624) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 9082862744523472384311689216, coefficient := (-9082862744523472384311689216) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 373392795434019977401729024, coefficient := (-373392795434019977401729024) }, { argument := 381255535627997936682532864, coefficient := (-381255535627997936682532864) }, { argument := 11654965762549184824984207360, coefficient := (-11654965762549184824984207360) }, { argument := 8710079134365742591142526976, coefficient := (-8710079134365742591142526976) }, { argument := 9200893572396316296782807040, coefficient := (-9200893572396316296782807040) }, { argument := 11900372981564471677804347392, coefficient := (-11900372981564471677804347392) }, { argument := 159367585921628582015039176704, coefficient := (-159367585921628582015039176704) }, { argument := 283475372213487365950820843520, coefficient := (-283475372213487365950820843520) }, { argument := 8589252665535039848704901120, coefficient := (-8589252665535039848704901120) }, { argument := 159367585921628582015039176704, coefficient := (-159367585921628582015039176704) }, { argument := 9204647853750197664727695360, coefficient := (-9204647853750197664727695360) }, { argument := 9325474322580900407165321216, coefficient := (-9325474322580900407165321216) }, { argument := 9200893572396316296782807040, coefficient := (-9200893572396316296782807040) }, { argument := 9080067103565613554345181184, coefficient := (-9080067103565613554345181184) }, { argument := 283475372213487365950820843520, coefficient := (-283475372213487365950820843520) }, { argument := 9080067103565613554345181184, coefficient := (-9080067103565613554345181184) }, { argument := 11654965762549184824984207360, coefficient := (-11654965762549184824984207360) }, { argument := 11900372981564471677804347392, coefficient := (-11900372981564471677804347392) }, { argument := 434515929736617968577544192, coefficient := (-434515929736617968577544192) }, { argument := 59412633791656804445222600704, coefficient := (-59412633791656804445222600704) }, { argument := 587092070806572961239918444544, coefficient := (-587092070806572961239918444544) }, { argument := 59412654721793799077922603008, coefficient := (-59412654721793799077922603008) }, { argument := 434515929736617968577544192, coefficient := (-434515929736617968577544192) }, { argument := 373392795434019977401729024, coefficient := (-373392795434019977401729024) }, { argument := 279039913106284466032082944, coefficient := (-279039913106284466032082944) }, { argument := 294765393494240384593690624, coefficient := (-294765393494240384593690624) }, { argument := 381255535627997936682532864, coefficient := (-381255535627997936682532864) }, { argument := 5105714026849554403208200192, coefficient := (-5105714026849554403208200192) }, { argument := 9082862744523472384311689216, coefficient := (-9082862744523472384311689216) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 5105714026849554403208200192, coefficient := (-5105714026849554403208200192) }, { argument := 294940121054106561466597376, coefficient := (-294940121054106561466597376) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 294765393494240384593690624, coefficient := (-294765393494240384593690624) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 9082862744523472384311689216, coefficient := (-9082862744523472384311689216) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 373392795434019977401729024, coefficient := (-373392795434019977401729024) }, { argument := 381255535627997936682532864, coefficient := (-381255535627997936682532864) }, { argument := 438774777963618486246703104, coefficient := (-438774777963618486246703104) }, { argument := 59903296251574640876294504448, coefficient := (-59903296251574640876294504448) }, { argument := 591711643625513206743488790528, coefficient := (-591711643625513206743488790528) }] }

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

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-143900207792075120872709079171072)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    51957845621, 190288227, 1552398735, 60753975665, 60753987185, 1552410255,
    19246324539, 54677623, 622266733789, 22764497, 2240959, 22742909,
    45931641, 2412507133, 54677623, 2240959, 2141511984613, 83287409187355,
    20035, 51829, 86761, 1234975, 20817516512223, 86761,
    40105, 20311, 20035, 39553, 1234975, 39553,
    535376870433, 51829, 2453484669, 1139695402487, 11875590632607, 569848987067,
    2453484669, 103657, 77461, 81827, 6615, 1417397,
    2521933, 76405, 1417397, 40949, 41477, 81827,
    80771, 2521933, 80771, 103657, 6615, 226521581,
    7727921885, 152651992345, 241497645, 226521581, 773638995, 30276787757,
    30276793517, 773644755, 9283973, 634063801
  ]
def negativeCoefficients : Array ℕ := #[
    59903317549493595478578692096, 438774777963618486246703104, 7159175541223863671523901440, 280178260138158266289131356160, 280178313264781198572640010240, 7159228667846795955032555520,
    43338870011046016604700672, 504312059019887537379344384, 1401220115208598016252444672, 419930850125728866633777152, 20669198576338041539919872, 419532621814665624833490944,
    423644613206252331548540928, 43459864900829854534991872, 504312059019887537379344384, 20669198576338041539919872, 602782035994534885225136128, 23443321561301625191928954880,
    378450449937173367425597440, 489511064881301683561299968, 6555475814724052614167658496, 11664009094363880195568435200, 23438439901806662584633393152, 6555475814724052614167658496,
    378781015590974242590556160, 383663942534261455741517824, 378450449937173367425597440, 373567522993886154274635776, 11664009094363880195568435200, 373567522993886154274635776,
    602780768546210279369736192, 489511064881301683561299968, 44198050564270498875703296, 10265463579912641320377647104, 106965811095626876129214726144, 10265486743249583177285500928,
    44198050564270498875703296, 489506342514818813916086272, 365799230129565587898105856, 386417082193774458901102592, 499815268546923249417584640, 6693468085719986516957069312,
    11909491871242892962711994368, 360812411123655242552442880, 6693468085719986516957069312, 386752370214058203711275008, 391739189219968549056937984, 386417082193774458901102592,
    381430263187864113555439616, 11909491871242892962711994368, 381430263187864113555439616, 489506342514818813916086272, 499815268546923249417584640, 522323203984883520857178112,
    71277498617107048533411758080, 703983058782521147259753594880, 71277524027497010068319109120, 522323203984883520857178112, 7135560273103431717051432960, 279254077563700828970634182656,
    279254130690323761254142836736, 7135613399726364000560087040, 21407384239778685880631296, 2924103165862625616911663104
  ]
def negativeScales : Array ℕ := #[
    35, 27, 30, 35, 35, 30,
    34, 25, 39, 24, 21, 24,
    25, 31, 25, 21, 40, 46,
    14, 15, 16, 20, 44, 16,
    15, 14, 14, 15, 20, 15,
    38, 15, 31, 40, 43, 39,
    31, 16, 16, 16, 12, 20,
    21, 16, 20, 15, 15, 16,
    16, 21, 16, 16, 12, 27,
    32, 37, 27, 27, 29, 34,
    34, 29, 23, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35596622561028386, 27503611064935386, 30531852016617525, 35822259769869925, 35822260043429728, 30531862722491494,
    34163863910232334, 25704447190325615, 39178742165961748, 24440282246405373, 21095684823242640, 24438913462481322,
    25452984991865164, 31167886061953928, 25704447190325615, 21095684823242640, 40961766902399049, 46243163648983660,
    14290234889318161, 15661471937897105, 16404759061037361, 20236050406485479, 44242863201826798, 16404759061037361,
    15291494492177873, 14309973651164077, 14290234889318161, 15271499503349441, 20236050406485479, 15271499503349441,
    38961763868891724, 15661471937897105, 31192185110504782, 40051785436688128, 43433064501214528, 39051788692030020,
    31192185110504782, 16661458019993992, 16241182505828290, 16320289339328739, 12691525441225267, 20434812469932088,
    21266098517531261, 16221379431935758, 20434812469932088, 15321540600337431, 15340023928434378, 16320289339328739,
    16301549780619742, 21266098517531261, 16301549780619742, 16661458019993992, 12691525441225267, 27755073263566388,
    32847433366903754, 37151455462833972, 27847433881223686, 27755073263566388, 29527085274280473, 34817493099208883,
    34817493373674023, 29527096015585597, 23146310896312608, 29240052774156383
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
noncomputable def negativeCeiling : ℝ := 496268993 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59903317549493595478578692096, coefficient := (-59903317549493595478578692096) }, { argument := 438774777963618486246703104, coefficient := (-438774777963618486246703104) }, { argument := 7159175541223863671523901440, coefficient := (-7159175541223863671523901440) }, { argument := 280178260138158266289131356160, coefficient := (-280178260138158266289131356160) }, { argument := 280178313264781198572640010240, coefficient := (-280178313264781198572640010240) }, { argument := 7159228667846795955032555520, coefficient := (-7159228667846795955032555520) }, { argument := 43338870011046016604700672, coefficient := (-43338870011046016604700672) }, { argument := 504312059019887537379344384, coefficient := (-504312059019887537379344384) }, { argument := 1401220115208598016252444672, coefficient := (-1401220115208598016252444672) }, { argument := 419930850125728866633777152, coefficient := (-419930850125728866633777152) }, { argument := 20669198576338041539919872, coefficient := (-20669198576338041539919872) }, { argument := 419532621814665624833490944, coefficient := (-419532621814665624833490944) }, { argument := 423644613206252331548540928, coefficient := (-423644613206252331548540928) }, { argument := 43459864900829854534991872, coefficient := (-43459864900829854534991872) }, { argument := 504312059019887537379344384, coefficient := (-504312059019887537379344384) }, { argument := 20669198576338041539919872, coefficient := (-20669198576338041539919872) }, { argument := 602782035994534885225136128, coefficient := (-602782035994534885225136128) }, { argument := 23443321561301625191928954880, coefficient := (-23443321561301625191928954880) }, { argument := 378450449937173367425597440, coefficient := (-378450449937173367425597440) }, { argument := 489511064881301683561299968, coefficient := (-489511064881301683561299968) }, { argument := 6555475814724052614167658496, coefficient := (-6555475814724052614167658496) }, { argument := 11664009094363880195568435200, coefficient := (-11664009094363880195568435200) }, { argument := 23438439901806662584633393152, coefficient := (-23438439901806662584633393152) }, { argument := 6555475814724052614167658496, coefficient := (-6555475814724052614167658496) }, { argument := 378781015590974242590556160, coefficient := (-378781015590974242590556160) }, { argument := 383663942534261455741517824, coefficient := (-383663942534261455741517824) }, { argument := 378450449937173367425597440, coefficient := (-378450449937173367425597440) }, { argument := 373567522993886154274635776, coefficient := (-373567522993886154274635776) }, { argument := 11664009094363880195568435200, coefficient := (-11664009094363880195568435200) }, { argument := 373567522993886154274635776, coefficient := (-373567522993886154274635776) }, { argument := 602780768546210279369736192, coefficient := (-602780768546210279369736192) }, { argument := 489511064881301683561299968, coefficient := (-489511064881301683561299968) }, { argument := 44198050564270498875703296, coefficient := (-44198050564270498875703296) }, { argument := 10265463579912641320377647104, coefficient := (-10265463579912641320377647104) }, { argument := 106965811095626876129214726144, coefficient := (-106965811095626876129214726144) }, { argument := 10265486743249583177285500928, coefficient := (-10265486743249583177285500928) }, { argument := 44198050564270498875703296, coefficient := (-44198050564270498875703296) }, { argument := 489506342514818813916086272, coefficient := (-489506342514818813916086272) }, { argument := 365799230129565587898105856, coefficient := (-365799230129565587898105856) }, { argument := 386417082193774458901102592, coefficient := (-386417082193774458901102592) }, { argument := 499815268546923249417584640, coefficient := (-499815268546923249417584640) }, { argument := 6693468085719986516957069312, coefficient := (-6693468085719986516957069312) }, { argument := 11909491871242892962711994368, coefficient := (-11909491871242892962711994368) }, { argument := 360812411123655242552442880, coefficient := (-360812411123655242552442880) }, { argument := 6693468085719986516957069312, coefficient := (-6693468085719986516957069312) }, { argument := 386752370214058203711275008, coefficient := (-386752370214058203711275008) }, { argument := 391739189219968549056937984, coefficient := (-391739189219968549056937984) }, { argument := 386417082193774458901102592, coefficient := (-386417082193774458901102592) }, { argument := 381430263187864113555439616, coefficient := (-381430263187864113555439616) }, { argument := 11909491871242892962711994368, coefficient := (-11909491871242892962711994368) }, { argument := 381430263187864113555439616, coefficient := (-381430263187864113555439616) }, { argument := 489506342514818813916086272, coefficient := (-489506342514818813916086272) }, { argument := 499815268546923249417584640, coefficient := (-499815268546923249417584640) }, { argument := 522323203984883520857178112, coefficient := (-522323203984883520857178112) }, { argument := 71277498617107048533411758080, coefficient := (-71277498617107048533411758080) }, { argument := 703983058782521147259753594880, coefficient := (-703983058782521147259753594880) }, { argument := 71277524027497010068319109120, coefficient := (-71277524027497010068319109120) }, { argument := 522323203984883520857178112, coefficient := (-522323203984883520857178112) }, { argument := 7135560273103431717051432960, coefficient := (-7135560273103431717051432960) }, { argument := 279254077563700828970634182656, coefficient := (-279254077563700828970634182656) }, { argument := 279254130690323761254142836736, coefficient := (-279254130690323761254142836736) }, { argument := 7135613399726364000560087040, coefficient := (-7135613399726364000560087040) }, { argument := 21407384239778685880631296, coefficient := (-21407384239778685880631296) }, { argument := 2924103165862625616911663104, coefficient := (-2924103165862625616911663104) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
