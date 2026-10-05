import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 11, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 3639966655951826989049886869028864
def positiveArguments : Array ℕ := #[
    107, 217, 665, 1967, 4389, 217,
    2191, 4459, 217, 665, 217, 1285,
    5125, 2545, 5125, 5, 15, 15,
    15, 15, 651, 15771, 11949, 6657,
    651, 6657, 13293, 651, 15771, 651,
    75, 225, 475, 1225, 1025, 28675,
    875, 1025, 925, 475, 475
  ]
def positiveCoefficients : Array ℕ := #[
    33909653556105136490036810743808, 8394780891403984989159686144, 205807531531194470701979402240, 152189253579646437545411084288, 169791213513235438329133006848, 8394780891403984989159686144,
    169520414129641761393998823424, 172499207349172207680474841088, 8394780891403984989159686144, 205807531531194470701979402240, 8394780891403984989159686144, 198844118810214206655671828480,
    198263834416799184651812864000, 196909837498830799976141946880, 198263834416799184651812864000, 792281625142643375935439503360, 594211218856982531951579627520, 594211218856982531951579627520,
    594211218856982531951579627520, 594211218856982531951579627520, 50368685348423909934958116864, 1220222022473108269714630508544, 924509095588813056548102209536, 1030120855190347061250433744896,
    50368685348423909934958116864, 1030120855190347061250433744896, 1028496058888784999639628644352, 50368685348423909934958116864, 1220222022473108269714630508544, 50368685348423909934958116864,
    92845502946403520617434316800, 69634127209802640463075737600, 73502689832569453822135500800, 94779784257786927296964198400, 1268888540267514781771602329600, 2218620664156767461420774195200,
    67699845898419233783545856000, 1268888540267514781771602329600, 71568408521186047142605619200, 73502689832569453822135500800, 73502689832569453822135500800
  ]
def positiveScales : Array ℕ := #[
    6, 7, 9, 10, 12, 7,
    11, 12, 7, 9, 7, 10,
    12, 11, 12, 2, 3, 3,
    3, 3, 9, 13, 13, 12,
    9, 12, 13, 9, 13, 9,
    6, 7, 8, 10, 10, 14,
    9, 10, 9, 8, 8
  ]
def negativeArguments : Array ℕ := #[
    5425, 525791, 33635, 112996023, 17143, 651,
    33635, 651, 17143, 17143, 668577, 4285039475,
    83777800265, 167555585155, 535630575, 14987765, 53910545, 7493885,
    7, 5, 5, 15, 21
  ]
def negativeCoefficients : Array ℕ := #[
    102475352678271301137203200, 2482977795394513626554433536, 158836796651320516762664960, 2084408717627998189721223168, 161911057231668655796781056, 6148521160696278068232192,
    158836796651320516762664960, 6148521160696278068232192, 161911057231668655796781056, 161911057231668655796781056, 12333068812568510890770432, 4940314158816733647444377600,
    193178455068351406613494497280, 193178437342183273283222241280, 4940320067539444757535129600, 70777719089126768096250429440, 254585350781235737426992824320, 70777742700959182444476497920,
    1109194275199700726309615304704, 792281625142643375935439503360, 792281625142643375935439503360, 2376844875427930127806318510080, 6655165651198204357857691828224
  ]
def negativeScales : Array ℕ := #[
    12, 19, 15, 26, 14, 9,
    15, 9, 14, 14, 19, 31,
    36, 37, 28, 23, 25, 22,
    2, 2, 2, 3, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6741466986389582, 7761551232426566, 9377210530388551, 10941781241718677, 12099676554859642, 7761551232426566,
    11097373768990222, 12122504484313904, 7761551232426566, 9377210530388551, 7761551232426566, 10327552644081240,
    12323336289280170, 11313449940963057, 12323336289280170, 2321928094887362, 3906890595303263, 3906890595303263,
    3906890595303263, 3906890595303263, 9346513733165635, 13944986519701843, 13544602265085271, 12700656452913602,
    9346513733165635, 12700656452913602, 13698379112202774, 9346513733165635, 13944986519701843, 9346513733165635,
    6228818690495880, 7813781191164178, 8891783702985444, 10258566033889932, 10001408194392808, 14807505865743947,
    9773139206696762, 10001408194392808, 9853309555289512, 8891783702985444, 8891783702985444
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    12405407422219213, 19004129921895826, 15037675637718717, 26751696755874086, 14065331980621583, 9346513733165637,
    15037675637718717, 9346513733165637, 14065331980621583, 14065331980621583, 19350734199483832, 31996661371348270,
    36285848953053723, 37285848820671176, 28996663096842367, 23837281927851364, 25684064158597707, 22837282409142216,
    2807354922807594, 2321928094887363, 2321928094887363, 3906890600547867, 4392317422778766
  ]

abbrev PositiveTerm := Fin 41
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 2485983893 / 500000000000
noncomputable def negativeCeiling : ℝ := 839983487 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 2084408717627998189721223168, coefficient := (-2084408717627998189721223168) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 4940314158816733647444377600, coefficient := (-4940314158816733647444377600) }, { argument := 193178455068351406613494497280, coefficient := (-193178455068351406613494497280) }, { argument := 193178437342183273283222241280, coefficient := (-193178437342183273283222241280) }, { argument := 4940320067539444757535129600, coefficient := (-4940320067539444757535129600) }, { argument := 70777719089126768096250429440, coefficient := (-70777719089126768096250429440) }, { argument := 254585350781235737426992824320, coefficient := (-254585350781235737426992824320) }, { argument := 70777742700959182444476497920, coefficient := (-70777742700959182444476497920) }, { argument := 33909653556105136490036810743808, coefficient := 33909653556105136490036810743808 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 152189253579646437545411084288, coefficient := 152189253579646437545411084288 }, { argument := 169791213513235438329133006848, coefficient := 169791213513235438329133006848 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 169520414129641761393998823424, coefficient := 169520414129641761393998823424 }, { argument := 172499207349172207680474841088, coefficient := 172499207349172207680474841088 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 205807531531194470701979402240, coefficient := 205807531531194470701979402240 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 594211218856982531951579627520, coefficient := 594211218856982531951579627520 }, { argument := 594211218856982531951579627520, coefficient := 594211218856982531951579627520 }, { argument := 594211218856982531951579627520, coefficient := 594211218856982531951579627520 }, { argument := 594211218856982531951579627520, coefficient := 594211218856982531951579627520 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 50368685348423909934958116864, coefficient := 50368685348423909934958116864 }, { argument := 1220222022473108269714630508544, coefficient := 1220222022473108269714630508544 }, { argument := 924509095588813056548102209536, coefficient := 924509095588813056548102209536 }, { argument := 1030120855190347061250433744896, coefficient := 1030120855190347061250433744896 }, { argument := 50368685348423909934958116864, coefficient := 50368685348423909934958116864 }, { argument := 1030120855190347061250433744896, coefficient := 1030120855190347061250433744896 }, { argument := 1028496058888784999639628644352, coefficient := 1028496058888784999639628644352 }, { argument := 50368685348423909934958116864, coefficient := 50368685348423909934958116864 }, { argument := 1220222022473108269714630508544, coefficient := 1220222022473108269714630508544 }, { argument := 50368685348423909934958116864, coefficient := 50368685348423909934958116864 }, { argument := 6655165651198204357857691828224, coefficient := (-6655165651198204357857691828224) }, { argument := 92845502946403520617434316800, coefficient := 92845502946403520617434316800 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 94779784257786927296964198400, coefficient := 94779784257786927296964198400 }, { argument := 1268888540267514781771602329600, coefficient := 1268888540267514781771602329600 }, { argument := 2218620664156767461420774195200, coefficient := 2218620664156767461420774195200 }, { argument := 67699845898419233783545856000, coefficient := 67699845898419233783545856000 }, { argument := 1268888540267514781771602329600, coefficient := 1268888540267514781771602329600 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }] }

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

end TermShard8


end Parent2

namespace Parent2

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1688521467142656988502574690729984)
def positiveArguments : Array ℕ := #[
    925, 28675, 925, 75, 1225, 21,
    315, 553, 21, 175, 21, 553,
    1099, 175, 16961, 1085, 315, 553,
    21, 1085, 21, 553, 553, 21,
    14987765, 53910545, 7493885, 4183585, 40897145, 163588565,
    2091795, 38571, 13528647, 272732505, 27057345, 38571,
    3620153, 659079879, 659079933, 3620099, 3198807, 144580257,
    401985
  ]
def positiveCoefficients : Array ℕ := #[
    71568408521186047142605619200, 2218620664156767461420774195200, 71568408521186047142605619200, 92845502946403520617434316800, 94779784257786927296964198400, 1624796301562061610805100544,
    24371944523430924162076508160, 42786302607800955751200980992, 1624796301562061610805100544, 27079938359367693513418342400, 1624796301562061610805100544, 42786302607800955751200980992,
    42515503224207278816066797568, 27079938359367693513418342400, 656146906447479213830126436352, 41973904457019924945798430720, 24371944523430924162076508160, 42786302607800955751200980992,
    1624796301562061610805100544, 41973904457019924945798430720, 1624796301562061610805100544, 42786302607800955751200980992, 42786302607800955751200980992, 1624796301562061610805100544,
    141555438178253536192500858880, 509170701562471474853985648640, 141555485401918364888952995840, 39512843164472409342680760320, 1545050454344479171224650383360, 1545050312673484685135293972480,
    39512890388137238039132897280, 5828684723544482737198989312, 1022195666421999633781323988992, 10303542723208623420740563107840, 1022197593147524644596571176960, 5828684723544482737198989312,
    68382756760239978917188861952, 12449666920493525360862755291136, 12449667940524685660706121449472, 68381736729079679073822703616, 120847511695750409576698085376, 5462087677931835219959900798976,
    121492511399446677198565539840
  ]
def positiveScales : Array ℕ := #[
    9, 14, 9, 6, 10, 4,
    8, 9, 4, 7, 4, 9,
    10, 7, 14, 10, 8, 9,
    4, 10, 4, 9, 9, 4,
    23, 25, 22, 21, 25, 27,
    20, 15, 23, 28, 24, 15,
    21, 29, 29, 21, 21, 27,
    18
  ]
def negativeArguments : Array ℕ := #[
    25, 7, 5, 5, 39, 79,
    9
  ]
def negativeCoefficients : Array ℕ := #[
    7922816251426433759354395033600, 1109194275199700726309615304704, 792281625142643375935439503360, 3169126500570573503741758013440, 12359593352225236664592856252416, 25036099354507530679559888306176,
    5704427701027032306735164424192
  ]
def negativeScales : Array ℕ := #[
    4, 2, 2, 2, 5, 6,
    3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9853309555289512, 14807505865743947, 9853309555289512, 6228818690495880, 10258566033889932, 4392317422778759,
    8299208018387278, 9111135670234706, 4392317422778759, 7451211111832325, 4392317422778759, 9111135670234706,
    10101975670949231, 7451211111832325, 14049933611508950, 10083479327331841, 8299208018387278, 9111135670234706,
    4392317422778759, 10083479327331841, 4392317422778759, 9111135670234706, 9111135670234706, 4392317422778759,
    23837281926411354, 25684064158545100, 22837282407702193, 21996308315293758, 25285496797400396, 27285496665114715,
    20996310039525663, 15235228929621358, 23689514226804435, 28022911413908980, 24689516946122107, 15235228929621358,
    21787619241097951, 29295878086325262, 29295878204528733, 21787597720981756, 21609102519407016, 27107295319182915,
    18616782142931597
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4643856189792934, 2807354922807594, 2321928094887363, 2321928094887363, 5285402218862249, 6303780748177104,
    3169925001442313
  ]

abbrev PositiveTerm := Fin 43
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 8278160523 / 500000000000
noncomputable def negativeCeiling : ℝ := 436846859 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 2218620664156767461420774195200, coefficient := 2218620664156767461420774195200 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 92845502946403520617434316800, coefficient := 92845502946403520617434316800 }, { argument := 94779784257786927296964198400, coefficient := 94779784257786927296964198400 }, { argument := 7922816251426433759354395033600, coefficient := (-7922816251426433759354395033600) }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 27079938359367693513418342400, coefficient := 27079938359367693513418342400 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 42515503224207278816066797568, coefficient := 42515503224207278816066797568 }, { argument := 27079938359367693513418342400, coefficient := 27079938359367693513418342400 }, { argument := 656146906447479213830126436352, coefficient := 656146906447479213830126436352 }, { argument := 41973904457019924945798430720, coefficient := 41973904457019924945798430720 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 41973904457019924945798430720, coefficient := 41973904457019924945798430720 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 42786302607800955751200980992, coefficient := 42786302607800955751200980992 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 141555438178253536192500858880, coefficient := 141555438178253536192500858880 }, { argument := 509170701562471474853985648640, coefficient := 509170701562471474853985648640 }, { argument := 141555485401918364888952995840, coefficient := 141555485401918364888952995840 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 39512843164472409342680760320, coefficient := 39512843164472409342680760320 }, { argument := 1545050454344479171224650383360, coefficient := 1545050454344479171224650383360 }, { argument := 1545050312673484685135293972480, coefficient := 1545050312673484685135293972480 }, { argument := 39512890388137238039132897280, coefficient := 39512890388137238039132897280 }, { argument := 3169126500570573503741758013440, coefficient := (-3169126500570573503741758013440) }, { argument := 5828684723544482737198989312, coefficient := 5828684723544482737198989312 }, { argument := 1022195666421999633781323988992, coefficient := 1022195666421999633781323988992 }, { argument := 10303542723208623420740563107840, coefficient := 10303542723208623420740563107840 }, { argument := 1022197593147524644596571176960, coefficient := 1022197593147524644596571176960 }, { argument := 5828684723544482737198989312, coefficient := 5828684723544482737198989312 }, { argument := 12359593352225236664592856252416, coefficient := (-12359593352225236664592856252416) }, { argument := 68382756760239978917188861952, coefficient := 68382756760239978917188861952 }, { argument := 12449666920493525360862755291136, coefficient := 12449666920493525360862755291136 }, { argument := 12449667940524685660706121449472, coefficient := 12449667940524685660706121449472 }, { argument := 68381736729079679073822703616, coefficient := 68381736729079679073822703616 }, { argument := 25036099354507530679559888306176, coefficient := (-25036099354507530679559888306176) }, { argument := 120847511695750409576698085376, coefficient := 120847511695750409576698085376 }, { argument := 5462087677931835219959900798976, coefficient := 5462087677931835219959900798976 }, { argument := 121492511399446677198565539840, coefficient := 121492511399446677198565539840 }, { argument := 5704427701027032306735164424192, coefficient := (-5704427701027032306735164424192) }] }

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

end TermShard9


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
