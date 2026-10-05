import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 17166118182096995013118230353936384
def positiveArguments : Array ℕ := #[
    1175, 1, 489, 535, 489, 535,
    471, 78657, 2041, 84623, 126699, 3925,
    126699, 132037, 78657, 3925, 23777, 26845,
    11505, 302965, 26845, 11505, 26845, 26845,
    1112917, 6903, 302965, 1112917, 23777, 26845,
    6903, 26845, 45, 1305, 1155, 75
  ]
def positiveCoefficients : Array ℕ := #[
    186186181908521193344828283289600, 158456325028528675187087900672, 302676339605275477212835872768, 331148960508839223535515729920, 302676339605275477212835872768, 331148960508839223535515729920,
    72883719812926763684685938688, 1521447651094846191917818970112, 78957363130670660658409766912, 1636846874131980234418571706368, 2450715078709662428897564688384, 75920541471798712171547852800,
    2450715078709662428897564688384, 2553967015111308677450869768192, 1521447651094846191917818970112, 75920541471798712171547852800, 459914067407632606191819948032, 519257818040875523119796715520,
    445078129749321876959825756160, 5860195375032738046637705789440, 519257818040875523119796715520, 445078129749321876959825756160, 519257818040875523119796715520, 519257818040875523119796715520,
    21526945542208868115623572406272, 534093755699186252351790907392, 5860195375032738046637705789440, 21526945542208868115623572406272, 459914067407632606191819948032, 519257818040875523119796715520,
    534093755699186252351790907392, 519257818040875523119796715520, 27853650883921056185230295040, 403877937816855314685839278080, 714910372687307108754244239360, 23211375736600880154358579200
  ]
def positiveScales : Array ℕ := #[
    10, 0, 8, 9, 8, 9,
    8, 16, 10, 16, 16, 11,
    16, 17, 16, 11, 14, 14,
    13, 18, 14, 13, 14, 14,
    20, 12, 18, 20, 14, 14,
    12, 14, 5, 10, 10, 6
  ]
def negativeArguments : Array ℕ := #[
    290737323, 20283885, 77703648115, 77703703693, 57, 2474638475,
    2474640245, 111, 315435435, 1130645145, 78881775, 75723937335,
    75723991497, 111, 2474638475, 2474640245, 3489, 111,
    1646159181, 275525, 1646160243, 275525, 667175, 9,
    1, 1, 157, 767
  ]
def negativeCoefficients : Array ℕ := #[
    171621023681805750923717246976, 47893969333191176752705044480, 179172413796373577685511700480, 179172541950516343764194164736, 2205080694977083614664065024, 5706127827909986550494003200,
    5706131909252112858732298240, 2147052255635581414278168576, 46550053929793955821183303680, 166853773023977813398058434560, 46563581296158088509574348800, 174607511534045588445116497920,
    174607636423114653477208326144, 2147052255635581414278168576, 182596090493119569615808102400, 182596221096067611479433543680, 67487074954167059048797569024, 2147052255635581414278168576,
    7591569279123579780017946624, 40660313287270593671987200, 7591574176734131349903900672, 40660313287270593671987200, 3150644858208555545447628800, 2785365088392105618523029504,
    158456325028528675187087900672, 1267650600228229401496703205376, 12438821514739501002186400202752, 60768000648440746934248209907712
  ]
def negativeScales : Array ℕ := #[
    28, 24, 36, 36, 5, 31,
    31, 6, 28, 30, 26, 36,
    36, 6, 31, 31, 11, 6,
    30, 18, 30, 18, 19, 3,
    0, 0, 7, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10198445041452361, 0, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509,
    8879583249426338, 16263287542086835, 10995060465683787, 16368762211644132, 16951045611514478, 11938476938137180,
    16951045611514478, 17010582739146771, 16263287542086835, 11938476938137180, 14537279077889752, 14712365784441905,
    13489973363111439, 18208791610567398, 14712365784441905, 13489973363111439, 14712365784441905, 14712365784441905,
    20085914571569677, 12753007768930352, 18208791610567398, 20085914571569677, 14537279077889752, 14712365784441905,
    12753007768930352, 14712365784441905, 5491853096329661, 10349834091457246, 10173677136303419, 6228818690495880
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28115141046433659, 24273830664355817, 36177263282305424, 36177264314201329, 5832890015409720, 31204570628301159,
    31204571660197065, 6794415866926375, 28232769496041627, 30074499061936313, 26233188679858471, 36140030376106449,
    36140031408002354, 6794415866926375, 31204570628301159, 31204571660197065, 11768597882530236, 6794415866926375,
    30616456702838236, 18071823703359091, 30616457633575468, 18071823703359091, 19347705704388811, 3169925001442313,
    0, 0, 7294620748891628, 9583082767506450
  ]

abbrev PositiveTerm := Fin 36
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 39615647749 / 1000000000000
noncomputable def negativeCeiling : ℝ := 8731036231 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 171621023681805750923717246976, coefficient := (-171621023681805750923717246976) }, { argument := 47893969333191176752705044480, coefficient := (-47893969333191176752705044480) }, { argument := 179172413796373577685511700480, coefficient := (-179172413796373577685511700480) }, { argument := 179172541950516343764194164736, coefficient := (-179172541950516343764194164736) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 5706127827909986550494003200, coefficient := (-5706127827909986550494003200) }, { argument := 5706131909252112858732298240, coefficient := (-5706131909252112858732298240) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 46550053929793955821183303680, coefficient := (-46550053929793955821183303680) }, { argument := 166853773023977813398058434560, coefficient := (-166853773023977813398058434560) }, { argument := 46563581296158088509574348800, coefficient := (-46563581296158088509574348800) }, { argument := 174607511534045588445116497920, coefficient := (-174607511534045588445116497920) }, { argument := 174607636423114653477208326144, coefficient := (-174607636423114653477208326144) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 182596090493119569615808102400, coefficient := (-182596090493119569615808102400) }, { argument := 182596221096067611479433543680, coefficient := (-182596221096067611479433543680) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 7591569279123579780017946624, coefficient := (-7591569279123579780017946624) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 7591574176734131349903900672, coefficient := (-7591574176734131349903900672) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 3150644858208555545447628800, coefficient := (-3150644858208555545447628800) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 186186181908521193344828283289600, coefficient := 186186181908521193344828283289600 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 72883719812926763684685938688, coefficient := 72883719812926763684685938688 }, { argument := 1521447651094846191917818970112, coefficient := 1521447651094846191917818970112 }, { argument := 78957363130670660658409766912, coefficient := 78957363130670660658409766912 }, { argument := 1636846874131980234418571706368, coefficient := 1636846874131980234418571706368 }, { argument := 2450715078709662428897564688384, coefficient := 2450715078709662428897564688384 }, { argument := 75920541471798712171547852800, coefficient := 75920541471798712171547852800 }, { argument := 2450715078709662428897564688384, coefficient := 2450715078709662428897564688384 }, { argument := 2553967015111308677450869768192, coefficient := 2553967015111308677450869768192 }, { argument := 1521447651094846191917818970112, coefficient := 1521447651094846191917818970112 }, { argument := 75920541471798712171547852800, coefficient := 75920541471798712171547852800 }, { argument := 12438821514739501002186400202752, coefficient := (-12438821514739501002186400202752) }, { argument := 459914067407632606191819948032, coefficient := 459914067407632606191819948032 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 445078129749321876959825756160, coefficient := 445078129749321876959825756160 }, { argument := 5860195375032738046637705789440, coefficient := 5860195375032738046637705789440 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 445078129749321876959825756160, coefficient := 445078129749321876959825756160 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 21526945542208868115623572406272, coefficient := 21526945542208868115623572406272 }, { argument := 534093755699186252351790907392, coefficient := 534093755699186252351790907392 }, { argument := 5860195375032738046637705789440, coefficient := 5860195375032738046637705789440 }, { argument := 21526945542208868115623572406272, coefficient := 21526945542208868115623572406272 }, { argument := 459914067407632606191819948032, coefficient := 459914067407632606191819948032 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 534093755699186252351790907392, coefficient := 534093755699186252351790907392 }, { argument := 519257818040875523119796715520, coefficient := 519257818040875523119796715520 }, { argument := 60768000648440746934248209907712, coefficient := (-60768000648440746934248209907712) }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 714910372687307108754244239360, coefficient := 714910372687307108754244239360 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7141628143501106978318983800815616)
def positiveArguments : Array ℕ := #[
    45, 75, 2295, 75, 45, 36765,
    2355, 1305, 2295, 75, 2355, 75,
    2295, 75, 45, 141, 105, 111,
    9, 1929, 3489, 105, 1929, 57,
    57, 111, 111, 3489, 111, 141,
    9, 1, 164102099, 164102189, 5536079585, 20032127529,
    2768375675, 255323615, 10180105353, 5090051825, 127662043, 336567,
    15093115, 312584013, 15093123, 336567, 11205, 2085947,
    16687577, 89639
  ]
def positiveCoefficients : Array ℕ := #[
    445658414142736898963684720640, 23211375736600880154358579200, 710268097539986932723372523520, 742764023571228164939474534400, 445658414142736898963684720640, 11378216386081751451666575523840,
    728837198129267636846859386880, 403877937816855314685839278080, 710268097539986932723372523520, 23211375736600880154358579200, 728837198129267636846859386880, 23211375736600880154358579200,
    710268097539986932723372523520, 742764023571228164939474534400, 27853650883921056185230295040, 5454673298101206836274266112, 4061990753905154027012751360, 4294104511271162828556337152,
    5570730176784211237046059008, 74624572993171829696262832128, 134974149908334118097595138048, 4061990753905154027012751360, 74624572993171829696262832128, 4410161389954167229328130048,
    4410161389954167229328130048, 4294104511271162828556337152, 4294104511271162828556337152, 134974149908334118097595138048, 4294104511271162828556337152, 5454673298101206836274266112,
    5570730176784211237046059008, 633825300114114700748351602688, 12399204033378501167245074366464, 12399210833586236499534182088704, 26143396678702895083735387996160, 94599047623519926803742729437184,
    26146568999223260010952366489600, 1205731681761113389728310231040, 48074188311089058041157478514688, 48074180268898937714151679590400, 1205733905995726821331205881856, 3178785440079975761276043264,
    570201763184776681756106424320, 5904545064288357827133352968192, 570202065416231585413400100864, 3178785440079975761276043264, 846625863048869993911418880, 157609699165479805193176481792,
    157609708610212770932466909184, 846616418315904254620991488
  ]
def positiveScales : Array ℕ := #[
    5, 6, 11, 6, 5, 15,
    11, 10, 11, 6, 11, 6,
    11, 6, 5, 7, 6, 6,
    3, 10, 11, 6, 10, 5,
    5, 6, 6, 11, 6, 7,
    3, 0, 27, 27, 32, 34,
    31, 27, 33, 32, 26, 18,
    23, 28, 23, 18, 13, 20,
    23, 16
  ]
def negativeArguments : Array ℕ := #[
    15, 3, 1, 313, 927, 311,
    89, 1
  ]
def negativeCoefficients : Array ℕ := #[
    19014759003423441022450548080640, 475368975085586025561263702016, 633825300114114700748351602688, 24798414866964737666779256455168, 146889013301446081898430483922944, 98559834167744835966368674217984,
    7051306463769526045825411579904, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    3, 1, 0, 8, 9, 8,
    6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5491853096329661, 6228818690495880, 11164278438301170, 6228818690495880, 5491853096329661, 15166045364475357,
    11201511344500145, 10349834091457246, 11164278438301170, 6228818690495880, 11201511344500145, 6228818690495880,
    11164278438301170, 6228818690495880, 5491853096329661, 7139551352398793, 6714245517659862, 6794415866314396,
    3169925001442312, 10913637427705176, 11768597882173550, 6714245517659862, 10913637427705176, 5832890014087662,
    5832890014087662, 6794415866314396, 6794415866314396, 11768597882173550, 6794415866314396, 7139551352398793,
    3169925001442312, 0, 27290018451317520, 27290019242547607, 32366217536856046, 34221596600805026,
    31366392587309000, 27927751738110921, 33245033440686461, 32245033199342214, 26927754399473570, 18360534203480569,
    23847387252033317, 28219668753190096, 23847388016723524, 18360534203480569, 13451855028397752, 20992271070183114,
    23992271156636352, 16451838933985791
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3906890600547867, 1584962500724866, 0, 8290018846932619, 9856425530582692, 8280770770130603,
    6475733430966516, 0
  ]

abbrev PositiveTerm := Fin 50
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
noncomputable def positiveFloor : ℝ := 55567152203 / 500000000000
noncomputable def negativeCeiling : ℝ := 7794707171 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 445658414142736898963684720640, coefficient := 445658414142736898963684720640 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 710268097539986932723372523520, coefficient := 710268097539986932723372523520 }, { argument := 742764023571228164939474534400, coefficient := 742764023571228164939474534400 }, { argument := 445658414142736898963684720640, coefficient := 445658414142736898963684720640 }, { argument := 11378216386081751451666575523840, coefficient := 11378216386081751451666575523840 }, { argument := 728837198129267636846859386880, coefficient := 728837198129267636846859386880 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 710268097539986932723372523520, coefficient := 710268097539986932723372523520 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 728837198129267636846859386880, coefficient := 728837198129267636846859386880 }, { argument := 23211375736600880154358579200, coefficient := 23211375736600880154358579200 }, { argument := 710268097539986932723372523520, coefficient := 710268097539986932723372523520 }, { argument := 742764023571228164939474534400, coefficient := 742764023571228164939474534400 }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 19014759003423441022450548080640, coefficient := (-19014759003423441022450548080640) }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 12399204033378501167245074366464, coefficient := 12399204033378501167245074366464 }, { argument := 12399210833586236499534182088704, coefficient := 12399210833586236499534182088704 }, { argument := 24798414866964737666779256455168, coefficient := (-24798414866964737666779256455168) }, { argument := 26143396678702895083735387996160, coefficient := 26143396678702895083735387996160 }, { argument := 94599047623519926803742729437184, coefficient := 94599047623519926803742729437184 }, { argument := 26146568999223260010952366489600, coefficient := 26146568999223260010952366489600 }, { argument := 146889013301446081898430483922944, coefficient := (-146889013301446081898430483922944) }, { argument := 1205731681761113389728310231040, coefficient := 1205731681761113389728310231040 }, { argument := 48074188311089058041157478514688, coefficient := 48074188311089058041157478514688 }, { argument := 48074180268898937714151679590400, coefficient := 48074180268898937714151679590400 }, { argument := 1205733905995726821331205881856, coefficient := 1205733905995726821331205881856 }, { argument := 98559834167744835966368674217984, coefficient := (-98559834167744835966368674217984) }, { argument := 3178785440079975761276043264, coefficient := 3178785440079975761276043264 }, { argument := 570201763184776681756106424320, coefficient := 570201763184776681756106424320 }, { argument := 5904545064288357827133352968192, coefficient := 5904545064288357827133352968192 }, { argument := 570202065416231585413400100864, coefficient := 570202065416231585413400100864 }, { argument := 3178785440079975761276043264, coefficient := 3178785440079975761276043264 }, { argument := 7051306463769526045825411579904, coefficient := (-7051306463769526045825411579904) }, { argument := 846625863048869993911418880, coefficient := 846625863048869993911418880 }, { argument := 157609699165479805193176481792, coefficient := 157609699165479805193176481792 }, { argument := 157609708610212770932466909184, coefficient := 157609708610212770932466909184 }, { argument := 846616418315904254620991488, coefficient := 846616418315904254620991488 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
