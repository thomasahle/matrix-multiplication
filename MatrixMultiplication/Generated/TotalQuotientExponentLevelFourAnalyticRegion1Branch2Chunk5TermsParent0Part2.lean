import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5

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
def constantNumerator : ℤ := 11279615564732277283634698923278336
def positiveArguments : Array ℕ := #[
    1135, 5, 2751651661, 3563, 2751389875, 1799,
    1387746337, 6745, 2201, 4804591805, 22223, 693873041,
    44517, 19951, 6745, 2201, 104922979, 35861,
    1199189455, 887369, 28231, 4796760073, 14497, 14497,
    490609, 26705, 887369, 490609, 209844725, 28231,
    26705, 35861, 7183735, 274490609, 9639, 1177008875
  ]
def positiveCoefficients : Array ℕ := #[
    179847928907380046337344767262720, 792281625142643375935439503360, 12994307576438987298747298349056, 275673772498363119966598725632, 12993071327006902785805385728000, 278381766334299889317940559872,
    26213787154295693575184824926208, 2087476391244972488548648222720, 85147063327097562032905388032, 90756173215208681107925101445120, 1719421343314937865567702351872, 26213782337481881048146706956288,
    1722168022777102303052634783744, 1543633857736413866532026712064, 2087476391244972488548648222720, 85147063327097562032905388032, 1981939037249742577976303681536, 693652621075203469346210840576,
    45304096711221733438843718205440, 17164212730009822018077515055104, 546066957016649539698080874496, 45304117990205105249465051119616, 560825523422504932662893871104, 560825523422504932662893871104,
    9489758198965017676374756818944, 516549824204938753768454881280, 17164212730009822018077515055104, 9489758198965017676374756818944, 1981927391893995821431206707200, 546066957016649539698080874496,
    516549824204938753768454881280, 693652621075203469346210840576, 33924229385817570759210434560, 1296245251804076982321350180864, 745781502416986279359541149696, 5558267261340107884621463552000
  ]
def positiveScales : Array ℕ := #[
    10, 2, 31, 11, 31, 10,
    30, 12, 11, 32, 14, 29,
    15, 14, 12, 11, 26, 15,
    30, 19, 14, 32, 13, 13,
    18, 14, 19, 18, 27, 14,
    14, 15, 22, 28, 13, 30
  ]
def negativeArguments : Array ℕ := #[
    17865164205, 10540759635, 375, 375, 105, 625,
    625, 45, 14154734367, 23990363361, 14154734367, 9625,
    9625, 105, 10875, 10875, 1185, 45,
    14802530765855, 16272221, 14801724347361, 8216033, 313835, 93,
    5, 335, 1925, 1925
  ]
def negativeCoefficients : Array ℕ := #[
    164777055962215881548381552640, 48610673832333276596970455040, 116056878683004400771792896000, 116056878683004400771792896000, 2030995376952577013506375680, 6044629098073145873530880000,
    6044629098073145873530880000, 1740853180245066011576893440, 65277190574847542858788896768, 221272046577832755222112370688, 65277190574847542858788896768, 186174576220652892904751104000,
    186174576220652892904751104000, 2030995376952577013506375680, 105176546306472738199437312000, 105176546306472738199437312000, 22921233539893369152429096960, 1740853180245066011576893440,
    8333084005155610096838901760, 75042374074460528426614784, 8332630031901974712268357632, 75779529026076054246129664, 2964087770302790211280568320, 1798881619586568211962789888,
    792281625142643375935439503360, 26541434442278553093837223362560, 152514212839958849867572104396800, 152514212839958849867572104396800
  ]
def negativeScales : Array ℕ := #[
    34, 33, 8, 8, 6, 9,
    9, 5, 33, 34, 33, 13,
    13, 6, 13, 13, 10, 5,
    43, 23, 43, 22, 18, 6,
    2, 8, 10, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10148476582178277, 2321928094887362, 31357650700931833, 11798876768094178, 31357513439614873, 10812979471199464,
    30370096739051953, 12719602727828552, 11103943429891557, 32161766719757851, 14439765966437297, 29370096473955041,
    15442068752306718, 14284173439725607, 12719602727828552, 11103943429891557, 26644755433760608, 15130128098512167,
    30159412456188795, 19759174628290728, 14784992612434086, 32159413133811324, 13823466760214044, 13823466760214044,
    18904214173871410, 14704822263774464, 19759174628290728, 18904214173871410, 27644746956836734, 14784992612434086,
    14704822263774464, 15130128098512167, 22776302700943685, 28032181551021949, 13234667766192568, 30132478052757023
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34056430123174668, 33295259789487922, 8550746785384604, 8550746785384604, 6714245517766967, 9287712379549450,
    9287712379549450, 5491853096329881, 33720565624337153, 34481735957907484, 33720565624337153, 13232570825356989,
    13232570825356989, 6714245517766967, 13408727780510825, 13408727780510825, 10210671343785622, 5491853096329881,
    43750909086052935, 23955907854025280, 43750830488164636, 22970010560187291, 18259646730218516, 6539158811108986,
    2321928094887363, 8388017285345139, 10910642735748889, 10910642735748889
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
noncomputable def positiveFloor : ℝ := 69284346749 / 500000000000
noncomputable def negativeCeiling : ℝ := 10781331679 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 164777055962215881548381552640, coefficient := (-164777055962215881548381552640) }, { argument := 48610673832333276596970455040, coefficient := (-48610673832333276596970455040) }, { argument := 116056878683004400771792896000, coefficient := (-116056878683004400771792896000) }, { argument := 116056878683004400771792896000, coefficient := (-116056878683004400771792896000) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 6044629098073145873530880000, coefficient := (-6044629098073145873530880000) }, { argument := 6044629098073145873530880000, coefficient := (-6044629098073145873530880000) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 65277190574847542858788896768, coefficient := (-65277190574847542858788896768) }, { argument := 221272046577832755222112370688, coefficient := (-221272046577832755222112370688) }, { argument := 65277190574847542858788896768, coefficient := (-65277190574847542858788896768) }, { argument := 186174576220652892904751104000, coefficient := (-186174576220652892904751104000) }, { argument := 186174576220652892904751104000, coefficient := (-186174576220652892904751104000) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 105176546306472738199437312000, coefficient := (-105176546306472738199437312000) }, { argument := 105176546306472738199437312000, coefficient := (-105176546306472738199437312000) }, { argument := 22921233539893369152429096960, coefficient := (-22921233539893369152429096960) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 8333084005155610096838901760, coefficient := (-8333084005155610096838901760) }, { argument := 75042374074460528426614784, coefficient := (-75042374074460528426614784) }, { argument := 8332630031901974712268357632, coefficient := (-8332630031901974712268357632) }, { argument := 75779529026076054246129664, coefficient := (-75779529026076054246129664) }, { argument := 2964087770302790211280568320, coefficient := (-2964087770302790211280568320) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 179847928907380046337344767262720, coefficient := 179847928907380046337344767262720 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 12994307576438987298747298349056, coefficient := 12994307576438987298747298349056 }, { argument := 275673772498363119966598725632, coefficient := 275673772498363119966598725632 }, { argument := 12993071327006902785805385728000, coefficient := 12993071327006902785805385728000 }, { argument := 278381766334299889317940559872, coefficient := 278381766334299889317940559872 }, { argument := 26541434442278553093837223362560, coefficient := (-26541434442278553093837223362560) }, { argument := 26213787154295693575184824926208, coefficient := 26213787154295693575184824926208 }, { argument := 2087476391244972488548648222720, coefficient := 2087476391244972488548648222720 }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 90756173215208681107925101445120, coefficient := 90756173215208681107925101445120 }, { argument := 1719421343314937865567702351872, coefficient := 1719421343314937865567702351872 }, { argument := 26213782337481881048146706956288, coefficient := 26213782337481881048146706956288 }, { argument := 1722168022777102303052634783744, coefficient := 1722168022777102303052634783744 }, { argument := 1543633857736413866532026712064, coefficient := 1543633857736413866532026712064 }, { argument := 2087476391244972488548648222720, coefficient := 2087476391244972488548648222720 }, { argument := 85147063327097562032905388032, coefficient := 85147063327097562032905388032 }, { argument := 152514212839958849867572104396800, coefficient := (-152514212839958849867572104396800) }, { argument := 1981939037249742577976303681536, coefficient := 1981939037249742577976303681536 }, { argument := 693652621075203469346210840576, coefficient := 693652621075203469346210840576 }, { argument := 45304096711221733438843718205440, coefficient := 45304096711221733438843718205440 }, { argument := 17164212730009822018077515055104, coefficient := 17164212730009822018077515055104 }, { argument := 546066957016649539698080874496, coefficient := 546066957016649539698080874496 }, { argument := 45304117990205105249465051119616, coefficient := 45304117990205105249465051119616 }, { argument := 560825523422504932662893871104, coefficient := 560825523422504932662893871104 }, { argument := 560825523422504932662893871104, coefficient := 560825523422504932662893871104 }, { argument := 9489758198965017676374756818944, coefficient := 9489758198965017676374756818944 }, { argument := 516549824204938753768454881280, coefficient := 516549824204938753768454881280 }, { argument := 17164212730009822018077515055104, coefficient := 17164212730009822018077515055104 }, { argument := 9489758198965017676374756818944, coefficient := 9489758198965017676374756818944 }, { argument := 1981927391893995821431206707200, coefficient := 1981927391893995821431206707200 }, { argument := 546066957016649539698080874496, coefficient := 546066957016649539698080874496 }, { argument := 516549824204938753768454881280, coefficient := 516549824204938753768454881280 }, { argument := 693652621075203469346210840576, coefficient := 693652621075203469346210840576 }, { argument := 152514212839958849867572104396800, coefficient := (-152514212839958849867572104396800) }, { argument := 33924229385817570759210434560, coefficient := 33924229385817570759210434560 }, { argument := 1296245251804076982321350180864, coefficient := 1296245251804076982321350180864 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 5558267261340107884621463552000, coefficient := 5558267261340107884621463552000 }] }

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
def constantNumerator : ℤ := (-947187608416759578560176785981440)
def positiveArguments : Array ℕ := #[
    9891, 315, 9639, 5481, 9891, 154413,
    189, 137245339, 9639, 315, 189, 315,
    4851, 5481, 7183735, 627671, 17021993, 105,
    93, 4353, 1185, 8510997, 4353, 105,
    105, 45, 105, 1185, 45, 313835,
    93
  ]
def positiveCoefficients : Array ℕ := #[
    765279058035731018689202356224, 24371944523430924162076508160, 745781502416986279359541149696, 424071834707698080420131241984, 765279058035731018689202356224, 11947127205385839024249904300032,
    467941334849873743911868956672, 1296245577647364300326869925888, 745781502416986279359541149696, 24371944523430924162076508160, 467941334849873743911868956672, 24371944523430924162076508160,
    750655891321672464191956451328, 424071834707698080420131241984, 33924229385817570759210434560, 5928184985338546161851564032, 160768178429683441480033632256, 4061990753905154027012751360,
    3597763239173136423925579776, 168398530969039385519871492096, 45842467079786738304858193920, 160768187874416407219324059648, 168398530969039385519871492096, 4061990753905154027012751360,
    4061990753905154027012751360, 3481706360490132023153786880, 4061990753905154027012751360, 45842467079786738304858193920, 3481706360490132023153786880, 5928175540605580422561136640,
    3597763239173136423925579776
  ]
def positiveScales : Array ℕ := #[
    13, 8, 13, 12, 13, 17,
    7, 27, 13, 8, 7, 8,
    12, 12, 22, 19, 24, 6,
    6, 12, 10, 23, 12, 6,
    6, 5, 6, 10, 5, 18,
    6
  ]
def negativeArguments : Array ℕ := #[
    335, 5
  ]
def negativeCoefficients : Array ℕ := #[
    26541434442278553093837223362560, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    8, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13271900672391543, 8299208018387278, 13234667766192568, 12420223419348643, 13271900672391543, 17236434692366755,
    7562242424220952, 27032181913678966, 13234667766192568, 8299208018387278, 7562242424220952, 8299208018387278,
    12244066464194817, 12420223419348643, 22776302700943685, 19259649028709588, 24020896627374359, 6714245517659862,
    6539158811107971, 12087794304787900, 10210671343785621, 23020896712129123, 12087794304787900, 6714245517659862,
    6714245517659862, 5491853096329661, 6714245517659862, 10210671343785621, 5491853096329661, 18259646730218515,
    6539158811107971
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8388017285345139, 2321928094887363
  ]

abbrev PositiveTerm := Fin 31
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
noncomputable def positiveFloor : ℝ := 775641729 / 200000000000
noncomputable def negativeCeiling : ℝ := 270195491 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }, { argument := 765279058035731018689202356224, coefficient := 765279058035731018689202356224 }, { argument := 11947127205385839024249904300032, coefficient := 11947127205385839024249904300032 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 1296245577647364300326869925888, coefficient := 1296245577647364300326869925888 }, { argument := 745781502416986279359541149696, coefficient := 745781502416986279359541149696 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 467941334849873743911868956672, coefficient := 467941334849873743911868956672 }, { argument := 24371944523430924162076508160, coefficient := 24371944523430924162076508160 }, { argument := 750655891321672464191956451328, coefficient := 750655891321672464191956451328 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }, { argument := 33924229385817570759210434560, coefficient := 33924229385817570759210434560 }, { argument := 26541434442278553093837223362560, coefficient := (-26541434442278553093837223362560) }, { argument := 5928184985338546161851564032, coefficient := 5928184985338546161851564032 }, { argument := 160768178429683441480033632256, coefficient := 160768178429683441480033632256 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 160768187874416407219324059648, coefficient := 160768187874416407219324059648 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 5928175540605580422561136640, coefficient := 5928175540605580422561136640 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5
