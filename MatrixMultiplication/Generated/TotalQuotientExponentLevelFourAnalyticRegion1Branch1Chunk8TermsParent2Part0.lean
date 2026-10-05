import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-851836169231945821576870410321920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    13211469, 375272079, 1498893711, 746886483, 1498893711, 19246324539,
    54677623, 622266733789, 22764497, 2240959, 22742909, 45931641,
    2412507133, 54677623, 2240959, 49077315, 14686470897, 58659997809,
    29229798829, 58659997809, 8993390386097, 1865360455, 338880710673559, 3112256021,
    153049883, 1554852229, 3135386121, 1128500896759, 1865360455, 153049883,
    2141516697909, 83288343998155, 20035, 51829, 86761, 1234975,
    20817750214923, 86761, 40105, 20311, 20035, 39553,
    1234975, 39553, 535378048757, 51829, 825543, 14686473585,
    58660008561, 29229804205, 58660008561, 93751832478537, 36847032635, 3569661294275519,
    123012317099, 6047948627, 61457730901, 123882630249, 11764999571999, 36847032635,
    6047948627, 83058949123787, 15247466430959925, 7487
  ]
def negativeCoefficients : Array ℕ := #[
    124778796790142697563486158848, 6922547999321912677094129664, 6912427170127441839463071744, 6888811902007009884990603264, 6912427170127441839463071744, 43338870011046016604700672,
    504312059019887537379344384, 1401220115208598016252444672, 419930850125728866633777152, 20669198576338041539919872, 419532621814665624833490944, 423644613206252331548540928,
    43459864900829854534991872, 504312059019887537379344384, 20669198576338041539919872, 463522134850471364181601812480, 270917569982942552639303319552, 270521491736746508074233102336,
    269597309162289070755735928832, 270521491736746508074233102336, 10125657397905962587576598528, 68819653837206805480535490560, 381545760578122294736050978816, 57410990311248619822106279936,
    2823272022212190250811260928, 57363922281599673257456304128, 57837665346347929121939521536, 10164632436262205954277244928, 68819653837206805480535490560, 2823272022212190250811260928,
    602783362669416715653218304, 23443584687149784061632839680, 378450449937173367425597440, 489511064881301683561299968, 6555475814724052614167658496, 11664009094363880195568435200,
    23438703027654821454337277952, 6555475814724052614167658496, 378781015590974242590556160, 383663942534261455741517824, 378450449937173367425597440, 373567522993886154274635776,
    11664009094363880195568435200, 373567522993886154274635776, 602782095221092109797818368, 489511064881301683561299968, 124752530987764976596807581696, 270917619567790622770578063360,
    270521541321594578205507846144, 269597358747137140887010672640, 270521541321594578205507846144, 105555179453910099407916761088, 679707780893468693905968988160, 4019081318684527458628828921856,
    567294182859814598153124970496, 27891240123303017373193207808, 566847516640829066024748843008, 571307793845323096166127108096, 105969695376937482651600683008, 679707780893468693905968988160,
    27891240123303017373193207808, 23379015770229507402625974272, 4291780258550954050297056460800, 282850862857960269719535616
  ]
def negativeScales : Array ℕ := #[
    23, 28, 30, 29, 30, 34,
    25, 39, 24, 21, 24, 25,
    31, 25, 21, 25, 33, 35,
    34, 35, 43, 30, 48, 31,
    27, 30, 31, 40, 30, 27,
    40, 46, 14, 15, 16, 20,
    44, 16, 15, 14, 14, 15,
    20, 15, 38, 15, 19, 33,
    35, 34, 35, 46, 35, 51,
    36, 32, 35, 36, 43, 35,
    32, 46, 53, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23655287554831676, 28483361713894388, 30481250937038715, 29476313747953145, 30481250937038715, 34163863910232334,
    25704447190325615, 39178742165961748, 24440282246405373, 21095684823242640, 24438913462481322, 25452984991865164,
    31167886061953928, 25704447190325615, 21095684823242640, 25548552986112051, 33773768712666624, 35771657966441044,
    34766720849178363, 35771657966441044, 43032002233377770, 30796807292789847, 48267770848373940, 31535313598448249,
    27189426701086415, 30534130329121647, 31545995975021127, 40037544703610750, 30796807292789847, 27189426701086415,
    40961770077652221, 46243179841579276, 14290234889318161, 15661471937897105, 16404759061037361, 20236050406485479,
    44242879397794920, 16404759061037361, 15291494492177873, 14309973651164077, 14290234889318161, 15271499503349441,
    20236050406485479, 15271499503349441, 38961767044151572, 15661471937897105, 19654983837111453, 33773768976716712,
    35771658230877736, 34766721114521546, 35771658230877736, 46413912123304784, 35100829389764004, 51664708614612200,
    36840011823584294, 32493798738934503, 35838875452017502, 36850182964936174, 43419566501613879, 35100829389764004,
    32493798738934503, 46239200852186308, 53759419058122970, 12870172041643401
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
noncomputable def negativeCeiling : ℝ := 8265010901 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 124778796790142697563486158848, coefficient := (-124778796790142697563486158848) }, { argument := 6922547999321912677094129664, coefficient := (-6922547999321912677094129664) }, { argument := 6912427170127441839463071744, coefficient := (-6912427170127441839463071744) }, { argument := 6888811902007009884990603264, coefficient := (-6888811902007009884990603264) }, { argument := 6912427170127441839463071744, coefficient := (-6912427170127441839463071744) }, { argument := 43338870011046016604700672, coefficient := (-43338870011046016604700672) }, { argument := 504312059019887537379344384, coefficient := (-504312059019887537379344384) }, { argument := 1401220115208598016252444672, coefficient := (-1401220115208598016252444672) }, { argument := 419930850125728866633777152, coefficient := (-419930850125728866633777152) }, { argument := 20669198576338041539919872, coefficient := (-20669198576338041539919872) }, { argument := 419532621814665624833490944, coefficient := (-419532621814665624833490944) }, { argument := 423644613206252331548540928, coefficient := (-423644613206252331548540928) }, { argument := 43459864900829854534991872, coefficient := (-43459864900829854534991872) }, { argument := 504312059019887537379344384, coefficient := (-504312059019887537379344384) }, { argument := 20669198576338041539919872, coefficient := (-20669198576338041539919872) }, { argument := 463522134850471364181601812480, coefficient := (-463522134850471364181601812480) }, { argument := 270917569982942552639303319552, coefficient := (-270917569982942552639303319552) }, { argument := 270521491736746508074233102336, coefficient := (-270521491736746508074233102336) }, { argument := 269597309162289070755735928832, coefficient := (-269597309162289070755735928832) }, { argument := 270521491736746508074233102336, coefficient := (-270521491736746508074233102336) }, { argument := 10125657397905962587576598528, coefficient := (-10125657397905962587576598528) }, { argument := 68819653837206805480535490560, coefficient := (-68819653837206805480535490560) }, { argument := 381545760578122294736050978816, coefficient := (-381545760578122294736050978816) }, { argument := 57410990311248619822106279936, coefficient := (-57410990311248619822106279936) }, { argument := 2823272022212190250811260928, coefficient := (-2823272022212190250811260928) }, { argument := 57363922281599673257456304128, coefficient := (-57363922281599673257456304128) }, { argument := 57837665346347929121939521536, coefficient := (-57837665346347929121939521536) }, { argument := 10164632436262205954277244928, coefficient := (-10164632436262205954277244928) }, { argument := 68819653837206805480535490560, coefficient := (-68819653837206805480535490560) }, { argument := 2823272022212190250811260928, coefficient := (-2823272022212190250811260928) }, { argument := 602783362669416715653218304, coefficient := (-602783362669416715653218304) }, { argument := 23443584687149784061632839680, coefficient := (-23443584687149784061632839680) }, { argument := 378450449937173367425597440, coefficient := (-378450449937173367425597440) }, { argument := 489511064881301683561299968, coefficient := (-489511064881301683561299968) }, { argument := 6555475814724052614167658496, coefficient := (-6555475814724052614167658496) }, { argument := 11664009094363880195568435200, coefficient := (-11664009094363880195568435200) }, { argument := 23438703027654821454337277952, coefficient := (-23438703027654821454337277952) }, { argument := 6555475814724052614167658496, coefficient := (-6555475814724052614167658496) }, { argument := 378781015590974242590556160, coefficient := (-378781015590974242590556160) }, { argument := 383663942534261455741517824, coefficient := (-383663942534261455741517824) }, { argument := 378450449937173367425597440, coefficient := (-378450449937173367425597440) }, { argument := 373567522993886154274635776, coefficient := (-373567522993886154274635776) }, { argument := 11664009094363880195568435200, coefficient := (-11664009094363880195568435200) }, { argument := 373567522993886154274635776, coefficient := (-373567522993886154274635776) }, { argument := 602782095221092109797818368, coefficient := (-602782095221092109797818368) }, { argument := 489511064881301683561299968, coefficient := (-489511064881301683561299968) }, { argument := 124752530987764976596807581696, coefficient := (-124752530987764976596807581696) }, { argument := 270917619567790622770578063360, coefficient := (-270917619567790622770578063360) }, { argument := 270521541321594578205507846144, coefficient := (-270521541321594578205507846144) }, { argument := 269597358747137140887010672640, coefficient := (-269597358747137140887010672640) }, { argument := 270521541321594578205507846144, coefficient := (-270521541321594578205507846144) }, { argument := 105555179453910099407916761088, coefficient := (-105555179453910099407916761088) }, { argument := 679707780893468693905968988160, coefficient := (-679707780893468693905968988160) }, { argument := 4019081318684527458628828921856, coefficient := (-4019081318684527458628828921856) }, { argument := 567294182859814598153124970496, coefficient := (-567294182859814598153124970496) }, { argument := 27891240123303017373193207808, coefficient := (-27891240123303017373193207808) }, { argument := 566847516640829066024748843008, coefficient := (-566847516640829066024748843008) }, { argument := 571307793845323096166127108096, coefficient := (-571307793845323096166127108096) }, { argument := 105969695376937482651600683008, coefficient := (-105969695376937482651600683008) }, { argument := 679707780893468693905968988160, coefficient := (-679707780893468693905968988160) }, { argument := 27891240123303017373193207808, coefficient := (-27891240123303017373193207808) }, { argument := 23379015770229507402625974272, coefficient := (-23379015770229507402625974272) }, { argument := 4291780258550954050297056460800, coefficient := (-4291780258550954050297056460800) }, { argument := 282850862857960269719535616, coefficient := (-282850862857960269719535616) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-270640857492952646001350276022272)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    38737, 259381, 923077, 3811863601395445, 259381, 29977,
    15181, 7487, 29563, 923077, 29563, 20764514011403,
    38737, 40075, 29947, 31635, 40919, 547983,
    243765, 7385, 547983, 31665, 4009, 31635,
    7807, 243765, 7807, 40075, 40919, 19574144827,
    9082946431921, 94636560963401, 4541483450381, 19574144827, 103657, 77461,
    81827, 6615, 1417397, 2521933, 76405, 1417397,
    40949, 41477, 81827, 80771, 2521933, 80771,
    103657, 6615, 86759, 129667, 273951, 708689,
    1186335, 16886403, 511595, 1186335, 548373, 277723,
    273951, 540829, 16886403, 540829
  ]
def negativeCoefficients : Array ℕ := #[
    365860620893842893285883904, 4899568562772845780694728704, 8718215771815726989845725184, 4291776873707920749590405447680, 4899568562772845780694728704, 283124760113966709141929984,
    286760982305776335956475904, 282850862857960269719535616, 279214640666150642904989696, 8718215771815726989845725184, 279214640666150642904989696, 23378764391070998482462441472,
    365860620893842893285883904, 378497673602002063877734400, 282841418124994530429108224, 298784127371162452670545920, 386469028225086024998453248, 5175553104764713586273550336,
    9209181325573752524132843520, 278997411807938639225159680, 5175553104764713586273550336, 299067469360134631383367680, 302911475677190522587316224, 298784127371162452670545920,
    294940121054106561466597376, 9209181325573752524132843520, 294940121054106561466597376, 378497673602002063877734400, 386469028225086024998453248, 44077055674486660945412096,
    10226488541556397953677000704, 106551295172599492885530804224, 10226511587422573030159679488, 44077055674486660945412096, 489506342514818813916086272, 365799230129565587898105856,
    386417082193774458901102592, 499815268546923249417584640, 6693468085719986516957069312, 11909491871242892962711994368, 360812411123655242552442880, 6693468085719986516957069312,
    386752370214058203711275008, 391739189219968549056937984, 386417082193774458901102592, 381430263187864113555439616, 11909491871242892962711994368, 381430263187864113555439616,
    489506342514818813916086272, 499815268546923249417584640, 6555324698996600785520820224, 4898680757874066287394553856, 5174788081394488703748931584, 6693378360756811993698009088,
    89636938263282568873440706560, 159487567086858851090983550976, 4831878161607392286201610240, 89636938263282568873440706560, 5179236550621351909540233216, 5246039146888025910733176832,
    5174788081394488703748931584, 5107985485127814702555987968, 159487567086858851090983550976, 5107985485127814702555987968
  ]
def negativeScales : Array ℕ := #[
    15, 17, 19, 51, 17, 14,
    13, 12, 14, 19, 14, 44,
    15, 15, 14, 14, 15, 19,
    17, 12, 19, 14, 11, 14,
    12, 17, 12, 15, 15, 34,
    43, 46, 42, 34, 16, 16,
    16, 12, 20, 21, 16, 20,
    15, 15, 16, 16, 21, 16,
    16, 12, 16, 16, 18, 19,
    20, 24, 18, 20, 19, 18,
    18, 19, 24, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15241424607813969, 17984713297100141, 19816091473022541, 51759417920297192, 17984713297100141, 14871568392463517,
    13889979210016915, 12870172041643401, 14851505060339484, 19816091473022541, 14851505060339484, 44239185339753334,
    15241424607813969, 15290414899929273, 14870123867501686, 14949233985692235, 15320483267724837, 19063771611790276,
    17895131475802240, 12850382207396955, 19063771611790276, 14950601469486097, 11969026716473715, 14949233985692235,
    12930552561813914, 17895131475802240, 12930552561813914, 15290414899929273, 15320483267724837, 34188230227996761,
    43046297510303717, 46427462881482300, 42046300761480233, 34188230227996761, 16661458019993992, 16241182505828290,
    16320289339328739, 12691525441225267, 20434812469932088, 21266098517531261, 16221379431935758, 20434812469932088,
    15321540600337431, 15340023928434378, 16320289339328739, 16301549780619742, 21266098517531261, 16301549780619742,
    16661458019993992, 12691525441225267, 16404725803890267, 16984451856087507, 18063558344342460, 19434793130685921,
    20178080028275706, 24009358714273789, 18964642652073247, 20178080028275706, 19064798013961977, 18083287135251826,
    18063558344342460, 19044812987437190, 24009358714273789, 19044812987437190
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
noncomputable def negativeCeiling : ℝ := 2928031287 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 365860620893842893285883904, coefficient := (-365860620893842893285883904) }, { argument := 4899568562772845780694728704, coefficient := (-4899568562772845780694728704) }, { argument := 8718215771815726989845725184, coefficient := (-8718215771815726989845725184) }, { argument := 4291776873707920749590405447680, coefficient := (-4291776873707920749590405447680) }, { argument := 4899568562772845780694728704, coefficient := (-4899568562772845780694728704) }, { argument := 283124760113966709141929984, coefficient := (-283124760113966709141929984) }, { argument := 286760982305776335956475904, coefficient := (-286760982305776335956475904) }, { argument := 282850862857960269719535616, coefficient := (-282850862857960269719535616) }, { argument := 279214640666150642904989696, coefficient := (-279214640666150642904989696) }, { argument := 8718215771815726989845725184, coefficient := (-8718215771815726989845725184) }, { argument := 279214640666150642904989696, coefficient := (-279214640666150642904989696) }, { argument := 23378764391070998482462441472, coefficient := (-23378764391070998482462441472) }, { argument := 365860620893842893285883904, coefficient := (-365860620893842893285883904) }, { argument := 378497673602002063877734400, coefficient := (-378497673602002063877734400) }, { argument := 282841418124994530429108224, coefficient := (-282841418124994530429108224) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 386469028225086024998453248, coefficient := (-386469028225086024998453248) }, { argument := 5175553104764713586273550336, coefficient := (-5175553104764713586273550336) }, { argument := 9209181325573752524132843520, coefficient := (-9209181325573752524132843520) }, { argument := 278997411807938639225159680, coefficient := (-278997411807938639225159680) }, { argument := 5175553104764713586273550336, coefficient := (-5175553104764713586273550336) }, { argument := 299067469360134631383367680, coefficient := (-299067469360134631383367680) }, { argument := 302911475677190522587316224, coefficient := (-302911475677190522587316224) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 294940121054106561466597376, coefficient := (-294940121054106561466597376) }, { argument := 9209181325573752524132843520, coefficient := (-9209181325573752524132843520) }, { argument := 294940121054106561466597376, coefficient := (-294940121054106561466597376) }, { argument := 378497673602002063877734400, coefficient := (-378497673602002063877734400) }, { argument := 386469028225086024998453248, coefficient := (-386469028225086024998453248) }, { argument := 44077055674486660945412096, coefficient := (-44077055674486660945412096) }, { argument := 10226488541556397953677000704, coefficient := (-10226488541556397953677000704) }, { argument := 106551295172599492885530804224, coefficient := (-106551295172599492885530804224) }, { argument := 10226511587422573030159679488, coefficient := (-10226511587422573030159679488) }, { argument := 44077055674486660945412096, coefficient := (-44077055674486660945412096) }, { argument := 489506342514818813916086272, coefficient := (-489506342514818813916086272) }, { argument := 365799230129565587898105856, coefficient := (-365799230129565587898105856) }, { argument := 386417082193774458901102592, coefficient := (-386417082193774458901102592) }, { argument := 499815268546923249417584640, coefficient := (-499815268546923249417584640) }, { argument := 6693468085719986516957069312, coefficient := (-6693468085719986516957069312) }, { argument := 11909491871242892962711994368, coefficient := (-11909491871242892962711994368) }, { argument := 360812411123655242552442880, coefficient := (-360812411123655242552442880) }, { argument := 6693468085719986516957069312, coefficient := (-6693468085719986516957069312) }, { argument := 386752370214058203711275008, coefficient := (-386752370214058203711275008) }, { argument := 391739189219968549056937984, coefficient := (-391739189219968549056937984) }, { argument := 386417082193774458901102592, coefficient := (-386417082193774458901102592) }, { argument := 381430263187864113555439616, coefficient := (-381430263187864113555439616) }, { argument := 11909491871242892962711994368, coefficient := (-11909491871242892962711994368) }, { argument := 381430263187864113555439616, coefficient := (-381430263187864113555439616) }, { argument := 489506342514818813916086272, coefficient := (-489506342514818813916086272) }, { argument := 499815268546923249417584640, coefficient := (-499815268546923249417584640) }, { argument := 6555324698996600785520820224, coefficient := (-6555324698996600785520820224) }, { argument := 4898680757874066287394553856, coefficient := (-4898680757874066287394553856) }, { argument := 5174788081394488703748931584, coefficient := (-5174788081394488703748931584) }, { argument := 6693378360756811993698009088, coefficient := (-6693378360756811993698009088) }, { argument := 89636938263282568873440706560, coefficient := (-89636938263282568873440706560) }, { argument := 159487567086858851090983550976, coefficient := (-159487567086858851090983550976) }, { argument := 4831878161607392286201610240, coefficient := (-4831878161607392286201610240) }, { argument := 89636938263282568873440706560, coefficient := (-89636938263282568873440706560) }, { argument := 5179236550621351909540233216, coefficient := (-5179236550621351909540233216) }, { argument := 5246039146888025910733176832, coefficient := (-5246039146888025910733176832) }, { argument := 5174788081394488703748931584, coefficient := (-5174788081394488703748931584) }, { argument := 5107985485127814702555987968, coefficient := (-5107985485127814702555987968) }, { argument := 159487567086858851090983550976, coefficient := (-159487567086858851090983550976) }, { argument := 5107985485127814702555987968, coefficient := (-5107985485127814702555987968) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
