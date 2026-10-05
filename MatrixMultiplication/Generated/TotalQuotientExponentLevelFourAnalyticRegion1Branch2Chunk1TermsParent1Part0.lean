import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

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
def constantNumerator : ℤ := (-286225116667824694907058926911488)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    67724125, 1357191465, 2278239565, 2186134755, 67724125, 2186134755,
    1460132135, 35216545, 1357191465, 8126895, 556928455, 1371375567,
    497525455, 440665403, 20625983863, 5614930135, 1371376017, 20625983863,
    497525455, 497525455, 213225195, 497525455, 5614930135, 213225195,
    556926655, 440665403, 116330875, 9740283525, 4870143525, 58163675,
    42122607, 2750813125, 135820089, 23544828635, 139370941, 4438565,
    135820089, 77231031, 139370941, 2175784563, 2663139, 1375407395,
    135820089, 4438565, 2663139, 4438565, 68353901, 77231031,
    42122607, 1852426975, 37122636579, 62315643439, 59796342753, 1852426975,
    59796342753, 39938325581, 963262027, 37122636579, 222291237, 34915880605,
    43487163783, 8706075245, 7711095217, 360929005157
  ]
def negativeCoefficients : Array ℕ := #[
    624644800745457443667968000, 12517881806938967171106078720, 21013051097077188404990443520, 20163534168063366281602007040, 624644800745457443667968000, 20163534168063366281602007040,
    13467341904072062485481390080, 649630592775275741414686720, 12517881806938967171106078720, 599659008715639145921249280, 2568379169187866675060408320, 25297414113387326140707766272,
    2294431184635224551399096320, 2032210477819770316953485312, 95120561397306023545145393152, 25894294798026105651504087040, 25297422414422159310005993472, 95120561397306023545145393152,
    2294431184635224551399096320, 2294431184635224551399096320, 1966655301115906758342082560, 2294431184635224551399096320, 25894294798026105651504087040, 1966655301115906758342082560,
    2568370868153033505762181120, 2032210477819770316953485312, 268240734874462079418368000, 22459564673880566405057740800, 22459572801977173883328921600, 268232606777854601147187200,
    97128118880805809358372864, 6342943213934525252894720000, 1252719210925726930317606912, 54290678511149150195175915520, 1285470039969536784704995328, 40938536304762317984235520,
    1252719210925726930317606912, 712330531702864332925698048, 1285470039969536784704995328, 20068070496594488275872251904, 786019897051436505297321984, 6342947053163135593695150080,
    1252719210925726930317606912, 40938536304762317984235520, 786019897051436505297321984, 40938536304762317984235520, 1260906918186679393914454016, 712330531702864332925698048,
    97128118880805809358372864, 2135702895191310108039577600, 42799486019633854565113135104, 71845045394235672034451390464, 68940489456775490287517564928, 2135702895191310108039577600,
    68940489456775490287517564928, 46045754420324645929333293056, 2221131010998962512361160704, 42799486019633854565113135104, 2050274779383657703717994496, 80510539203579252959042600960,
    100274572599561486937060540416, 80299370965486591322053672960, 71122299998002409456676110336, 3328982493454886971665710841856
  ]
def negativeScales : Array ℕ := #[
    26, 30, 31, 31, 26, 31,
    30, 25, 30, 22, 29, 30,
    28, 28, 34, 32, 30, 34,
    28, 28, 27, 28, 32, 27,
    29, 28, 26, 33, 32, 25,
    25, 31, 27, 34, 27, 22,
    27, 26, 27, 31, 21, 30,
    27, 22, 21, 22, 26, 26,
    25, 30, 35, 35, 35, 30,
    35, 35, 29, 35, 27, 35,
    35, 33, 32, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26013166513047603, 30337977116468087, 31085272313528023, 31025735186550659, 26013166513047603, 31025735186550659,
    30443451786025420, 25069750041413971, 30337977116468087, 22954272835195966, 29052916764857624, 30352976577874108,
    28890195103214438, 28715108393099551, 34263743886676554, 32386620925674278, 30352977051276637, 34263743886676554,
    28890195103214438, 28890195103214438, 27667802678251627, 28890195103214438, 32386620925674278, 27667802678251627,
    29052912102040978, 28715108393099551, 26793658808307411, 33181316621587323, 32181317143697289, 25793615091820888,
    25328091392825413, 31357210988262979, 27017121641900989, 34454691171263281, 27054354548099964, 22081661894095700,
    27017121641900989, 26202677295057066, 27054354548099964, 31018888568075177, 21344696299929494, 30357211861490787,
    27017121641900989, 22081661894095700, 21344696299929494, 22081661894095700, 26026520339903239, 26202677295057066,
    25328091392825413, 30786769525278346, 35111580128206732, 35858875327316589, 35799338198926676, 30786769525278346,
    35799338198926676, 35217054797764030, 29843353054677514, 35111580128206732, 27727875835870268, 35023164307918147,
    35339870568698126, 33019375343112677, 32844288638107181, 38392924130234460
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
noncomputable def negativeCeiling : ℝ := 255352779 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 624644800745457443667968000, coefficient := (-624644800745457443667968000) }, { argument := 12517881806938967171106078720, coefficient := (-12517881806938967171106078720) }, { argument := 21013051097077188404990443520, coefficient := (-21013051097077188404990443520) }, { argument := 20163534168063366281602007040, coefficient := (-20163534168063366281602007040) }, { argument := 624644800745457443667968000, coefficient := (-624644800745457443667968000) }, { argument := 20163534168063366281602007040, coefficient := (-20163534168063366281602007040) }, { argument := 13467341904072062485481390080, coefficient := (-13467341904072062485481390080) }, { argument := 649630592775275741414686720, coefficient := (-649630592775275741414686720) }, { argument := 12517881806938967171106078720, coefficient := (-12517881806938967171106078720) }, { argument := 599659008715639145921249280, coefficient := (-599659008715639145921249280) }, { argument := 2568379169187866675060408320, coefficient := (-2568379169187866675060408320) }, { argument := 25297414113387326140707766272, coefficient := (-25297414113387326140707766272) }, { argument := 2294431184635224551399096320, coefficient := (-2294431184635224551399096320) }, { argument := 2032210477819770316953485312, coefficient := (-2032210477819770316953485312) }, { argument := 95120561397306023545145393152, coefficient := (-95120561397306023545145393152) }, { argument := 25894294798026105651504087040, coefficient := (-25894294798026105651504087040) }, { argument := 25297422414422159310005993472, coefficient := (-25297422414422159310005993472) }, { argument := 95120561397306023545145393152, coefficient := (-95120561397306023545145393152) }, { argument := 2294431184635224551399096320, coefficient := (-2294431184635224551399096320) }, { argument := 2294431184635224551399096320, coefficient := (-2294431184635224551399096320) }, { argument := 1966655301115906758342082560, coefficient := (-1966655301115906758342082560) }, { argument := 2294431184635224551399096320, coefficient := (-2294431184635224551399096320) }, { argument := 25894294798026105651504087040, coefficient := (-25894294798026105651504087040) }, { argument := 1966655301115906758342082560, coefficient := (-1966655301115906758342082560) }, { argument := 2568370868153033505762181120, coefficient := (-2568370868153033505762181120) }, { argument := 2032210477819770316953485312, coefficient := (-2032210477819770316953485312) }, { argument := 268240734874462079418368000, coefficient := (-268240734874462079418368000) }, { argument := 22459564673880566405057740800, coefficient := (-22459564673880566405057740800) }, { argument := 22459572801977173883328921600, coefficient := (-22459572801977173883328921600) }, { argument := 268232606777854601147187200, coefficient := (-268232606777854601147187200) }, { argument := 97128118880805809358372864, coefficient := (-97128118880805809358372864) }, { argument := 6342943213934525252894720000, coefficient := (-6342943213934525252894720000) }, { argument := 1252719210925726930317606912, coefficient := (-1252719210925726930317606912) }, { argument := 54290678511149150195175915520, coefficient := (-54290678511149150195175915520) }, { argument := 1285470039969536784704995328, coefficient := (-1285470039969536784704995328) }, { argument := 40938536304762317984235520, coefficient := (-40938536304762317984235520) }, { argument := 1252719210925726930317606912, coefficient := (-1252719210925726930317606912) }, { argument := 712330531702864332925698048, coefficient := (-712330531702864332925698048) }, { argument := 1285470039969536784704995328, coefficient := (-1285470039969536784704995328) }, { argument := 20068070496594488275872251904, coefficient := (-20068070496594488275872251904) }, { argument := 786019897051436505297321984, coefficient := (-786019897051436505297321984) }, { argument := 6342947053163135593695150080, coefficient := (-6342947053163135593695150080) }, { argument := 1252719210925726930317606912, coefficient := (-1252719210925726930317606912) }, { argument := 40938536304762317984235520, coefficient := (-40938536304762317984235520) }, { argument := 786019897051436505297321984, coefficient := (-786019897051436505297321984) }, { argument := 40938536304762317984235520, coefficient := (-40938536304762317984235520) }, { argument := 1260906918186679393914454016, coefficient := (-1260906918186679393914454016) }, { argument := 712330531702864332925698048, coefficient := (-712330531702864332925698048) }, { argument := 97128118880805809358372864, coefficient := (-97128118880805809358372864) }, { argument := 2135702895191310108039577600, coefficient := (-2135702895191310108039577600) }, { argument := 42799486019633854565113135104, coefficient := (-42799486019633854565113135104) }, { argument := 71845045394235672034451390464, coefficient := (-71845045394235672034451390464) }, { argument := 68940489456775490287517564928, coefficient := (-68940489456775490287517564928) }, { argument := 2135702895191310108039577600, coefficient := (-2135702895191310108039577600) }, { argument := 68940489456775490287517564928, coefficient := (-68940489456775490287517564928) }, { argument := 46045754420324645929333293056, coefficient := (-46045754420324645929333293056) }, { argument := 2221131010998962512361160704, coefficient := (-2221131010998962512361160704) }, { argument := 42799486019633854565113135104, coefficient := (-42799486019633854565113135104) }, { argument := 2050274779383657703717994496, coefficient := (-2050274779383657703717994496) }, { argument := 80510539203579252959042600960, coefficient := (-80510539203579252959042600960) }, { argument := 100274572599561486937060540416, coefficient := (-100274572599561486937060540416) }, { argument := 80299370965486591322053672960, coefficient := (-80299370965486591322053672960) }, { argument := 71122299998002409456676110336, coefficient := (-71122299998002409456676110336) }, { argument := 3328982493454886971665710841856, coefficient := (-3328982493454886971665710841856) }] }

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
def constantNumerator : ℤ := (-880630236156386906431177927688192)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    98254277765, 21743583279, 360929005157, 8706075245, 8706075245, 3731175105,
    8706075245, 98254277765, 3731175105, 17457938915, 7711095217, 2878570375,
    241020207225, 120510147225, 1439241575, 348616971, 7360798955, 14240491371,
    157312538035, 14612791799, 465375535, 14240491371, 8097534309, 14612791799,
    228127087257, 279225321, 3680400865, 14240491371, 465375535, 279225321,
    465375535, 7166783239, 8097534309, 348616971, 91579625, 7667882775,
    3833942775, 45788425, 1061692245, 111316517055, 1199880793125, 55658300985,
    1061692245, 2242677805, 13959705, 35340385055, 345428445, 10989555,
    35340402345, 5643285, 5643285, 190980645, 10395525, 345428445,
    190980645, 2242660515, 10989555, 10395525, 13959705, 541792825,
    10857528213, 18225910633, 17489072391, 541792825
  ]
def negativeCoefficients : Array ℕ := #[
    906235758039062959206034309120, 100274578998275837505061257216, 3328982493454886971665710841856, 80299370965486591322053672960, 80299370965486591322053672960, 68828032256131363990331719680,
    80299370965486591322053672960, 906235758039062959206034309120, 68828032256131363990331719680, 80510532804864902391041884160, 71122299998002409456676110336, 6637531375723391454543872000,
    555754759909002100618769203200, 555754961036158579283224166400, 6637330248566912790088908800, 6430848043788824618138075136, 271565549001827421017142722560, 131345349902353128873963552768,
    1450952064358672341067397857280, 134779215259277393681125998592, 4292331696155331008953057280, 131345349902353128873963552768, 74686571513102759555783196672, 134779215259277393681125998592,
    2104100997455343260588788678656, 82412768566182355371898699776, 271565651381257030105154191360, 131345349902353128873963552768, 4292331696155331008953057280, 82412768566182355371898699776,
    4292331696155331008953057280, 132203816241584195075754164224, 74686571513102759555783196672, 6430848043788824618138075136, 211168238092661636988928000, 17680933892203850148662476800,
    17680940290918200716663193600, 211161839378311068988211200, 1224047820534821208320901120, 128339206330644342473679175680, 1383368369358531890868387840000, 128339304230973906164090142720,
    1224047820534821208320901120, 2585631469288980964106567680, 257511105479483596241633280, 81489379821991857042604687360, 6372030120694455796362117120, 202721508568955171509370880,
    81489419690017486347373117440, 208200468260008013982597120, 208200468260008013982597120, 3522971081346977710284472320, 191763589186849486562918400, 6372030120694455796362117120,
    3522971081346977710284472320, 2585611535276166311722352640, 202721508568955171509370880, 191763589186849486562918400, 257511105479483596241633280, 624644598984194137469747200,
    12517877763643250514893733888, 21013044309828290784482295808, 20163527655209786757523439616, 624644598984194137469747200
  ]
def negativeScales : Array ℕ := #[
    36, 34, 38, 33, 33, 31,
    33, 36, 31, 34, 32, 31,
    37, 36, 30, 28, 32, 33,
    37, 33, 28, 33, 32, 33,
    37, 28, 31, 33, 28, 28,
    28, 32, 32, 28, 26, 32,
    31, 25, 29, 36, 40, 35,
    29, 31, 23, 35, 28, 23,
    35, 22, 22, 27, 23, 28,
    27, 31, 23, 23, 23, 29,
    33, 34, 34, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36515801169232631, 34339870660759283, 38392924130234460, 33019375343112677, 33019375343112677, 31796982922383645,
    33019375343112677, 36515801169232631, 31796982922383645, 34023164193257459, 32844288638107181, 31422705337535638,
    37810363152179750, 36810363674289724, 30422661621049624, 28377067562015104, 32777215222011104, 33729279876659445,
    37194842703961857, 33766512783037667, 28793820129281399, 33729279876659445, 32914835535358324, 33766512783037667,
    37731046802839390, 28056854534545937, 31777215765902880, 33729279876659445, 28793820129281399, 28056854534545937,
    28793820129281399, 32738678574694917, 32914835535358324, 28377067562015104, 26448523321691397, 32836181136866017,
    31836181658975997, 25448479605205383, 29983718501853114, 36695876718315895, 40126028221390399, 35695877818839035,
    29983718501853114, 31062575224068489, 23734765118847076, 35040598707889147, 28363811648482054, 23389629632637788,
    35040599413715955, 22428103780452440, 22428103780452440, 27508851194337145, 23309459283953801, 28363811648482054,
    27508851194337145, 31062564101519653, 23389629632637788, 23309459283953801, 23734765118847076, 29013166047054737,
    33337976650475221, 34085271847535157, 34025734720557793, 29013166047054737
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
noncomputable def negativeCeiling : ℝ := 3123383053 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 906235758039062959206034309120, coefficient := (-906235758039062959206034309120) }, { argument := 100274578998275837505061257216, coefficient := (-100274578998275837505061257216) }, { argument := 3328982493454886971665710841856, coefficient := (-3328982493454886971665710841856) }, { argument := 80299370965486591322053672960, coefficient := (-80299370965486591322053672960) }, { argument := 80299370965486591322053672960, coefficient := (-80299370965486591322053672960) }, { argument := 68828032256131363990331719680, coefficient := (-68828032256131363990331719680) }, { argument := 80299370965486591322053672960, coefficient := (-80299370965486591322053672960) }, { argument := 906235758039062959206034309120, coefficient := (-906235758039062959206034309120) }, { argument := 68828032256131363990331719680, coefficient := (-68828032256131363990331719680) }, { argument := 80510532804864902391041884160, coefficient := (-80510532804864902391041884160) }, { argument := 71122299998002409456676110336, coefficient := (-71122299998002409456676110336) }, { argument := 6637531375723391454543872000, coefficient := (-6637531375723391454543872000) }, { argument := 555754759909002100618769203200, coefficient := (-555754759909002100618769203200) }, { argument := 555754961036158579283224166400, coefficient := (-555754961036158579283224166400) }, { argument := 6637330248566912790088908800, coefficient := (-6637330248566912790088908800) }, { argument := 6430848043788824618138075136, coefficient := (-6430848043788824618138075136) }, { argument := 271565549001827421017142722560, coefficient := (-271565549001827421017142722560) }, { argument := 131345349902353128873963552768, coefficient := (-131345349902353128873963552768) }, { argument := 1450952064358672341067397857280, coefficient := (-1450952064358672341067397857280) }, { argument := 134779215259277393681125998592, coefficient := (-134779215259277393681125998592) }, { argument := 4292331696155331008953057280, coefficient := (-4292331696155331008953057280) }, { argument := 131345349902353128873963552768, coefficient := (-131345349902353128873963552768) }, { argument := 74686571513102759555783196672, coefficient := (-74686571513102759555783196672) }, { argument := 134779215259277393681125998592, coefficient := (-134779215259277393681125998592) }, { argument := 2104100997455343260588788678656, coefficient := (-2104100997455343260588788678656) }, { argument := 82412768566182355371898699776, coefficient := (-82412768566182355371898699776) }, { argument := 271565651381257030105154191360, coefficient := (-271565651381257030105154191360) }, { argument := 131345349902353128873963552768, coefficient := (-131345349902353128873963552768) }, { argument := 4292331696155331008953057280, coefficient := (-4292331696155331008953057280) }, { argument := 82412768566182355371898699776, coefficient := (-82412768566182355371898699776) }, { argument := 4292331696155331008953057280, coefficient := (-4292331696155331008953057280) }, { argument := 132203816241584195075754164224, coefficient := (-132203816241584195075754164224) }, { argument := 74686571513102759555783196672, coefficient := (-74686571513102759555783196672) }, { argument := 6430848043788824618138075136, coefficient := (-6430848043788824618138075136) }, { argument := 211168238092661636988928000, coefficient := (-211168238092661636988928000) }, { argument := 17680933892203850148662476800, coefficient := (-17680933892203850148662476800) }, { argument := 17680940290918200716663193600, coefficient := (-17680940290918200716663193600) }, { argument := 211161839378311068988211200, coefficient := (-211161839378311068988211200) }, { argument := 1224047820534821208320901120, coefficient := (-1224047820534821208320901120) }, { argument := 128339206330644342473679175680, coefficient := (-128339206330644342473679175680) }, { argument := 1383368369358531890868387840000, coefficient := (-1383368369358531890868387840000) }, { argument := 128339304230973906164090142720, coefficient := (-128339304230973906164090142720) }, { argument := 1224047820534821208320901120, coefficient := (-1224047820534821208320901120) }, { argument := 2585631469288980964106567680, coefficient := (-2585631469288980964106567680) }, { argument := 257511105479483596241633280, coefficient := (-257511105479483596241633280) }, { argument := 81489379821991857042604687360, coefficient := (-81489379821991857042604687360) }, { argument := 6372030120694455796362117120, coefficient := (-6372030120694455796362117120) }, { argument := 202721508568955171509370880, coefficient := (-202721508568955171509370880) }, { argument := 81489419690017486347373117440, coefficient := (-81489419690017486347373117440) }, { argument := 208200468260008013982597120, coefficient := (-208200468260008013982597120) }, { argument := 208200468260008013982597120, coefficient := (-208200468260008013982597120) }, { argument := 3522971081346977710284472320, coefficient := (-3522971081346977710284472320) }, { argument := 191763589186849486562918400, coefficient := (-191763589186849486562918400) }, { argument := 6372030120694455796362117120, coefficient := (-6372030120694455796362117120) }, { argument := 3522971081346977710284472320, coefficient := (-3522971081346977710284472320) }, { argument := 2585611535276166311722352640, coefficient := (-2585611535276166311722352640) }, { argument := 202721508568955171509370880, coefficient := (-202721508568955171509370880) }, { argument := 191763589186849486562918400, coefficient := (-191763589186849486562918400) }, { argument := 257511105479483596241633280, coefficient := (-257511105479483596241633280) }, { argument := 624644598984194137469747200, coefficient := (-624644598984194137469747200) }, { argument := 12517877763643250514893733888, coefficient := (-12517877763643250514893733888) }, { argument := 21013044309828290784482295808, coefficient := (-21013044309828290784482295808) }, { argument := 20163527655209786757523439616, coefficient := (-20163527655209786757523439616) }, { argument := 624644598984194137469747200, coefficient := (-624644598984194137469747200) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
