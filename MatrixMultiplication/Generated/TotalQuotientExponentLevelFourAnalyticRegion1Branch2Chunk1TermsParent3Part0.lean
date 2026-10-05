import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-184002697483007693608150961750016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    491241575, 9403017615, 881003025, 780316965, 36523868265, 9942748425,
    4701510345, 36523868265, 881003025, 881003025, 377572725, 881003025,
    9942748425, 377572725, 982480075, 780316965, 2351785957, 63593067983,
    3730244805, 14653661925, 3827767545, 121903425, 3730244805, 2121119595,
    3827767545, 59757058935, 73142055, 31796534441, 3730244805, 121903425,
    73142055, 121903425, 1877312745, 2121119595, 2351785957, 50393545,
    4219407927, 2109704727, 25196009, 34445765, 3611576335, 38929183125,
    1805789545, 34445765, 78998187, 2508134179, 89271752705, 62062979791,
    1974488609, 89271795521, 1013926583, 1013926583, 34313410151, 1867759495,
    62062979791, 34313410151, 157995705, 1974488609, 1867759495, 2508134179,
    11240197, 1178514383, 12703207125, 589257641
  ]
def negativeCoefficients : Array ℕ := #[
    1132725951548874528548454400, 10840941216530485764937482240, 1015727333146183621568102400, 899644209358048350531747840, 42109153154146069568437616640, 11463208474078358014840012800,
    10840944761764112430991933440, 42109153154146069568437616640, 1015727333146183621568102400, 1015727333146183621568102400, 870623428411014532772659200, 1015727333146183621568102400,
    11463208474078358014840012800, 870623428411014532772659200, 1132722406315247862494003200, 899644209358048350531747840, 2711424604057693524204716032, 73317815621525867432045969408,
    68810871250119591994463354880, 16894521954571065626512588800, 70609848276266509432227102720, 2248721282683646797204684800, 68810871250119591994463354880, 39127750318695454271361515520,
    70609848276266509432227102720, 1102323172771523659989736488960, 43175448627526018506329948160, 73317816658002300073601400832, 68810871250119591994463354880, 2248721282683646797204684800,
    43175448627526018506329948160, 2248721282683646797204684800, 69260615506656321353904291840, 39127750318695454271361515520, 2711424604057693524204716032, 116199603447745700786339840,
    9729292271493794298020757504, 9729295792516069367331422208, 116196082425470631475675136, 317706105689070946610053120, 33310912177205456139903303680, 359058339052723816460451840000,
    33310937587595417674810654720, 317706105689070946610053120, 5829037351504195768987680768, 2891681831408538857928392704, 102923323447538961491249070080, 71553744041024057271717462016,
    2276430377917360377518096384, 102923372811026102738009194496, 2337955523266478225559126016, 2337955523266478225559126016, 39560668459482776290382053376, 2153380087219124681436037120,
    71553744041024057271717462016, 39560668459482776290382053376, 5829012669760625145607618560, 2276430377917360377518096384, 2153380087219124681436037120, 2891681831408538857928392704,
    12959064837317367559094272, 1358734575649169921496055808, 14645800671887418829307904000, 1358735612125602563051487232
  ]
def negativeScales : Array ℕ := #[
    28, 33, 29, 29, 35, 33,
    32, 35, 29, 29, 28, 29,
    33, 28, 29, 29, 31, 35,
    31, 33, 31, 26, 31, 30,
    31, 35, 26, 34, 31, 26,
    26, 26, 30, 30, 31, 25,
    31, 30, 24, 25, 31, 35,
    30, 25, 26, 31, 36, 35,
    30, 36, 29, 29, 34, 30,
    35, 34, 27, 30, 30, 31,
    23, 30, 33, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28871857426468264, 33130476674559417, 29714571731972760, 29539485025314029, 35088120518992934, 33210997557990655,
    32130477146353336, 35088120518992934, 29714571731972760, 29714571731972760, 28492179310534916, 29714571731972760,
    33210997557990655, 28492179310534916, 29871852911078449, 29539485025314029, 31131109616190065, 35888150464267927,
    31796623168010801, 33770542185944298, 31833856074875475, 26861163421742798, 31796623168010801, 30982178838332939,
    31833856074875475, 35798390094207182, 26124197825436347, 34888150484662963, 31796623168010801, 26861163421742798,
    26124197825436347, 26861163421742798, 30806021866140151, 30982178838332939, 31131109616190065, 25586735612367274,
    31974393441856869, 30974393963966969, 24586691895881256, 25037823283162175, 31749981518003409, 35180133020918799,
    30749982618526552, 25037823283162175, 26235316208183267, 31223967384821504, 36377484700041747, 35853013916451575,
    30878831901746255, 36377485391978605, 29917306052524625, 29917306052524625, 34998053483423901, 30798661550717461,
    35853013916451575, 34998053483423901, 27235310099403671, 30878831901746255, 30798661550717461, 31223967384821504,
    23422163985218119, 30134322219834546, 33564473722976775, 29134323320357684
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
noncomputable def negativeCeiling : ℝ := 75511731 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1132725951548874528548454400, coefficient := (-1132725951548874528548454400) }, { argument := 10840941216530485764937482240, coefficient := (-10840941216530485764937482240) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 899644209358048350531747840, coefficient := (-899644209358048350531747840) }, { argument := 42109153154146069568437616640, coefficient := (-42109153154146069568437616640) }, { argument := 11463208474078358014840012800, coefficient := (-11463208474078358014840012800) }, { argument := 10840944761764112430991933440, coefficient := (-10840944761764112430991933440) }, { argument := 42109153154146069568437616640, coefficient := (-42109153154146069568437616640) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 870623428411014532772659200, coefficient := (-870623428411014532772659200) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 11463208474078358014840012800, coefficient := (-11463208474078358014840012800) }, { argument := 870623428411014532772659200, coefficient := (-870623428411014532772659200) }, { argument := 1132722406315247862494003200, coefficient := (-1132722406315247862494003200) }, { argument := 899644209358048350531747840, coefficient := (-899644209358048350531747840) }, { argument := 2711424604057693524204716032, coefficient := (-2711424604057693524204716032) }, { argument := 73317815621525867432045969408, coefficient := (-73317815621525867432045969408) }, { argument := 68810871250119591994463354880, coefficient := (-68810871250119591994463354880) }, { argument := 16894521954571065626512588800, coefficient := (-16894521954571065626512588800) }, { argument := 70609848276266509432227102720, coefficient := (-70609848276266509432227102720) }, { argument := 2248721282683646797204684800, coefficient := (-2248721282683646797204684800) }, { argument := 68810871250119591994463354880, coefficient := (-68810871250119591994463354880) }, { argument := 39127750318695454271361515520, coefficient := (-39127750318695454271361515520) }, { argument := 70609848276266509432227102720, coefficient := (-70609848276266509432227102720) }, { argument := 1102323172771523659989736488960, coefficient := (-1102323172771523659989736488960) }, { argument := 43175448627526018506329948160, coefficient := (-43175448627526018506329948160) }, { argument := 73317816658002300073601400832, coefficient := (-73317816658002300073601400832) }, { argument := 68810871250119591994463354880, coefficient := (-68810871250119591994463354880) }, { argument := 2248721282683646797204684800, coefficient := (-2248721282683646797204684800) }, { argument := 43175448627526018506329948160, coefficient := (-43175448627526018506329948160) }, { argument := 2248721282683646797204684800, coefficient := (-2248721282683646797204684800) }, { argument := 69260615506656321353904291840, coefficient := (-69260615506656321353904291840) }, { argument := 39127750318695454271361515520, coefficient := (-39127750318695454271361515520) }, { argument := 2711424604057693524204716032, coefficient := (-2711424604057693524204716032) }, { argument := 116199603447745700786339840, coefficient := (-116199603447745700786339840) }, { argument := 9729292271493794298020757504, coefficient := (-9729292271493794298020757504) }, { argument := 9729295792516069367331422208, coefficient := (-9729295792516069367331422208) }, { argument := 116196082425470631475675136, coefficient := (-116196082425470631475675136) }, { argument := 317706105689070946610053120, coefficient := (-317706105689070946610053120) }, { argument := 33310912177205456139903303680, coefficient := (-33310912177205456139903303680) }, { argument := 359058339052723816460451840000, coefficient := (-359058339052723816460451840000) }, { argument := 33310937587595417674810654720, coefficient := (-33310937587595417674810654720) }, { argument := 317706105689070946610053120, coefficient := (-317706105689070946610053120) }, { argument := 5829037351504195768987680768, coefficient := (-5829037351504195768987680768) }, { argument := 2891681831408538857928392704, coefficient := (-2891681831408538857928392704) }, { argument := 102923323447538961491249070080, coefficient := (-102923323447538961491249070080) }, { argument := 71553744041024057271717462016, coefficient := (-71553744041024057271717462016) }, { argument := 2276430377917360377518096384, coefficient := (-2276430377917360377518096384) }, { argument := 102923372811026102738009194496, coefficient := (-102923372811026102738009194496) }, { argument := 2337955523266478225559126016, coefficient := (-2337955523266478225559126016) }, { argument := 2337955523266478225559126016, coefficient := (-2337955523266478225559126016) }, { argument := 39560668459482776290382053376, coefficient := (-39560668459482776290382053376) }, { argument := 2153380087219124681436037120, coefficient := (-2153380087219124681436037120) }, { argument := 71553744041024057271717462016, coefficient := (-71553744041024057271717462016) }, { argument := 39560668459482776290382053376, coefficient := (-39560668459482776290382053376) }, { argument := 5829012669760625145607618560, coefficient := (-5829012669760625145607618560) }, { argument := 2276430377917360377518096384, coefficient := (-2276430377917360377518096384) }, { argument := 2153380087219124681436037120, coefficient := (-2153380087219124681436037120) }, { argument := 2891681831408538857928392704, coefficient := (-2891681831408538857928392704) }, { argument := 12959064837317367559094272, coefficient := (-12959064837317367559094272) }, { argument := 1358734575649169921496055808, coefficient := (-1358734575649169921496055808) }, { argument := 14645800671887418829307904000, coefficient := (-14645800671887418829307904000) }, { argument := 1358735612125602563051487232, coefficient := (-1358735612125602563051487232) }] }

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
def constantNumerator : ℤ := (-966169332066052165481100535136256)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    11240197, 2442418873, 42739285547, 42739306509, 2442397911, 2351010771,
    32070195, 10465011, 8217523629, 105662853, 2351010015, 211663287,
    94860261, 32070195, 10465011, 245521195, 9402607863, 880604655,
    779964123, 36507352983, 9938252535, 4701305469, 36507352983, 880604655,
    880604655, 377401995, 880604655, 9938252535, 377401995, 982081705,
    779964123, 8233452451, 237616157261, 102031677783, 267699154485, 104699172627,
    3334368555, 102031677783, 58018012857, 104699172627, 1634507465661, 2000621133,
    118808087867, 102031677783, 3334368555, 2000621133, 3334368555, 51349275747,
    58018012857, 8233452451, 91568824691, 43889221481, 17049227447, 1086024778349,
    34551089251, 34098463145, 17742451237, 17742451237, 600441902389, 32683462805,
    1086024778349, 600441902389, 91568808189, 34551089251
  ]
def negativeCoefficients : Array ℕ := #[
    12959064837317367559094272, 2815917241939319499205378048, 98550082797337817757194911744, 98550131132418976894647533568, 2815893074398739930479067136, 2710530875448223360924778496,
    295795339779479846843842560, 12065336227847204279156736, 9474159706488997380467195904, 243641950923624189637165056, 2710530003839565878148464640, 244031155318070873646170112,
    218732869679036413060841472, 295795339779479846843842560, 12065336227847204279156736, 1132266662209084298918625280, 10840468804638130100175372288, 1015268043806393391938273280,
    899237410228519861431042048, 42090112330373623191498129408, 11458025065815011137589084160, 10840472349871756766229823488, 42090112330373623191498129408, 1015268043806393391938273280,
    1015268043806393391938273280, 870229751834051478804234240, 1015268043806393391938273280, 11458025065815011137589084160, 870229751834051478804234240, 1132263116975457632864174080,
    899237410228519861431042048, 9492524387915852025929138176, 273952777548249287026578292736, 235269030934274721501639868416, 308636111970826967816979087360, 241419855272425694612793851904,
    7688530422688716388942479360, 235269030934274721501639868416, 133780429354783665167599140864, 241419855272425694612793851904, 3768917613202008773859603382272, 147619784115623354667695603712,
    273952798846168241628862480384, 235269030934274721501639868416, 7688530422688716388942479360, 147619784115623354667695603712, 7688530422688716388942479360, 236806737018812464779428364288,
    133780429354783665167599140864, 9492524387915852025929138176, 105571667137828319623607484416, 101201654531795337517478182912, 157251367684636739258785202176, 2504202642988893138996321845248,
    79669387610136755066950909952, 157251405735658077303162798080, 81822614302302613312003637248, 81822614302302613312003637248, 1384524763062646851568903651328, 75362934225805038576845455360,
    2504202642988893138996321845248, 1384524763062646851568903651328, 105571648112317650601418686464, 79669387610136755066950909952
  ]
def negativeScales : Array ℕ := #[
    23, 31, 35, 35, 31, 31,
    24, 23, 32, 26, 31, 27,
    26, 24, 23, 27, 33, 29,
    29, 35, 33, 32, 35, 29,
    29, 28, 29, 33, 28, 29,
    29, 32, 37, 36, 37, 36,
    31, 36, 35, 36, 40, 30,
    36, 36, 31, 30, 31, 35,
    35, 32, 36, 35, 33, 39,
    35, 34, 34, 34, 39, 34,
    39, 39, 36, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23422163985218119, 31185663496644865, 35314843740202766, 35314844447789841, 31185651114696970, 31130634002604031,
    24934729798234083, 23319070492253999, 32936056561902796, 26654893028823861, 31130633538685431, 27657195814694722,
    26499300502088315, 24934729798234083, 23319070492253999, 27871272334499401, 33130413805373899, 29713919229782749,
    29538832523125513, 35087468016804438, 33210345055802159, 32130414277188377, 35087468016804438, 29713919229782749,
    29713919229782749, 28491526808346416, 29713919229782749, 33210345055802159, 28491526808346416, 29871267817277976,
    29538832523125513, 32938850370962265, 37789841983150499, 36570226179148915, 37961821638773128, 36607459085352405,
    31634766431355589, 36570226179148915, 35755781832557601, 36607459085352405, 40571993105323231, 30897800841373533,
    36789842095309979, 36570226179148915, 31634766431355589, 30897800841373533, 31634766431355589, 35579624877151922,
    35755781832557601, 32938850370962265, 36414137454192418, 35353147628379406, 33988987336490881, 39982194175948441,
    35008012142330718, 34988987685588199, 34046486290145354, 34046486290145354, 39127233704029715, 34927841800781805,
    39982194175948441, 39127233704029715, 36414137194198301, 35008012142330718
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
noncomputable def negativeCeiling : ℝ := 7389154981 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12959064837317367559094272, coefficient := (-12959064837317367559094272) }, { argument := 2815917241939319499205378048, coefficient := (-2815917241939319499205378048) }, { argument := 98550082797337817757194911744, coefficient := (-98550082797337817757194911744) }, { argument := 98550131132418976894647533568, coefficient := (-98550131132418976894647533568) }, { argument := 2815893074398739930479067136, coefficient := (-2815893074398739930479067136) }, { argument := 2710530875448223360924778496, coefficient := (-2710530875448223360924778496) }, { argument := 295795339779479846843842560, coefficient := (-295795339779479846843842560) }, { argument := 12065336227847204279156736, coefficient := (-12065336227847204279156736) }, { argument := 9474159706488997380467195904, coefficient := (-9474159706488997380467195904) }, { argument := 243641950923624189637165056, coefficient := (-243641950923624189637165056) }, { argument := 2710530003839565878148464640, coefficient := (-2710530003839565878148464640) }, { argument := 244031155318070873646170112, coefficient := (-244031155318070873646170112) }, { argument := 218732869679036413060841472, coefficient := (-218732869679036413060841472) }, { argument := 295795339779479846843842560, coefficient := (-295795339779479846843842560) }, { argument := 12065336227847204279156736, coefficient := (-12065336227847204279156736) }, { argument := 1132266662209084298918625280, coefficient := (-1132266662209084298918625280) }, { argument := 10840468804638130100175372288, coefficient := (-10840468804638130100175372288) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 899237410228519861431042048, coefficient := (-899237410228519861431042048) }, { argument := 42090112330373623191498129408, coefficient := (-42090112330373623191498129408) }, { argument := 11458025065815011137589084160, coefficient := (-11458025065815011137589084160) }, { argument := 10840472349871756766229823488, coefficient := (-10840472349871756766229823488) }, { argument := 42090112330373623191498129408, coefficient := (-42090112330373623191498129408) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 870229751834051478804234240, coefficient := (-870229751834051478804234240) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 11458025065815011137589084160, coefficient := (-11458025065815011137589084160) }, { argument := 870229751834051478804234240, coefficient := (-870229751834051478804234240) }, { argument := 1132263116975457632864174080, coefficient := (-1132263116975457632864174080) }, { argument := 899237410228519861431042048, coefficient := (-899237410228519861431042048) }, { argument := 9492524387915852025929138176, coefficient := (-9492524387915852025929138176) }, { argument := 273952777548249287026578292736, coefficient := (-273952777548249287026578292736) }, { argument := 235269030934274721501639868416, coefficient := (-235269030934274721501639868416) }, { argument := 308636111970826967816979087360, coefficient := (-308636111970826967816979087360) }, { argument := 241419855272425694612793851904, coefficient := (-241419855272425694612793851904) }, { argument := 7688530422688716388942479360, coefficient := (-7688530422688716388942479360) }, { argument := 235269030934274721501639868416, coefficient := (-235269030934274721501639868416) }, { argument := 133780429354783665167599140864, coefficient := (-133780429354783665167599140864) }, { argument := 241419855272425694612793851904, coefficient := (-241419855272425694612793851904) }, { argument := 3768917613202008773859603382272, coefficient := (-3768917613202008773859603382272) }, { argument := 147619784115623354667695603712, coefficient := (-147619784115623354667695603712) }, { argument := 273952798846168241628862480384, coefficient := (-273952798846168241628862480384) }, { argument := 235269030934274721501639868416, coefficient := (-235269030934274721501639868416) }, { argument := 7688530422688716388942479360, coefficient := (-7688530422688716388942479360) }, { argument := 147619784115623354667695603712, coefficient := (-147619784115623354667695603712) }, { argument := 7688530422688716388942479360, coefficient := (-7688530422688716388942479360) }, { argument := 236806737018812464779428364288, coefficient := (-236806737018812464779428364288) }, { argument := 133780429354783665167599140864, coefficient := (-133780429354783665167599140864) }, { argument := 9492524387915852025929138176, coefficient := (-9492524387915852025929138176) }, { argument := 105571667137828319623607484416, coefficient := (-105571667137828319623607484416) }, { argument := 101201654531795337517478182912, coefficient := (-101201654531795337517478182912) }, { argument := 157251367684636739258785202176, coefficient := (-157251367684636739258785202176) }, { argument := 2504202642988893138996321845248, coefficient := (-2504202642988893138996321845248) }, { argument := 79669387610136755066950909952, coefficient := (-79669387610136755066950909952) }, { argument := 157251405735658077303162798080, coefficient := (-157251405735658077303162798080) }, { argument := 81822614302302613312003637248, coefficient := (-81822614302302613312003637248) }, { argument := 81822614302302613312003637248, coefficient := (-81822614302302613312003637248) }, { argument := 1384524763062646851568903651328, coefficient := (-1384524763062646851568903651328) }, { argument := 75362934225805038576845455360, coefficient := (-75362934225805038576845455360) }, { argument := 2504202642988893138996321845248, coefficient := (-2504202642988893138996321845248) }, { argument := 1384524763062646851568903651328, coefficient := (-1384524763062646851568903651328) }, { argument := 105571648112317650601418686464, coefficient := (-105571648112317650601418686464) }, { argument := 79669387610136755066950909952, coefficient := (-79669387610136755066950909952) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
