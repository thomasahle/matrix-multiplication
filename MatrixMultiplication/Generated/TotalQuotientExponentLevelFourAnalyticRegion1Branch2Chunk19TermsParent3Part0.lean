import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 19, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

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
def constantNumerator : ℤ := (-60055810706374352858373535544901632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    308945309, 209, 5703524143, 3289, 99, 5703263035,
    99, 99, 8481, 99, 3289, 8481,
    309467535, 99, 99, 209, 70147338442462413, 801,
    45, 125205310127326003, 2433, 70147336381080781, 2433, 2433,
    801, 45, 70181177007038881, 209364295, 70181156763246175, 209364295,
    209364295, 5726645677, 1674913819, 1869, 1869, 307257981,
    105, 105, 209, 70147318127242035, 801, 45,
    125205273181908173, 2433, 70147316065860403, 2433, 2433, 801,
    45, 125246435810784863, 5726645677, 125246398995265953, 5726645677, 5670813375,
    5677, 5677, 3289, 99, 70181174966628769, 1674913819,
    70181154722836063, 1674913819, 708819805, 99
  ]
def negativeCoefficients : Array ℕ := #[
    1458952972261405747265681752064, 16170591763165279840869810176, 53868262494282034796319060525056, 127237024662800491379475611648, 15319507986156580901876662272, 53865796398946816541674145054720,
    15319507986156580901876662272, 15319507986156580901876662272, 656185592073706881963717033984, 15319507986156580901876662272, 127237024662800491379475611648, 656185592073706881963717033984,
    1461419114820288830607049359360, 15319507986156580901876662272, 15319507986156580901876662272, 16170591763165279840869810176, 39489440908813224056487313145856, 30987186608362175006068703232,
    1740853180245066011576893440, 140968647008558194049783663951872, 47061064305958284512962019328, 39489439748358530338539199004672, 47061064305958284512962019328, 47061064305958284512962019328,
    30987186608362175006068703232, 1740853180245066011576893440, 39508490327165390775312158031872, 3862089568037628308849950720, 39508478930923229861916547481600, 3862089568037628308849950720,
    3862089568037628308849950720, 13204745900554271639421845504, 3862088320576560324241522688, 36151717709755870840413487104, 36151717709755870840413487104, 1450984791068598274546546507776,
    2030995376952577013506375680, 2030995376952577013506375680, 16170591763165279840869810176, 39489429472360858517698951249920, 30987186608362175006068703232, 1740853180245066011576893440,
    140968605411715700990963930365952, 47061064305958284512962019328, 39489428311906164799750837108736, 47061064305958284512962019328, 47061064305958284512962019328, 30987186608362175006068703232,
    1740853180245066011576893440, 141014950411733363766549662400512, 13204745900554271639421845504, 141014908961144052634687396380672, 13204745900554271639421845504, 53559318025417784918664019968000,
    54904575023617998598455689216, 54904575023617998598455689216, 127237024662800491379475611648, 15319507986156580901876662272, 39508489178516613264538156924928, 3862088320576560324241522688,
    39508477782274452351142546374656, 3862088320576560324241522688, 53556910232419164172658912788480, 15319507986156580901876662272
  ]
def negativeScales : Array ℕ := #[
    28, 7, 32, 11, 6, 32,
    6, 6, 13, 6, 11, 13,
    28, 6, 6, 7, 55, 9,
    5, 56, 11, 55, 11, 11,
    9, 5, 55, 27, 55, 27,
    27, 32, 30, 10, 10, 28,
    6, 6, 7, 55, 9, 5,
    56, 11, 55, 11, 11, 9,
    5, 56, 32, 56, 32, 32,
    12, 12, 11, 6, 55, 30,
    55, 30, 29, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28202776226944033, 7707359132166870, 32409206473711264, 11683433292884184, 6629356620092098, 32409140425452289,
    6629356620092098, 6629356620092098, 13050018668552332, 6629356620092098, 11683433292884184, 13050018668552332,
    28205212829116266, 6629356620092098, 6629356620092098, 7707359132166870, 55961237896372964, 9645658432427781,
    5491853096329881, 56797073363918730, 11248520604938430, 55961237853977261, 11248520604938430, 11248520604938430,
    9645658432427781, 5491853096329881, 55961933674282268, 27641440185059200, 55961933258136074, 27641440185059200,
    27641440185059200, 32415043196780747, 30641439719066333, 10868050856180197, 10868050856180197, 28194875244064877,
    6714245517766967, 6714245517766967, 7707359132166870, 55961237478556996, 9645658432427781, 5491853096329881,
    56797072938210112, 11248520604938430, 55961237436161281, 11248520604938430, 11248520604938430, 9645658432427781,
    5491853096329881, 56797547162339521, 32415043196780747, 56797546738266974, 32415043196780747, 32400908532349484,
    12470913026274977, 12470913026274977, 11683433292884184, 6629356620092098, 55961933632338113, 30641439719066333,
    55961933216191906, 30641439719066333, 29400843673624048, 6629356620092098
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
noncomputable def negativeCeiling : ℝ := 682156823557 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1458952972261405747265681752064, coefficient := (-1458952972261405747265681752064) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 53868262494282034796319060525056, coefficient := (-53868262494282034796319060525056) }, { argument := 127237024662800491379475611648, coefficient := (-127237024662800491379475611648) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 53865796398946816541674145054720, coefficient := (-53865796398946816541674145054720) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 656185592073706881963717033984, coefficient := (-656185592073706881963717033984) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 127237024662800491379475611648, coefficient := (-127237024662800491379475611648) }, { argument := 656185592073706881963717033984, coefficient := (-656185592073706881963717033984) }, { argument := 1461419114820288830607049359360, coefficient := (-1461419114820288830607049359360) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 39489440908813224056487313145856, coefficient := (-39489440908813224056487313145856) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 140968647008558194049783663951872, coefficient := (-140968647008558194049783663951872) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 39489439748358530338539199004672, coefficient := (-39489439748358530338539199004672) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 39508490327165390775312158031872, coefficient := (-39508490327165390775312158031872) }, { argument := 3862089568037628308849950720, coefficient := (-3862089568037628308849950720) }, { argument := 39508478930923229861916547481600, coefficient := (-39508478930923229861916547481600) }, { argument := 3862089568037628308849950720, coefficient := (-3862089568037628308849950720) }, { argument := 3862089568037628308849950720, coefficient := (-3862089568037628308849950720) }, { argument := 13204745900554271639421845504, coefficient := (-13204745900554271639421845504) }, { argument := 3862088320576560324241522688, coefficient := (-3862088320576560324241522688) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 1450984791068598274546546507776, coefficient := (-1450984791068598274546546507776) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 39489429472360858517698951249920, coefficient := (-39489429472360858517698951249920) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 140968605411715700990963930365952, coefficient := (-140968605411715700990963930365952) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 39489428311906164799750837108736, coefficient := (-39489428311906164799750837108736) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 47061064305958284512962019328, coefficient := (-47061064305958284512962019328) }, { argument := 30987186608362175006068703232, coefficient := (-30987186608362175006068703232) }, { argument := 1740853180245066011576893440, coefficient := (-1740853180245066011576893440) }, { argument := 141014950411733363766549662400512, coefficient := (-141014950411733363766549662400512) }, { argument := 13204745900554271639421845504, coefficient := (-13204745900554271639421845504) }, { argument := 141014908961144052634687396380672, coefficient := (-141014908961144052634687396380672) }, { argument := 13204745900554271639421845504, coefficient := (-13204745900554271639421845504) }, { argument := 53559318025417784918664019968000, coefficient := (-53559318025417784918664019968000) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 127237024662800491379475611648, coefficient := (-127237024662800491379475611648) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 39508489178516613264538156924928, coefficient := (-39508489178516613264538156924928) }, { argument := 3862088320576560324241522688, coefficient := (-3862088320576560324241522688) }, { argument := 39508477782274452351142546374656, coefficient := (-39508477782274452351142546374656) }, { argument := 3862088320576560324241522688, coefficient := (-3862088320576560324241522688) }, { argument := 53556910232419164172658912788480, coefficient := (-53556910232419164172658912788480) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }] }

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
def constantNumerator : ℤ := 64917851015847250567554605273579520
def positiveArguments : Array ℕ := #[
    13947, 11, 209, 319, 3289, 99,
    319, 99, 99, 8481, 99, 3289,
    8481, 11, 99, 99, 209, 195,
    3471, 195, 6175, 10543, 195, 10543,
    10543, 3471, 195, 483, 541, 483,
    541, 707, 23314042191, 23314035377, 33458594303, 119410573269,
    8364648331, 305218061
  ]
def positiveCoefficients : Array ℕ := #[
    1104995182586444716417157475336192, 27234680864278366047780732928, 32341183526330559681739620352, 24681429533252269230801289216, 254474049325600982758951223296, 30639015972313161803753324544,
    24681429533252269230801289216, 30639015972313161803753324544, 30639015972313161803753324544, 1312371184147413763927434067968, 30639015972313161803753324544, 254474049325600982758951223296,
    1312371184147413763927434067968, 27234680864278366047780732928, 30639015972313161803753324544, 30639015972313161803753324544, 32341183526330559681739620352, 7543697114395286050166538240,
    134277808636236091692964380672, 7543697114395286050166538240, 119441870977925362460970188800, 203931278659152566222835417088, 7543697114395286050166538240, 203931278659152566222835417088,
    203931278659152566222835417088, 134277808636236091692964380672, 7543697114395286050166538240, 37370314935927417048517312512, 41857847578336920545026637824, 37370314935927417048517312512,
    41857847578336920545026637824, 224057243590339546714542291550208, 440389805691948749061239020191744, 440389676979127891966189075693568, 158003744300420458438600203173888, 563900488905775603166081370292224,
    158003739677223671709217538965504, 2882703082465725655764447526912
  ]
def positiveScales : Array ℕ := #[
    13, 3, 7, 8, 11, 6,
    8, 6, 6, 13, 6, 11,
    13, 3, 6, 6, 7, 7,
    11, 7, 12, 13, 7, 13,
    13, 11, 7, 8, 9, 8,
    9, 9, 34, 34, 34, 36,
    32, 28
  ]
def negativeArguments : Array ℕ := #[
    209364295, 5726645677, 1674913819, 5677, 5677, 99,
    5677, 5677, 8481, 99, 1869, 1869,
    3289, 8481, 307767861, 105, 105, 99,
    99, 209, 11, 13, 1, 707,
    11117, 5553
  ]
def negativeCoefficients : Array ℕ := #[
    3862089568037628308849950720, 13204745900554271639421845504, 3862088320576560324241522688, 54904575023617998598455689216, 54904575023617998598455689216, 15319507986156580901876662272,
    54904575023617998598455689216, 54904575023617998598455689216, 656185592073706881963717033984, 15319507986156580901876662272, 36151717709755870840413487104, 36151717709755870840413487104,
    127237024662800491379475611648, 656185592073706881963717033984, 1453392631290883849248105824256, 2030995376952577013506375680, 2030995376952577013506375680, 15319507986156580901876662272,
    15319507986156580901876662272, 16170591763165279840869810176, 3486039150627630854115933814784, 1029966112685436388716071354368, 158456325028528675187087900672, 224057243590339546714542291550208,
    880779482671076641027428095885312, 879907972883419733313899112431616
  ]
def negativeScales : Array ℕ := #[
    27, 32, 30, 12, 12, 6,
    12, 12, 13, 6, 10, 10,
    11, 13, 28, 6, 6, 6,
    6, 7, 3, 3, 0, 9,
    13, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13767667211219704, 3459431618637292, 7707359132075544, 8317412613764869, 11683433292832372, 6629356620078832,
    8317412613764869, 6629356620078832, 6629356620078832, 13050018668552331, 6629356620078832, 11683433292832372,
    13050018668552331, 3459431618637292, 6629356620078832, 6629356620078832, 7707359132075544, 7607330313749179,
    11761135649810892, 7607330313749179, 12592223421359118, 13363997822358364, 7607330313749179, 13363997822358364,
    13363997822358364, 11761135649810892, 7607330313749179, 8915879378478017, 9079484783826815, 8915879378478017,
    9079484783826815, 9465566404809393, 34440480109639622, 34440479687982778, 34961657782747680, 36797139630136630,
    32961657740534357, 28185265093958704
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    27641440185059200, 32415043196780747, 30641439719066333, 12470913026274977, 12470913026274977, 6629356620092098,
    12470913026274977, 12470913026274977, 13050018668552332, 6629356620092098, 10868050856180197, 10868050856180197,
    11683433292884184, 13050018668552332, 28197267343601976, 6714245517766967, 6714245517766967, 6629356620092098,
    6629356620092098, 7707359132166870, 3459431618637364, 3700439718214233, 0, 9465566404809482,
    13440479898811251, 12439051680591762
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 477202260633 / 500000000000
noncomputable def negativeCeiling : ℝ := 300738174733 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3862089568037628308849950720, coefficient := (-3862089568037628308849950720) }, { argument := 13204745900554271639421845504, coefficient := (-13204745900554271639421845504) }, { argument := 3862088320576560324241522688, coefficient := (-3862088320576560324241522688) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 656185592073706881963717033984, coefficient := (-656185592073706881963717033984) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 127237024662800491379475611648, coefficient := (-127237024662800491379475611648) }, { argument := 656185592073706881963717033984, coefficient := (-656185592073706881963717033984) }, { argument := 1453392631290883849248105824256, coefficient := (-1453392631290883849248105824256) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 15319507986156580901876662272, coefficient := (-15319507986156580901876662272) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 1104995182586444716417157475336192, coefficient := 1104995182586444716417157475336192 }, { argument := 27234680864278366047780732928, coefficient := 27234680864278366047780732928 }, { argument := 32341183526330559681739620352, coefficient := 32341183526330559681739620352 }, { argument := 24681429533252269230801289216, coefficient := 24681429533252269230801289216 }, { argument := 254474049325600982758951223296, coefficient := 254474049325600982758951223296 }, { argument := 30639015972313161803753324544, coefficient := 30639015972313161803753324544 }, { argument := 24681429533252269230801289216, coefficient := 24681429533252269230801289216 }, { argument := 30639015972313161803753324544, coefficient := 30639015972313161803753324544 }, { argument := 30639015972313161803753324544, coefficient := 30639015972313161803753324544 }, { argument := 1312371184147413763927434067968, coefficient := 1312371184147413763927434067968 }, { argument := 30639015972313161803753324544, coefficient := 30639015972313161803753324544 }, { argument := 254474049325600982758951223296, coefficient := 254474049325600982758951223296 }, { argument := 1312371184147413763927434067968, coefficient := 1312371184147413763927434067968 }, { argument := 27234680864278366047780732928, coefficient := 27234680864278366047780732928 }, { argument := 30639015972313161803753324544, coefficient := 30639015972313161803753324544 }, { argument := 30639015972313161803753324544, coefficient := 30639015972313161803753324544 }, { argument := 32341183526330559681739620352, coefficient := 32341183526330559681739620352 }, { argument := 3486039150627630854115933814784, coefficient := (-3486039150627630854115933814784) }, { argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 134277808636236091692964380672, coefficient := 134277808636236091692964380672 }, { argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 119441870977925362460970188800, coefficient := 119441870977925362460970188800 }, { argument := 203931278659152566222835417088, coefficient := 203931278659152566222835417088 }, { argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 203931278659152566222835417088, coefficient := 203931278659152566222835417088 }, { argument := 203931278659152566222835417088, coefficient := 203931278659152566222835417088 }, { argument := 134277808636236091692964380672, coefficient := 134277808636236091692964380672 }, { argument := 7543697114395286050166538240, coefficient := 7543697114395286050166538240 }, { argument := 1029966112685436388716071354368, coefficient := (-1029966112685436388716071354368) }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 224057243590339546714542291550208, coefficient := 224057243590339546714542291550208 }, { argument := 224057243590339546714542291550208, coefficient := (-224057243590339546714542291550208) }, { argument := 440389805691948749061239020191744, coefficient := 440389805691948749061239020191744 }, { argument := 440389676979127891966189075693568, coefficient := 440389676979127891966189075693568 }, { argument := 880779482671076641027428095885312, coefficient := (-880779482671076641027428095885312) }, { argument := 158003744300420458438600203173888, coefficient := 158003744300420458438600203173888 }, { argument := 563900488905775603166081370292224, coefficient := 563900488905775603166081370292224 }, { argument := 158003739677223671709217538965504, coefficient := 158003739677223671709217538965504 }, { argument := 879907972883419733313899112431616, coefficient := (-879907972883419733313899112431616) }, { argument := 2882703082465725655764447526912, coefficient := 2882703082465725655764447526912 }] }

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

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6276140573176518155203183032401920)
def positiveArguments : Array ℕ := #[
    5685862135, 11371208227, 152867057
  ]
def positiveCoefficients : Array ℕ := #[
    107402899090166567445752279203840, 107398025201832728445102256553984, 2887577065246894313807374450688
  ]
def positiveScales : Array ℕ := #[
    32, 33, 27
  ]
def negativeArguments : Array ℕ := #[
    87
  ]
def negativeCoefficients : Array ℕ := #[
    220571204439711915860426357735424
  ]
def negativeScales : Array ℕ := #[
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    32404731972424296, 33404666502179664, 27187702297103112
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6442943495848765
  ]

abbrev PositiveTerm := Fin 3
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 86022430839 / 1000000000000
noncomputable def negativeCeiling : ℝ := 855310187 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 107402899090166567445752279203840, coefficient := 107402899090166567445752279203840 }, { argument := 107398025201832728445102256553984, coefficient := 107398025201832728445102256553984 }, { argument := 2887577065246894313807374450688, coefficient := 2887577065246894313807374450688 }, { argument := 220571204439711915860426357735424, coefficient := (-220571204439711915860426357735424) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
