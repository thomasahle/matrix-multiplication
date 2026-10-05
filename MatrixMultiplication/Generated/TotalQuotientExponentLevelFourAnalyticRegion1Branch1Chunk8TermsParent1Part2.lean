import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-471877219820734243529927214235648)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7011, 196137, 5985, 7011, 6327, 3249,
    3249, 6327, 196137, 6327, 513, 8379,
    419121, 1257363, 2654433, 6845643, 5727987, 160243929,
    4889745, 5727987, 5169159, 2654433, 2654433, 5169159,
    160243929, 5169159, 419121, 6845643, 92653083, 32310834117,
    173635, 1165856920943, 6765, 11275, 345015, 11275,
    6765, 5527005, 354035, 129243420701, 345015, 11275,
    354035, 11275, 345015, 11275, 92653083, 26847,
    80541, 170031, 438501, 366909, 10264503, 313215,
    366909, 331113, 170031, 170031, 331113, 10264503,
    331113, 26847, 438501, 165913443
  ]
def negativeCoefficients : Array ℕ := #[
    16951557842636330287729999872, 29639385435219315304918155264, 904427628799194451327057920, 16951557842636330287729999872, 956109207587719848545746944, 981949996981982547155091456,
    981949996981982547155091456, 956109207587719848545746944, 29639385435219315304918155264, 956109207587719848545746944, 1240357890924609533248536576, 1266198680318872231857881088,
    31667887402668937145751699456, 23750915552001702859313774592, 25070410860446241907053428736, 32327635056891206669621526528, 432794461169808807658606559232, 756730559392943143878691651584,
    23091167897779433335443947520, 432794461169808807658606559232, 24410663206223972383183601664, 25070410860446241907053428736, 25070410860446241907053428736, 24410663206223972383183601664,
    756730559392943143878691651584, 24410663206223972383183601664, 31667887402668937145751699456, 32327635056891206669621526528, 3418295419482338407540064256, 298014843882191071551512641536,
    26238979336098267093763358720, 2688283030899818810389861236736, 16356766339385932733774561280, 851914913509683996550758400, 26068596353396330294453207040, 27261277232309887889624268800,
    16356766339385932733774561280, 417608690602447095109181767680, 26750128284204077491693813760, 298015038110265266648595300352, 26068596353396330294453207040, 851914913509683996550758400,
    26750128284204077491693813760, 851914913509683996550758400, 26068596353396330294453207040, 27261277232309887889624268800, 3418295419482338407540064256, 2028501967449621840833544192,
    1521376475587216380625158144, 1605897390897617290659889152, 2070762425104822295850909696, 27722860221811498491391770624, 48472744930514921904918233088, 1479116017932015925607792640,
    27722860221811498491391770624, 1563636933242416835642523648, 1605897390897617290659889152, 1605897390897617290659889152, 1563636933242416835642523648, 48472744930514921904918233088,
    1563636933242416835642523648, 2028501967449621840833544192, 2070762425104822295850909696, 6121125642817994981193547776
  ]
def negativeScales : Array ℕ := #[
    12, 17, 12, 12, 12, 11,
    11, 12, 17, 12, 9, 13,
    18, 20, 21, 22, 22, 27,
    22, 22, 22, 21, 21, 22,
    27, 22, 18, 22, 26, 34,
    17, 40, 12, 13, 18, 13,
    12, 22, 18, 36, 18, 13,
    18, 13, 18, 13, 26, 14,
    16, 17, 18, 18, 23, 18,
    18, 18, 17, 17, 18, 23,
    18, 14, 18, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12775404519891943, 17581502190905084, 12547135531832084, 12775404519891943, 12627305880526679, 11665780028361156,
    11665780028361156, 12627305880526679, 17581502190905084, 12627305880526679, 9002815015607055, 13032562359001107,
    18677007283794480, 20261969784473894, 21339972296475168, 22706754627231575, 22449596787649711, 27255694459047407,
    22221327799976548, 22449596787649711, 22301498148660532, 21339972296475168, 21339972296475168, 22301498148660532,
    27255694459047407, 22301498148660532, 18677007283794480, 22706754627231575, 26465335646452397, 34911298949043322,
    17405698258837653, 40084527884209212, 12723874218989575, 13460839813030175, 18396299560835401, 13460839813030175,
    12723874218989575, 22398066487009589, 18433532467034396, 36911299889304588, 18396299560835401, 13460839813030175,
    18433532467034396, 13460839813030175, 18396299560835401, 13460839813030175, 26465335646452397, 14712473263874332,
    16297435764498682, 17375438276499957, 18742220607361118, 18485062767674616, 23291160439072194, 18256793780001336,
    18485062767674616, 18336964128685319, 17375438276499957, 17375438276499957, 18336964128685319, 23291160439072194,
    18336964128685319, 14712473263874332, 18742220607361118, 27305855543305370
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
noncomputable def negativeCeiling : ℝ := 519307697 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16951557842636330287729999872, coefficient := (-16951557842636330287729999872) }, { argument := 29639385435219315304918155264, coefficient := (-29639385435219315304918155264) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 16951557842636330287729999872, coefficient := (-16951557842636330287729999872) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 981949996981982547155091456, coefficient := (-981949996981982547155091456) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 29639385435219315304918155264, coefficient := (-29639385435219315304918155264) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 1240357890924609533248536576, coefficient := (-1240357890924609533248536576) }, { argument := 1266198680318872231857881088, coefficient := (-1266198680318872231857881088) }, { argument := 31667887402668937145751699456, coefficient := (-31667887402668937145751699456) }, { argument := 23750915552001702859313774592, coefficient := (-23750915552001702859313774592) }, { argument := 25070410860446241907053428736, coefficient := (-25070410860446241907053428736) }, { argument := 32327635056891206669621526528, coefficient := (-32327635056891206669621526528) }, { argument := 432794461169808807658606559232, coefficient := (-432794461169808807658606559232) }, { argument := 756730559392943143878691651584, coefficient := (-756730559392943143878691651584) }, { argument := 23091167897779433335443947520, coefficient := (-23091167897779433335443947520) }, { argument := 432794461169808807658606559232, coefficient := (-432794461169808807658606559232) }, { argument := 24410663206223972383183601664, coefficient := (-24410663206223972383183601664) }, { argument := 25070410860446241907053428736, coefficient := (-25070410860446241907053428736) }, { argument := 25070410860446241907053428736, coefficient := (-25070410860446241907053428736) }, { argument := 24410663206223972383183601664, coefficient := (-24410663206223972383183601664) }, { argument := 756730559392943143878691651584, coefficient := (-756730559392943143878691651584) }, { argument := 24410663206223972383183601664, coefficient := (-24410663206223972383183601664) }, { argument := 31667887402668937145751699456, coefficient := (-31667887402668937145751699456) }, { argument := 32327635056891206669621526528, coefficient := (-32327635056891206669621526528) }, { argument := 3418295419482338407540064256, coefficient := (-3418295419482338407540064256) }, { argument := 298014843882191071551512641536, coefficient := (-298014843882191071551512641536) }, { argument := 26238979336098267093763358720, coefficient := (-26238979336098267093763358720) }, { argument := 2688283030899818810389861236736, coefficient := (-2688283030899818810389861236736) }, { argument := 16356766339385932733774561280, coefficient := (-16356766339385932733774561280) }, { argument := 851914913509683996550758400, coefficient := (-851914913509683996550758400) }, { argument := 26068596353396330294453207040, coefficient := (-26068596353396330294453207040) }, { argument := 27261277232309887889624268800, coefficient := (-27261277232309887889624268800) }, { argument := 16356766339385932733774561280, coefficient := (-16356766339385932733774561280) }, { argument := 417608690602447095109181767680, coefficient := (-417608690602447095109181767680) }, { argument := 26750128284204077491693813760, coefficient := (-26750128284204077491693813760) }, { argument := 298015038110265266648595300352, coefficient := (-298015038110265266648595300352) }, { argument := 26068596353396330294453207040, coefficient := (-26068596353396330294453207040) }, { argument := 851914913509683996550758400, coefficient := (-851914913509683996550758400) }, { argument := 26750128284204077491693813760, coefficient := (-26750128284204077491693813760) }, { argument := 851914913509683996550758400, coefficient := (-851914913509683996550758400) }, { argument := 26068596353396330294453207040, coefficient := (-26068596353396330294453207040) }, { argument := 27261277232309887889624268800, coefficient := (-27261277232309887889624268800) }, { argument := 3418295419482338407540064256, coefficient := (-3418295419482338407540064256) }, { argument := 2028501967449621840833544192, coefficient := (-2028501967449621840833544192) }, { argument := 1521376475587216380625158144, coefficient := (-1521376475587216380625158144) }, { argument := 1605897390897617290659889152, coefficient := (-1605897390897617290659889152) }, { argument := 2070762425104822295850909696, coefficient := (-2070762425104822295850909696) }, { argument := 27722860221811498491391770624, coefficient := (-27722860221811498491391770624) }, { argument := 48472744930514921904918233088, coefficient := (-48472744930514921904918233088) }, { argument := 1479116017932015925607792640, coefficient := (-1479116017932015925607792640) }, { argument := 27722860221811498491391770624, coefficient := (-27722860221811498491391770624) }, { argument := 1563636933242416835642523648, coefficient := (-1563636933242416835642523648) }, { argument := 1605897390897617290659889152, coefficient := (-1605897390897617290659889152) }, { argument := 1605897390897617290659889152, coefficient := (-1605897390897617290659889152) }, { argument := 1563636933242416835642523648, coefficient := (-1563636933242416835642523648) }, { argument := 48472744930514921904918233088, coefficient := (-48472744930514921904918233088) }, { argument := 1563636933242416835642523648, coefficient := (-1563636933242416835642523648) }, { argument := 2028501967449621840833544192, coefficient := (-2028501967449621840833544192) }, { argument := 2070762425104822295850909696, coefficient := (-2070762425104822295850909696) }, { argument := 6121125642817994981193547776, coefficient := (-6121125642817994981193547776) }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3697532794245195670925618974818304)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    58344097917, 4857545, 2108673856663, 189255, 315425, 9652005,
    315425, 189255, 154621335, 9904345, 233376544021, 9652005,
    315425, 9904345, 315425, 9652005, 315425, 165913443,
    15746596977, 154937299889, 309874579501, 15746596977, 9277683652105, 7955280863,
    347314202152703, 6601493267, 81367157, 206051731, 834651363, 1164121366367,
    7955280863, 81367157, 2405875125793, 226127301224671, 7453034555, 604111389,
    129477187613, 233785279765, 904504047779445, 129477187613, 3816940685, 3822018701,
    7453034555, 7442878523, 233785279765, 7442878523, 9623457734027, 604111389,
    7805706991107, 1807570765468305, 148225, 18970594171692755, 5775, 9625,
    294525, 9625, 5775, 4718175, 302225, 903787025173835,
    294525, 9625, 302225, 9625
  ]
def negativeCoefficients : Array ℕ := #[
    538129321243174772451034791936, 45878215394062061519125872640, 4862270871098057468876398002176, 28599406998895830557377167360, 1489552447859157841530060800, 45580304904490229950819860480,
    47665678331493050928961945600, 28599406998895830557377167360, 730178609940559173918035804160, 46771946862777556224043909120, 538129672545274755184949460992, 45580304904490229950819860480,
    1489552447859157841530060800, 46771946862777556224043909120, 1489552447859157841530060800, 45580304904490229950819860480, 47665678331493050928961945600, 6121125642817994981193547776,
    18154590279160468165783191552, 714522179630992579852979142656, 714522132875413882026906877952, 18154590279160468165783191552, 2611435789905088777950330880, 18343628764280032173884440576,
    97760256962212146905159303168, 15222007100083219588326621184, 750479560592172329369337856, 15203934190807378806842589184, 15396600084033849722413252608, 2621368275892226927431254016,
    18343628764280032173884440576, 750479560592172329369337856, 43340393280085199959267213312, 4073547318134896877569010827264, 17185527626074844403450511360, 22287776369792391218617909248,
    298554067910085939431867416576, 539072153003192913237408481280, 4073524092534613811953108254720, 298554067910085939431867416576, 17602531990181156609054474240, 17625950205569707179669192704,
    17185527626074844403450511360, 17162109410686293832835792896, 539072153003192913237408481280, 17162109410686293832835792896, 43340200664979715004555067392, 22287776369792391218617909248,
    17576889548256380367233089536, 4070287512904430308322590064640, 1399945543846706323600179200, 42717980421316197317418931978240, 872693326034310435491020800, 45452777397620335181824000,
    1390854988367182256563814400, 1454488876723850725818368000, 872693326034310435491020800, 22280951480313488306130124800, 1427217210285278524709273600, 4070294909795172393838350172160,
    1390854988367182256563814400, 45452777397620335181824000, 1427217210285278524709273600, 45452777397620335181824000
  ]
def negativeScales : Array ℕ := #[
    35, 22, 40, 17, 18, 23,
    18, 17, 27, 23, 37, 23,
    18, 23, 18, 23, 18, 27,
    33, 37, 38, 33, 43, 32,
    48, 32, 26, 27, 29, 40,
    32, 26, 41, 47, 32, 29,
    36, 37, 49, 36, 31, 31,
    32, 32, 37, 32, 43, 29,
    42, 50, 17, 54, 12, 13,
    18, 13, 12, 22, 18, 49,
    18, 13, 18, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35763867669607796, 22211795930235387, 40939473121699943, 17529971890262358, 18266937484427848, 23202397232233137,
    18266937484427848, 17529971890262358, 27204164158407325, 23239630138432112, 37763868611429056, 23202397232233137,
    18266937484427848, 23239630138432112, 18266937484427848, 23202397232233137, 18266937484427848, 27305855543305370,
    33874321030706504, 37172893546745295, 38172893452340887, 33874321030706504, 43076901793057674, 32889265723716670,
    48303234734122490, 32620145255015792, 26277943247466539, 27618431342574390, 29636598463402469, 40082378614014967,
    32889265723716670, 26277943247466539, 41129698901663388, 47684128513236399, 32795180803109530, 29170239344314223,
    36913906983429694, 37766393137857725, 49684120287591452, 36913906983429694, 31829769622501882, 31831687692589916,
    32795180803109530, 32793213544121395, 37766393137857725, 32793213544121395, 43129692489966264, 29170239344314223,
    42827666447999971, 50682973552411541, 17177429271164528, 54074614383828065, 12495605231191017, 13232570825356989,
    18168030573162278, 13232570825356989, 12495605231191017, 22169797499336466, 18205263479361254, 49682976174203705,
    18168030573162278, 13232570825356989, 18205263479361254, 13232570825356989
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
noncomputable def negativeCeiling : ℝ := 21173703951 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 538129321243174772451034791936, coefficient := (-538129321243174772451034791936) }, { argument := 45878215394062061519125872640, coefficient := (-45878215394062061519125872640) }, { argument := 4862270871098057468876398002176, coefficient := (-4862270871098057468876398002176) }, { argument := 28599406998895830557377167360, coefficient := (-28599406998895830557377167360) }, { argument := 1489552447859157841530060800, coefficient := (-1489552447859157841530060800) }, { argument := 45580304904490229950819860480, coefficient := (-45580304904490229950819860480) }, { argument := 47665678331493050928961945600, coefficient := (-47665678331493050928961945600) }, { argument := 28599406998895830557377167360, coefficient := (-28599406998895830557377167360) }, { argument := 730178609940559173918035804160, coefficient := (-730178609940559173918035804160) }, { argument := 46771946862777556224043909120, coefficient := (-46771946862777556224043909120) }, { argument := 538129672545274755184949460992, coefficient := (-538129672545274755184949460992) }, { argument := 45580304904490229950819860480, coefficient := (-45580304904490229950819860480) }, { argument := 1489552447859157841530060800, coefficient := (-1489552447859157841530060800) }, { argument := 46771946862777556224043909120, coefficient := (-46771946862777556224043909120) }, { argument := 1489552447859157841530060800, coefficient := (-1489552447859157841530060800) }, { argument := 45580304904490229950819860480, coefficient := (-45580304904490229950819860480) }, { argument := 47665678331493050928961945600, coefficient := (-47665678331493050928961945600) }, { argument := 6121125642817994981193547776, coefficient := (-6121125642817994981193547776) }, { argument := 18154590279160468165783191552, coefficient := (-18154590279160468165783191552) }, { argument := 714522179630992579852979142656, coefficient := (-714522179630992579852979142656) }, { argument := 714522132875413882026906877952, coefficient := (-714522132875413882026906877952) }, { argument := 18154590279160468165783191552, coefficient := (-18154590279160468165783191552) }, { argument := 2611435789905088777950330880, coefficient := (-2611435789905088777950330880) }, { argument := 18343628764280032173884440576, coefficient := (-18343628764280032173884440576) }, { argument := 97760256962212146905159303168, coefficient := (-97760256962212146905159303168) }, { argument := 15222007100083219588326621184, coefficient := (-15222007100083219588326621184) }, { argument := 750479560592172329369337856, coefficient := (-750479560592172329369337856) }, { argument := 15203934190807378806842589184, coefficient := (-15203934190807378806842589184) }, { argument := 15396600084033849722413252608, coefficient := (-15396600084033849722413252608) }, { argument := 2621368275892226927431254016, coefficient := (-2621368275892226927431254016) }, { argument := 18343628764280032173884440576, coefficient := (-18343628764280032173884440576) }, { argument := 750479560592172329369337856, coefficient := (-750479560592172329369337856) }, { argument := 43340393280085199959267213312, coefficient := (-43340393280085199959267213312) }, { argument := 4073547318134896877569010827264, coefficient := (-4073547318134896877569010827264) }, { argument := 17185527626074844403450511360, coefficient := (-17185527626074844403450511360) }, { argument := 22287776369792391218617909248, coefficient := (-22287776369792391218617909248) }, { argument := 298554067910085939431867416576, coefficient := (-298554067910085939431867416576) }, { argument := 539072153003192913237408481280, coefficient := (-539072153003192913237408481280) }, { argument := 4073524092534613811953108254720, coefficient := (-4073524092534613811953108254720) }, { argument := 298554067910085939431867416576, coefficient := (-298554067910085939431867416576) }, { argument := 17602531990181156609054474240, coefficient := (-17602531990181156609054474240) }, { argument := 17625950205569707179669192704, coefficient := (-17625950205569707179669192704) }, { argument := 17185527626074844403450511360, coefficient := (-17185527626074844403450511360) }, { argument := 17162109410686293832835792896, coefficient := (-17162109410686293832835792896) }, { argument := 539072153003192913237408481280, coefficient := (-539072153003192913237408481280) }, { argument := 17162109410686293832835792896, coefficient := (-17162109410686293832835792896) }, { argument := 43340200664979715004555067392, coefficient := (-43340200664979715004555067392) }, { argument := 22287776369792391218617909248, coefficient := (-22287776369792391218617909248) }, { argument := 17576889548256380367233089536, coefficient := (-17576889548256380367233089536) }, { argument := 4070287512904430308322590064640, coefficient := (-4070287512904430308322590064640) }, { argument := 1399945543846706323600179200, coefficient := (-1399945543846706323600179200) }, { argument := 42717980421316197317418931978240, coefficient := (-42717980421316197317418931978240) }, { argument := 872693326034310435491020800, coefficient := (-872693326034310435491020800) }, { argument := 45452777397620335181824000, coefficient := (-45452777397620335181824000) }, { argument := 1390854988367182256563814400, coefficient := (-1390854988367182256563814400) }, { argument := 1454488876723850725818368000, coefficient := (-1454488876723850725818368000) }, { argument := 872693326034310435491020800, coefficient := (-872693326034310435491020800) }, { argument := 22280951480313488306130124800, coefficient := (-22280951480313488306130124800) }, { argument := 1427217210285278524709273600, coefficient := (-1427217210285278524709273600) }, { argument := 4070294909795172393838350172160, coefficient := (-4070294909795172393838350172160) }, { argument := 1390854988367182256563814400, coefficient := (-1390854988367182256563814400) }, { argument := 45452777397620335181824000, coefficient := (-45452777397620335181824000) }, { argument := 1427217210285278524709273600, coefficient := (-1427217210285278524709273600) }, { argument := 45452777397620335181824000, coefficient := (-45452777397620335181824000) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
