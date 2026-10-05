import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 14, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-299419736890064937665400965955584)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8388607, 239661337, 958367089, 478858909, 958367089, 4724516946125,
    727361775, 160726130451803, 306820413, 30013983, 306806589, 612976761,
    592404333371, 727361775, 30013983, 3813, 11685, 34563,
    77121, 3813, 38499, 78351, 3813, 11685,
    3813, 45099943737, 4940635879623, 1751515, 4517065, 3779585,
    105736195, 1235064669419, 3779585, 3410845, 1751515, 1751515,
    3410845, 105736195, 3410845, 11274888981, 4517065, 8388609,
    27628122561, 110479967169, 55202039997, 110479967169, 91194093769847, 27661629201,
    3117457334213249, 11675901123, 1141815777, 11675888835, 23315239815, 11435141118497,
    27661629201, 1141815777, 39897, 122265, 361647, 806949,
    39897, 402831, 819819, 39897
  ]
def negativeCoefficients : Array ℕ := #[
    39614076534765685927126761472, 35367770784016461519688564736, 35357504838898048827442331648, 35333550966955085878867787776, 35357504838898048827442331648, 1329833297379633982865408000,
    13417456512424110297867878400, 45240383825715107544084512768, 11319675270401734137731874816, 553660263033669229140246528, 11319165254821584216048795648, 11307425433298426204337995776,
    1333975967511151344256811008, 13417456512424110297867878400, 553660263033669229140246528, 18006383399181957199822848, 441446818818654434576302080, 326438305494847095041949696,
    364193625525389908525449216, 18006383399181957199822848, 363612774447996942164164608, 370002136299319572138295296, 18006383399181957199822848, 441446818818654434576302080,
    18006383399181957199822848, 203112089808383534853783552, 22250645906443445531477803008, 64619497892526770597396480, 83325142019310835770327040, 1115536595197304250312949760,
    1950488528492847523031941120, 22248947139895492905896247296, 1115536595197304250312949760, 62918984790091855581675520, 64619497892526770597396480, 64619497892526770597396480,
    62918984790091855581675520, 1950488528492847523031941120, 62918984790091855581675520, 203110343253901245419618304, 83325142019310835770327040, 39614085979498651666417188864,
    127412226529961977490800902144, 127374729977398536161086930944, 127287238021417173058420998144, 127374729977398536161086930944, 51337710840034127501552779264, 510266994532697829373762338816,
    1754972461088276000919349362688, 430764719691837896978161729536, 21062783417642816950744645632, 430764266344655541492221214720, 430090261884468232583160791040, 51499297280192126044457664512,
    510266994532697829373762338816, 21062783417642816950744645632, 188408255567050235090829312, 4619041104224457376420331520, 3415659342860717165195034624, 3810708910985177335546773504,
    188408255567050235090829312, 3804631225321724102156746752, 3871485767619709669447041024, 188408255567050235090829312
  ]
def negativeScales : Array ℕ := #[
    22, 27, 29, 28, 29, 42,
    29, 47, 28, 24, 28, 29,
    39, 29, 24, 11, 13, 15,
    16, 11, 15, 16, 11, 13,
    11, 35, 42, 20, 22, 21,
    26, 40, 21, 21, 20, 20,
    21, 26, 21, 33, 22, 23,
    34, 36, 35, 36, 46, 34,
    51, 33, 30, 33, 34, 43,
    34, 30, 15, 16, 18, 19,
    15, 18, 19, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22999999851693669, 27836421947611674, 29836003126236481, 28835025403267950, 29836003126236481, 42103303968499382,
    29438097869018137, 47191597826251394, 28192819228752624, 24839131449833303, 28192754225693164, 29191257139009122,
    39107791237578136, 29438097869018137, 24839131449833303, 11896710819843133, 13512370113670596, 15076940825560167,
    16234836138141279, 11896710819843133, 15232533352271859, 16257664067595541, 11896710819843133, 13512370113670596,
    11896710819843133, 35392406582567107, 42167833873037433, 20740171912959561, 22106954243450046, 21849796405678326,
    26655894075375398, 40167723723622224, 21849796405678326, 21701697765039121, 20740171912959561, 20740171912959561,
    21701697765039121, 26655894075375398, 21701697765039121, 33392394176824415, 22106954243450046, 23000000171982641,
    34685418477634670, 36684993839798950, 35684002531853580, 36684993839798950, 46374005624100337, 34687167079059085,
    51469291238653310, 33442814847460808, 30088682755958533, 33442813329132945, 34440554217845133, 43378539403369213,
    34687167079059085, 30088682755958533, 15283992648607578, 16899651950892089, 18464222658441707, 19622117971033051,
    15283992648607578, 18619815185163015, 19644945900495728, 15283992648607578
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
noncomputable def negativeCeiling : ℝ := 495738523 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39614076534765685927126761472, coefficient := (-39614076534765685927126761472) }, { argument := 35367770784016461519688564736, coefficient := (-35367770784016461519688564736) }, { argument := 35357504838898048827442331648, coefficient := (-35357504838898048827442331648) }, { argument := 35333550966955085878867787776, coefficient := (-35333550966955085878867787776) }, { argument := 35357504838898048827442331648, coefficient := (-35357504838898048827442331648) }, { argument := 1329833297379633982865408000, coefficient := (-1329833297379633982865408000) }, { argument := 13417456512424110297867878400, coefficient := (-13417456512424110297867878400) }, { argument := 45240383825715107544084512768, coefficient := (-45240383825715107544084512768) }, { argument := 11319675270401734137731874816, coefficient := (-11319675270401734137731874816) }, { argument := 553660263033669229140246528, coefficient := (-553660263033669229140246528) }, { argument := 11319165254821584216048795648, coefficient := (-11319165254821584216048795648) }, { argument := 11307425433298426204337995776, coefficient := (-11307425433298426204337995776) }, { argument := 1333975967511151344256811008, coefficient := (-1333975967511151344256811008) }, { argument := 13417456512424110297867878400, coefficient := (-13417456512424110297867878400) }, { argument := 553660263033669229140246528, coefficient := (-553660263033669229140246528) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 326438305494847095041949696, coefficient := (-326438305494847095041949696) }, { argument := 364193625525389908525449216, coefficient := (-364193625525389908525449216) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 363612774447996942164164608, coefficient := (-363612774447996942164164608) }, { argument := 370002136299319572138295296, coefficient := (-370002136299319572138295296) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 203112089808383534853783552, coefficient := (-203112089808383534853783552) }, { argument := 22250645906443445531477803008, coefficient := (-22250645906443445531477803008) }, { argument := 64619497892526770597396480, coefficient := (-64619497892526770597396480) }, { argument := 83325142019310835770327040, coefficient := (-83325142019310835770327040) }, { argument := 1115536595197304250312949760, coefficient := (-1115536595197304250312949760) }, { argument := 1950488528492847523031941120, coefficient := (-1950488528492847523031941120) }, { argument := 22248947139895492905896247296, coefficient := (-22248947139895492905896247296) }, { argument := 1115536595197304250312949760, coefficient := (-1115536595197304250312949760) }, { argument := 62918984790091855581675520, coefficient := (-62918984790091855581675520) }, { argument := 64619497892526770597396480, coefficient := (-64619497892526770597396480) }, { argument := 64619497892526770597396480, coefficient := (-64619497892526770597396480) }, { argument := 62918984790091855581675520, coefficient := (-62918984790091855581675520) }, { argument := 1950488528492847523031941120, coefficient := (-1950488528492847523031941120) }, { argument := 62918984790091855581675520, coefficient := (-62918984790091855581675520) }, { argument := 203110343253901245419618304, coefficient := (-203110343253901245419618304) }, { argument := 83325142019310835770327040, coefficient := (-83325142019310835770327040) }, { argument := 39614085979498651666417188864, coefficient := (-39614085979498651666417188864) }, { argument := 127412226529961977490800902144, coefficient := (-127412226529961977490800902144) }, { argument := 127374729977398536161086930944, coefficient := (-127374729977398536161086930944) }, { argument := 127287238021417173058420998144, coefficient := (-127287238021417173058420998144) }, { argument := 127374729977398536161086930944, coefficient := (-127374729977398536161086930944) }, { argument := 51337710840034127501552779264, coefficient := (-51337710840034127501552779264) }, { argument := 510266994532697829373762338816, coefficient := (-510266994532697829373762338816) }, { argument := 1754972461088276000919349362688, coefficient := (-1754972461088276000919349362688) }, { argument := 430764719691837896978161729536, coefficient := (-430764719691837896978161729536) }, { argument := 21062783417642816950744645632, coefficient := (-21062783417642816950744645632) }, { argument := 430764266344655541492221214720, coefficient := (-430764266344655541492221214720) }, { argument := 430090261884468232583160791040, coefficient := (-430090261884468232583160791040) }, { argument := 51499297280192126044457664512, coefficient := (-51499297280192126044457664512) }, { argument := 510266994532697829373762338816, coefficient := (-510266994532697829373762338816) }, { argument := 21062783417642816950744645632, coefficient := (-21062783417642816950744645632) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 3415659342860717165195034624, coefficient := (-3415659342860717165195034624) }, { argument := 3810708910985177335546773504, coefficient := (-3810708910985177335546773504) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 3804631225321724102156746752, coefficient := (-3804631225321724102156746752) }, { argument := 3871485767619709669447041024, coefficient := (-3871485767619709669447041024) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-629212216624664284536257443266560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    122265, 39897, 32584334395239, 1648366402812057, 1128400785, 2910086235,
    2434970115, 68119773705, 411970016813301, 2434970115, 2197412055, 1128400785,
    1128400785, 2197412055, 68119773705, 2197412055, 8146037761803, 2910086235,
    1767, 5415, 16017, 35739, 1767, 17841,
    36309, 1767, 5415, 1767, 109710381, 21759390675,
    21759390675, 109710381, 22752557331, 16389218768589, 448815195, 666060182290311,
    142030125, 17043615, 448815195, 891949185, 142030125, 13765559715,
    880586775, 65557028664037, 448815195, 17043615, 880586775, 17043615,
    448815195, 448815195, 22752557331, 7669164831, 30667755039, 15323489187,
    30667755039, 182388148087741, 27661629201, 6234912885269995, 11675901123, 1141815777,
    11675888835, 23315239815, 22870277279179, 27661629201
  ]
def negativeCoefficients : Array ℕ := #[
    4619041104224457376420331520, 188408255567050235090829312, 36686699060128499132987867136, 1855895579368606203769748717568, 20815320493467955905492418560, 26840808004734995772871802880,
    359338164308288923000079646720, 628294015947572247989468528640, 1855348014208199355587987767296, 359338164308288923000079646720, 20267548901534588644821565440, 20815320493467955905492418560,
    20815320493467955905492418560, 20267548901534588644821565440, 628294015947572247989468528640, 20267548901534588644821565440, 36686492628601980054077964288, 26840808004734995772871802880,
    16688843150461326185201664, 409145832075826061314621440, 302552575824492429551075328, 337545311462556500584562688, 16688843150461326185201664, 337006961683509361030201344,
    342928809253027896128176128, 16688843150461326185201664, 409145832075826061314621440, 16688843150461326185201664, 1011899660268083495565262848, 200694955490793565045810790400,
    200694955490793565045810790400, 1011899660268083495565262848, 204936817435234894035812352, 36905239769555479856595075072, 1034897379819630847737200640, 374958548596121157326478508032,
    654998341657994207428608000, 39299900499479652445716480, 1034897379819630847737200640, 1028347396403050905662914560, 654998341657994207428608000, 15870609818373199645995171840,
    1015247429569891021514342400, 36905326232859244800763756544, 1034897379819630847737200640, 39299900499479652445716480, 1015247429569891021514342400, 39299900499479652445716480,
    1034897379819630847737200640, 1034897379819630847737200640, 204936817435234894035812352, 35367780224137741240551604224, 35357514282478093062125912064, 35333560418605580645799297024,
    35357514282478093062125912064, 51337699735296575636657668096, 510266994532697829373762338816, 1754971959174340847539553566720, 430764719691837896978161729536, 21062783417642816950744645632,
    430764266344655541492221214720, 430090261884468232583160791040, 51499286116185232758529851392, 510266994532697829373762338816
  ]
def negativeScales : Array ℕ := #[
    16, 15, 44, 50, 30, 31,
    31, 35, 48, 31, 31, 30,
    30, 31, 35, 31, 42, 31,
    10, 12, 13, 15, 10, 14,
    15, 10, 12, 10, 26, 34,
    34, 26, 34, 43, 28, 49,
    27, 24, 28, 29, 27, 33,
    29, 45, 28, 24, 29, 24,
    28, 28, 34, 32, 34, 33,
    34, 47, 34, 52, 33, 30,
    33, 34, 44, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16899651950892089, 15283992648607578, 44889243762254406, 50549958387171184, 30071632428669329, 31438414759340982,
    31181256919843827, 35987354610566853, 48549532670277464, 31181256919843827, 31033158280854693, 30071632428669329,
    30071632428669329, 31033158280854693, 35987354610566853, 31033158280854693, 42889235644364147, 31438414759340982,
    10787086325046961, 12402745622495697, 13967316348309272, 15125211646966781, 10787086325046961, 14122908861097361,
    15148039576421043, 10787086325046961, 12402745622495697, 10787086325046961, 26709124801872523, 34340919106451587,
    34340919106451587, 26709124801872523, 34405309658642170, 43897812324293023, 28741546279662048, 49242645867234795,
    27081621721072935, 24022728032019366, 28741546279662048, 29732386280342115, 27081621721072935, 33680344220794825,
    29713889936672469, 45897815704302030, 28741546279662048, 24022728032019366, 29713889936672469, 24022728032019366,
    28741546279662048, 28741546279662048, 34405309658642170, 32836422332685836, 34836003511563577, 33835025789185794,
    34836003511563577, 47374005312034386, 34687167079059085, 52469290826049201, 33442814847460808, 30088682755958533,
    33442813329132945, 34440554217845133, 44378539090622050, 34687167079059085
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
noncomputable def negativeCeiling : ℝ := 359627011 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 36686699060128499132987867136, coefficient := (-36686699060128499132987867136) }, { argument := 1855895579368606203769748717568, coefficient := (-1855895579368606203769748717568) }, { argument := 20815320493467955905492418560, coefficient := (-20815320493467955905492418560) }, { argument := 26840808004734995772871802880, coefficient := (-26840808004734995772871802880) }, { argument := 359338164308288923000079646720, coefficient := (-359338164308288923000079646720) }, { argument := 628294015947572247989468528640, coefficient := (-628294015947572247989468528640) }, { argument := 1855348014208199355587987767296, coefficient := (-1855348014208199355587987767296) }, { argument := 359338164308288923000079646720, coefficient := (-359338164308288923000079646720) }, { argument := 20267548901534588644821565440, coefficient := (-20267548901534588644821565440) }, { argument := 20815320493467955905492418560, coefficient := (-20815320493467955905492418560) }, { argument := 20815320493467955905492418560, coefficient := (-20815320493467955905492418560) }, { argument := 20267548901534588644821565440, coefficient := (-20267548901534588644821565440) }, { argument := 628294015947572247989468528640, coefficient := (-628294015947572247989468528640) }, { argument := 20267548901534588644821565440, coefficient := (-20267548901534588644821565440) }, { argument := 36686492628601980054077964288, coefficient := (-36686492628601980054077964288) }, { argument := 26840808004734995772871802880, coefficient := (-26840808004734995772871802880) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 204936817435234894035812352, coefficient := (-204936817435234894035812352) }, { argument := 36905239769555479856595075072, coefficient := (-36905239769555479856595075072) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 374958548596121157326478508032, coefficient := (-374958548596121157326478508032) }, { argument := 654998341657994207428608000, coefficient := (-654998341657994207428608000) }, { argument := 39299900499479652445716480, coefficient := (-39299900499479652445716480) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 1028347396403050905662914560, coefficient := (-1028347396403050905662914560) }, { argument := 654998341657994207428608000, coefficient := (-654998341657994207428608000) }, { argument := 15870609818373199645995171840, coefficient := (-15870609818373199645995171840) }, { argument := 1015247429569891021514342400, coefficient := (-1015247429569891021514342400) }, { argument := 36905326232859244800763756544, coefficient := (-36905326232859244800763756544) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 39299900499479652445716480, coefficient := (-39299900499479652445716480) }, { argument := 1015247429569891021514342400, coefficient := (-1015247429569891021514342400) }, { argument := 39299900499479652445716480, coefficient := (-39299900499479652445716480) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 204936817435234894035812352, coefficient := (-204936817435234894035812352) }, { argument := 35367780224137741240551604224, coefficient := (-35367780224137741240551604224) }, { argument := 35357514282478093062125912064, coefficient := (-35357514282478093062125912064) }, { argument := 35333560418605580645799297024, coefficient := (-35333560418605580645799297024) }, { argument := 35357514282478093062125912064, coefficient := (-35357514282478093062125912064) }, { argument := 51337699735296575636657668096, coefficient := (-51337699735296575636657668096) }, { argument := 510266994532697829373762338816, coefficient := (-510266994532697829373762338816) }, { argument := 1754971959174340847539553566720, coefficient := (-1754971959174340847539553566720) }, { argument := 430764719691837896978161729536, coefficient := (-430764719691837896978161729536) }, { argument := 21062783417642816950744645632, coefficient := (-21062783417642816950744645632) }, { argument := 430764266344655541492221214720, coefficient := (-430764266344655541492221214720) }, { argument := 430090261884468232583160791040, coefficient := (-430090261884468232583160791040) }, { argument := 51499286116185232758529851392, coefficient := (-51499286116185232758529851392) }, { argument := 510266994532697829373762338816, coefficient := (-510266994532697829373762338816) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
