import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-47778264874411341899597539704832)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    70707, 1335789, 70707, 819819, 1335789, 4969965753,
    70707, 70707, 78351, 958367089, 110479967169, 30667755039,
    45099943737, 4940635879623, 1751515, 4517065, 3779585, 105736195,
    1235064669419, 3779585, 3410845, 1751515, 1751515, 3410845,
    105736195, 3410845, 11274888981, 4517065, 5688090567, 4097281636953,
    448815195, 166514170415787, 142030125, 17043615, 448815195, 891949185,
    142030125, 13765559715, 880586775, 16389164945169, 448815195, 17043615,
    880586775, 17043615, 448815195, 448815195, 5688090567, 576990400381,
    3813, 11134742857095, 39897, 1767, 22269481024365, 1767,
    3441, 65007, 3441, 39897, 65007, 72123995457,
    3441, 3441, 3813, 1135575
  ]
def negativeCoefficients : Array ℕ := #[
    333904366904264004124803072, 12616170403571921020715532288, 333904366904264004124803072, 3871485767619709669447041024, 12616170403571921020715532288, 11459960787586522400063225856,
    333904366904264004124803072, 333904366904264004124803072, 370002136299319572138295296, 35357504838898048827442331648, 127374729977398536161086930944, 35357514282478093062125912064,
    203112089808383534853783552, 22250645906443445531477803008, 64619497892526770597396480, 83325142019310835770327040, 1115536595197304250312949760, 1950488528492847523031941120,
    22248947139895492905896247296, 1115536595197304250312949760, 62918984790091855581675520, 64619497892526770597396480, 64619497892526770597396480, 62918984790091855581675520,
    1950488528492847523031941120, 62918984790091855581675520, 203110343253901245419618304, 83325142019310835770327040, 204935060463926666493689856, 36905032106827013347791077376,
    1034897379819630847737200640, 374956577918222801096908210176, 654998341657994207428608000, 39299900499479652445716480, 1034897379819630847737200640, 1028347396403050905662914560,
    654998341657994207428608000, 15870609818373199645995171840, 1015247429569891021514342400, 36905118569988351953744166912, 1034897379819630847737200640, 39299900499479652445716480,
    1015247429569891021514342400, 39299900499479652445716480, 1034897379819630847737200640, 1034897379819630847737200640, 204935060463926666493689856, 1299266876076112446633279488,
    18006383399181957199822848, 50146423782079333993147269120, 188408255567050235090829312, 16688843150461326185201664, 50146413221532272776729067520, 16688843150461326185201664,
    16249663067554449180327936, 613973755903814052813471744, 16249663067554449180327936, 188408255567050235090829312, 613973755903814052813471744, 1299270396258466185439346688,
    16249663067554449180327936, 16249663067554449180327936, 18006383399181957199822848, 83790645606010896305356800
  ]
def negativeScales : Array ℕ := #[
    16, 20, 16, 19, 20, 32,
    16, 16, 16, 29, 36, 34,
    35, 42, 20, 22, 21, 26,
    40, 21, 21, 20, 20, 21,
    26, 21, 33, 22, 32, 41,
    28, 47, 27, 24, 28, 29,
    27, 33, 29, 43, 28, 24,
    29, 24, 28, 28, 32, 39,
    11, 43, 15, 10, 44, 10,
    11, 15, 11, 15, 15, 36,
    11, 11, 11, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16109565428606407, 20349260708352894, 16109565428606407, 19644945900495728, 20349260708352894, 32210588764496701,
    16109565428606407, 16109565428606407, 16257664067595541, 29836003126236481, 36684993839798950, 34836003511563577,
    35392406582567107, 42167833873037433, 20740171912959561, 22106954243450046, 21849796405678326, 26655894075375398,
    40167723723622224, 21849796405678326, 21701697765039121, 20740171912959561, 20740171912959561, 21701697765039121,
    26655894075375398, 21701697765039121, 33392394176824415, 22106954243450046, 32405297290026854, 41897804206344029,
    28741546279662048, 47242638284810783, 27081621721072935, 24022728032019366, 28741546279662048, 29732386280342115,
    27081621721072935, 33680344220794825, 29713889936672469, 43897807586366488, 28741546279662048, 24022728032019366,
    29713889936672469, 24022728032019366, 28741546279662048, 28741546279662048, 32405297290026854, 39069756360139658,
    11896710819843133, 43340133474815662, 15283992648607578, 10787086325046961, 44340133170992391, 10787086325046961,
    11748612176955137, 15988307476108722, 11748612176955137, 15283992648607578, 15988307476108722, 36069760268915321,
    11748612176955137, 11748612176955137, 11896710819843133, 20114991562515464
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
noncomputable def negativeCeiling : ℝ := 3402831 / 7812500000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 12616170403571921020715532288, coefficient := (-12616170403571921020715532288) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 3871485767619709669447041024, coefficient := (-3871485767619709669447041024) }, { argument := 12616170403571921020715532288, coefficient := (-12616170403571921020715532288) }, { argument := 11459960787586522400063225856, coefficient := (-11459960787586522400063225856) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 370002136299319572138295296, coefficient := (-370002136299319572138295296) }, { argument := 35357504838898048827442331648, coefficient := (-35357504838898048827442331648) }, { argument := 127374729977398536161086930944, coefficient := (-127374729977398536161086930944) }, { argument := 35357514282478093062125912064, coefficient := (-35357514282478093062125912064) }, { argument := 203112089808383534853783552, coefficient := (-203112089808383534853783552) }, { argument := 22250645906443445531477803008, coefficient := (-22250645906443445531477803008) }, { argument := 64619497892526770597396480, coefficient := (-64619497892526770597396480) }, { argument := 83325142019310835770327040, coefficient := (-83325142019310835770327040) }, { argument := 1115536595197304250312949760, coefficient := (-1115536595197304250312949760) }, { argument := 1950488528492847523031941120, coefficient := (-1950488528492847523031941120) }, { argument := 22248947139895492905896247296, coefficient := (-22248947139895492905896247296) }, { argument := 1115536595197304250312949760, coefficient := (-1115536595197304250312949760) }, { argument := 62918984790091855581675520, coefficient := (-62918984790091855581675520) }, { argument := 64619497892526770597396480, coefficient := (-64619497892526770597396480) }, { argument := 64619497892526770597396480, coefficient := (-64619497892526770597396480) }, { argument := 62918984790091855581675520, coefficient := (-62918984790091855581675520) }, { argument := 1950488528492847523031941120, coefficient := (-1950488528492847523031941120) }, { argument := 62918984790091855581675520, coefficient := (-62918984790091855581675520) }, { argument := 203110343253901245419618304, coefficient := (-203110343253901245419618304) }, { argument := 83325142019310835770327040, coefficient := (-83325142019310835770327040) }, { argument := 204935060463926666493689856, coefficient := (-204935060463926666493689856) }, { argument := 36905032106827013347791077376, coefficient := (-36905032106827013347791077376) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 374956577918222801096908210176, coefficient := (-374956577918222801096908210176) }, { argument := 654998341657994207428608000, coefficient := (-654998341657994207428608000) }, { argument := 39299900499479652445716480, coefficient := (-39299900499479652445716480) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 1028347396403050905662914560, coefficient := (-1028347396403050905662914560) }, { argument := 654998341657994207428608000, coefficient := (-654998341657994207428608000) }, { argument := 15870609818373199645995171840, coefficient := (-15870609818373199645995171840) }, { argument := 1015247429569891021514342400, coefficient := (-1015247429569891021514342400) }, { argument := 36905118569988351953744166912, coefficient := (-36905118569988351953744166912) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 39299900499479652445716480, coefficient := (-39299900499479652445716480) }, { argument := 1015247429569891021514342400, coefficient := (-1015247429569891021514342400) }, { argument := 39299900499479652445716480, coefficient := (-39299900499479652445716480) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 1034897379819630847737200640, coefficient := (-1034897379819630847737200640) }, { argument := 204935060463926666493689856, coefficient := (-204935060463926666493689856) }, { argument := 1299266876076112446633279488, coefficient := (-1299266876076112446633279488) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 50146423782079333993147269120, coefficient := (-50146423782079333993147269120) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 50146413221532272776729067520, coefficient := (-50146413221532272776729067520) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 1299270396258466185439346688, coefficient := (-1299270396258466185439346688) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 83790645606010896305356800, coefficient := (-83790645606010896305356800) }] }

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


end Parent0

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 16933645132023402923503753508159488
def positiveArguments : Array ℕ := #[
    2239, 93, 285, 843, 1881, 93,
    939, 1911, 93, 285, 93, 257,
    1025, 509, 1025, 1, 9
  ]
def positiveCoefficients : Array ℕ := #[
    177391855869437851871944904802304, 3597763239173136423925579776, 88203227799083344586562600960, 65223965819848473233747607552, 72767662934243759283914145792, 3597763239173136423925579776,
    72651606055560754883142352896, 73928231721073803291632074752, 3597763239173136423925579776, 88203227799083344586562600960, 3597763239173136423925579776, 39768823762042841331134365696,
    39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 158456325028528675187087900672, 356526731314189519170947776512
  ]
def positiveScales : Array ℕ := #[
    11, 6, 8, 9, 10, 6,
    9, 10, 6, 8, 6, 8,
    10, 8, 10, 0, 3
  ]
def negativeArguments : Array ℕ := #[
    731585925, 7780723965, 365794065, 1135575, 5897377455, 11685,
    224364472657, 122265, 5415, 224364472657, 5415, 10545,
    199215, 10545, 122265, 199215, 5897377455, 10545,
    10545, 11685, 478858909, 55202039997, 15323489187, 243351519,
    3813, 9261309985, 39897, 1767, 9261309985, 1767,
    3441, 65007, 3441, 39897, 65007, 243351519,
    3441, 3441, 3813, 958367089, 110479967169, 30667755039,
    8388607, 8388609, 3, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    26990756652806141000653209600, 287058047381067269416031354880, 26990838002947506059775836160, 83790645606010896305356800, 13598426577306195989794652160, 441446818818654434576302080,
    517349250792060435763470270464, 4619041104224457376420331520, 409145832075826061314621440, 517349250792060435763470270464, 409145832075826061314621440, 398378836494883270227394560,
    15052259822158021939943178240, 398378836494883270227394560, 4619041104224457376420331520, 15052259822158021939943178240, 13598426577306195989794652160, 398378836494883270227394560,
    398378836494883270227394560, 441446818818654434576302080, 35333550966955085878867787776, 127287238021417173058420998144, 35333560418605580645799297024, 561130398867683418820313088,
    18006383399181957199822848, 21355126885073230796391710720, 188408255567050235090829312, 16688843150461326185201664, 21355126885073230796391710720, 16688843150461326185201664,
    16249663067554449180327936, 613973755903814052813471744, 16249663067554449180327936, 188408255567050235090829312, 613973755903814052813471744, 561130398867683418820313088,
    16249663067554449180327936, 16249663067554449180327936, 18006383399181957199822848, 35357504838898048827442331648, 127374729977398536161086930944, 35357514282478093062125912064,
    39614076534765685927126761472, 39614085979498651666417188864, 475368975085586025561263702016, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    29, 32, 28, 20, 32, 13,
    37, 16, 12, 37, 12, 13,
    17, 13, 16, 17, 32, 13,
    13, 13, 28, 35, 33, 27,
    11, 33, 15, 10, 33, 10,
    11, 15, 11, 15, 15, 27,
    11, 11, 11, 29, 36, 34,
    22, 23, 1, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11128638812852597, 6539158811107971, 8154818109052103, 9719388820935039, 10877284133344468, 6539158811107971,
    9874981347482478, 10900112062706946, 6539158811107971, 8154818109052103, 6539158811107971, 8005624549193878,
    10001408194392808, 8991521844801183, 10001408194392808, 0, 3169925001442312
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29446452078406411, 32857257254389320, 28446456426682755, 20114991562515464, 32457426389172021, 13512370113670596,
    37707053292077454, 16899651950892089, 12402745622495697, 37707053292077454, 12402745622495697, 13364271474681056,
    17603966754433849, 13364271474681056, 16899651950892089, 17603966754433849, 32457426389172021, 13364271474681056,
    13364271474681056, 13512370113670596, 28835025403267950, 35684002531853580, 33835025789185794, 27858466541078951,
    11896710819843133, 33108569126866570, 15283992648607578, 10787086325046961, 33108569126866570, 10787086325046961,
    11748612176955137, 15988307476108722, 11748612176955137, 15283992648607578, 15988307476108722, 27858466541078951,
    11748612176955137, 11748612176955137, 11896710819843133, 29836003126236481, 36684993839798950, 34836003511563577,
    22999999851693669, 23000000171982641, 1584962500724866, 0, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 47
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
noncomputable def positiveFloor : ℝ := 23847912749 / 1000000000000
noncomputable def negativeCeiling : ℝ := 835223543 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 26990756652806141000653209600, coefficient := (-26990756652806141000653209600) }, { argument := 287058047381067269416031354880, coefficient := (-287058047381067269416031354880) }, { argument := 26990838002947506059775836160, coefficient := (-26990838002947506059775836160) }, { argument := 83790645606010896305356800, coefficient := (-83790645606010896305356800) }, { argument := 13598426577306195989794652160, coefficient := (-13598426577306195989794652160) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 517349250792060435763470270464, coefficient := (-517349250792060435763470270464) }, { argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 517349250792060435763470270464, coefficient := (-517349250792060435763470270464) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 13598426577306195989794652160, coefficient := (-13598426577306195989794652160) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 35333550966955085878867787776, coefficient := (-35333550966955085878867787776) }, { argument := 127287238021417173058420998144, coefficient := (-127287238021417173058420998144) }, { argument := 35333560418605580645799297024, coefficient := (-35333560418605580645799297024) }, { argument := 561130398867683418820313088, coefficient := (-561130398867683418820313088) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 21355126885073230796391710720, coefficient := (-21355126885073230796391710720) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 21355126885073230796391710720, coefficient := (-21355126885073230796391710720) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 561130398867683418820313088, coefficient := (-561130398867683418820313088) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 35357504838898048827442331648, coefficient := (-35357504838898048827442331648) }, { argument := 127374729977398536161086930944, coefficient := (-127374729977398536161086930944) }, { argument := 35357514282478093062125912064, coefficient := (-35357514282478093062125912064) }, { argument := 39614076534765685927126761472, coefficient := (-39614076534765685927126761472) }, { argument := 39614085979498651666417188864, coefficient := (-39614085979498651666417188864) }, { argument := 177391855869437851871944904802304, coefficient := 177391855869437851871944904802304 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 356526731314189519170947776512, coefficient := 356526731314189519170947776512 }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
