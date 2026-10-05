import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-94702458215110101699150343649099776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2982936225, 70452200958857, 38744818534610811, 1151078896737, 777287839180612923, 44847957295,
    74758830073, 2287224572509, 74741927033, 44847957295, 36638770131199, 2346911093745,
    77489725085305663, 2287224572509, 74758830073, 2346911093745, 74758830073, 2287224572509,
    74742409977, 70452200958857, 6509020771460173, 55391749245, 1016169573382031025, 625135455765,
    55391749245, 15877651861347737, 55391749245, 55391749245, 2296383661557, 14243592663,
    625135455765, 2296383661557, 26036285629096411, 55391749245, 14243592663, 55391749245,
    16947, 254205, 446271, 16947, 141225, 16947,
    446271, 886893, 141225, 13687527, 875595, 254205,
    446271, 16947, 875595, 16947, 446271, 446271,
    16947, 33047719635, 644519500905, 1289038528995, 4130984655, 10602617010045211,
    157815, 4095, 38791084928823341, 254205
  ]
def negativeCoefficients : Array ℕ := #[
    110050922261544583287747379200, 317288505985739686192791683072, 43622787578752683824391666008064, 2654207227094422960140529434624, 437574152861678297614905010814976, 1654597580899040606215932477440,
    86191062850410759751097909248, 2636990395510828648795979382784, 2757490399107248961036438470656, 1654597580899040606215932477440, 42241625986606355261773236404224, 2705804269378986292660005765120,
    43622837127403095031624138489856, 2636990395510828648795979382784, 86191062850410759751097909248, 2705804269378986292660005765120, 86191062850410759751097909248, 2636990395510828648795979382784,
    2757508216595988828207829745664, 317288505985739686192791683072, 14657011760447426763949189627904, 127724677764701160009357066240, 572052614003568851869022080204800, 1441464220487341662962744033280,
    127724677764701160009357066240, 572052696050273044596127921340416, 127724677764701160009357066240, 127724677764701160009357066240, 5295100212473753804959345803264, 131373954272264050295338696704,
    1441464220487341662962744033280, 5295100212473753804959345803264, 14657125782163799575884550111232, 127724677764701160009357066240, 131373954272264050295338696704, 127724677764701160009357066240,
    160059889570383754873012224, 2400898343555756323095183360, 4214910425353438878322655232, 160059889570383754873012224, 2667664826173062581216870400, 160059889570383754873012224,
    4214910425353438878322655232, 4188233777091708252510486528, 2667664826173062581216870400, 64637518738173306342884769792, 4134880480568247000886149120, 2400898343555756323095183360,
    4214910425353438878322655232, 160059889570383754873012224, 4134880480568247000886149120, 160059889570383754873012224, 4214910425353438878322655232, 4214910425353438878322655232,
    160059889570383754873012224, 38101426645409439764195573760, 1486160785463693342434457026560, 1486160240345112141748104069120, 38101608351603173326313226240, 11937485503897923676122501873664,
    1490520532988146118798868480, 77352362989404788600340480, 43674878907686515469570784886784, 2400898343555756323095183360
  ]
def negativeScales : Array ℕ := #[
    31, 46, 55, 40, 59, 35,
    36, 41, 36, 35, 45, 41,
    56, 41, 36, 41, 36, 41,
    36, 46, 52, 35, 59, 39,
    35, 53, 35, 35, 41, 33,
    39, 41, 54, 35, 33, 35,
    14, 17, 18, 14, 17, 14,
    18, 19, 17, 23, 19, 17,
    18, 14, 19, 14, 18, 18,
    14, 34, 39, 40, 31, 53,
    17, 11, 55, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31474085987254608, 46001710011225038, 55104852905378348, 40066123860068352, 59431226558256465, 35384323224598175,
    36121524940895594, 41056735163225645, 36121198709342525, 35384323224598175, 45058436310240230, 41093900329021304,
    56104854544052894, 41056735163225645, 36121524940895594, 41093900329021304, 36121524940895594, 41056735163225645,
    36121208031267855, 46001710011225038, 52531361941445623, 35688952047770669, 59817846880952830, 39185377873834471,
    35688952047770669, 53817847087871502, 35688952047770669, 35688952047770669, 41062500834836750, 33729594032355338,
    39185377873834471, 41062500834836750, 54531373164601312, 35688952047770669, 33729594032355338, 35688952047770669,
    14048742286056541, 17955632893125710, 18767560533841008, 14048742286056541, 17107635975110110, 14048742286056541,
    18767560533841008, 19758400534496915, 17107635975110110, 23706358474870738, 19739904190789689, 17955632893125710,
    18767560533841008, 14048742286056541, 19739904190789689, 14048742286056541, 18767560533841008, 18767560533841008,
    14048742286056541, 34943831684314328, 39229433053912406, 40229432524736811, 31943838564530227, 53235269922743131,
    17267874811582488, 11999647760072134, 55106574644661205, 17955632893125710
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
noncomputable def negativeCeiling : ℝ := 1253012693007 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 110050922261544583287747379200, coefficient := (-110050922261544583287747379200) }, { argument := 317288505985739686192791683072, coefficient := (-317288505985739686192791683072) }, { argument := 43622787578752683824391666008064, coefficient := (-43622787578752683824391666008064) }, { argument := 2654207227094422960140529434624, coefficient := (-2654207227094422960140529434624) }, { argument := 437574152861678297614905010814976, coefficient := (-437574152861678297614905010814976) }, { argument := 1654597580899040606215932477440, coefficient := (-1654597580899040606215932477440) }, { argument := 86191062850410759751097909248, coefficient := (-86191062850410759751097909248) }, { argument := 2636990395510828648795979382784, coefficient := (-2636990395510828648795979382784) }, { argument := 2757490399107248961036438470656, coefficient := (-2757490399107248961036438470656) }, { argument := 1654597580899040606215932477440, coefficient := (-1654597580899040606215932477440) }, { argument := 42241625986606355261773236404224, coefficient := (-42241625986606355261773236404224) }, { argument := 2705804269378986292660005765120, coefficient := (-2705804269378986292660005765120) }, { argument := 43622837127403095031624138489856, coefficient := (-43622837127403095031624138489856) }, { argument := 2636990395510828648795979382784, coefficient := (-2636990395510828648795979382784) }, { argument := 86191062850410759751097909248, coefficient := (-86191062850410759751097909248) }, { argument := 2705804269378986292660005765120, coefficient := (-2705804269378986292660005765120) }, { argument := 86191062850410759751097909248, coefficient := (-86191062850410759751097909248) }, { argument := 2636990395510828648795979382784, coefficient := (-2636990395510828648795979382784) }, { argument := 2757508216595988828207829745664, coefficient := (-2757508216595988828207829745664) }, { argument := 317288505985739686192791683072, coefficient := (-317288505985739686192791683072) }, { argument := 14657011760447426763949189627904, coefficient := (-14657011760447426763949189627904) }, { argument := 127724677764701160009357066240, coefficient := (-127724677764701160009357066240) }, { argument := 572052614003568851869022080204800, coefficient := (-572052614003568851869022080204800) }, { argument := 1441464220487341662962744033280, coefficient := (-1441464220487341662962744033280) }, { argument := 127724677764701160009357066240, coefficient := (-127724677764701160009357066240) }, { argument := 572052696050273044596127921340416, coefficient := (-572052696050273044596127921340416) }, { argument := 127724677764701160009357066240, coefficient := (-127724677764701160009357066240) }, { argument := 127724677764701160009357066240, coefficient := (-127724677764701160009357066240) }, { argument := 5295100212473753804959345803264, coefficient := (-5295100212473753804959345803264) }, { argument := 131373954272264050295338696704, coefficient := (-131373954272264050295338696704) }, { argument := 1441464220487341662962744033280, coefficient := (-1441464220487341662962744033280) }, { argument := 5295100212473753804959345803264, coefficient := (-5295100212473753804959345803264) }, { argument := 14657125782163799575884550111232, coefficient := (-14657125782163799575884550111232) }, { argument := 127724677764701160009357066240, coefficient := (-127724677764701160009357066240) }, { argument := 131373954272264050295338696704, coefficient := (-131373954272264050295338696704) }, { argument := 127724677764701160009357066240, coefficient := (-127724677764701160009357066240) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4188233777091708252510486528, coefficient := (-4188233777091708252510486528) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 64637518738173306342884769792, coefficient := (-64637518738173306342884769792) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 38101426645409439764195573760, coefficient := (-38101426645409439764195573760) }, { argument := 1486160785463693342434457026560, coefficient := (-1486160785463693342434457026560) }, { argument := 1486160240345112141748104069120, coefficient := (-1486160240345112141748104069120) }, { argument := 38101608351603173326313226240, coefficient := (-38101608351603173326313226240) }, { argument := 11937485503897923676122501873664, coefficient := (-11937485503897923676122501873664) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 77352362989404788600340480, coefficient := (-77352362989404788600340480) }, { argument := 43674878907686515469570784886784, coefficient := (-43674878907686515469570784886784) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-102988087515373421531152590905016320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1325319656659415, 254205, 264915, 157815, 7875, 2928278955,
    57109322865, 114218603835, 366036615, 160441229851, 277053, 7189,
    577615004351, 446271, 80221207955, 446271, 465073, 277053,
    13825, 278925317504931, 278925301776477, 4822360018783, 5294907238935645, 159865386765,
    212380815394944525, 6228538435, 10381181125, 317654967385, 10380789125, 6228538435,
    5088669264595, 325957116765, 21179653507068095, 317654967385, 10381181125, 325957116765,
    10381181125, 317654967385, 10380800325, 4822360018783, 13018043370360485, 110783457855,
    508084859617400891, 1250270452935, 110783457855, 508084932489550101, 110783457855, 110783457855,
    4592765638503, 28487174877, 1250270452935, 4592765638503, 13018144642025483, 110783457855,
    28487174877, 110783457855, 106305172348304285, 10521, 273, 194530018477285321,
    16947, 106304920259019985, 16947, 17661
  ]
def negativeCoefficients : Array ℕ := #[
    11937418223756270183103783239680, 2400898343555756323095183360, 2502051433618824123572551680, 1490520532988146118798868480, 74377272105196912115712000, 3376075778707165548726190080,
    131685132889188017684065812480, 131685084587541582180211752960, 3376091879255977383344209920, 739904576483151564259201122304, 2616691602356967630780235776, 135796370581399517765042176,
    2663779039599381530346524770304, 4214910425353438878322655232, 739910046214858894228471152640, 4214910425353438878322655232, 4392490294575269016938479616, 2616691602356967630780235776,
    130573433251345690158694400, 157020994497425567086880489472, 157020985643093120397632077824, 86871915134549987565840105472, 11923071134115956325700557864960, 737248968974637284341642690560,
    119559770134164282882032192716800, 459585017854833661067489443840, 23937373924462400746029056000, 732462485886706206817931755520, 765967041088089247295995904000, 459585017854833661067489443840,
    11733672449966969811927239229440, 751605938996027010349038305280, 11923084955283511426419408240640, 732462485886706206817931755520, 23937373924462400746029056000, 751605938996027010349038305280,
    23937373924462400746029056000, 732462485886706206817931755520, 765967867502223749483908300800, 86871915134549987565840105472, 14657013817962109024521043312640, 127724630915735820310130196480,
    572052696111379355891469054377984, 1441463691763304257785755074560, 127724630915735820310130196480, 572052778158125362852265170305024, 127724630915735820310130196480, 127724630915735820310130196480,
    5295098270249505007714254716928, 131373906084756843747562487808, 1441463691763304257785755074560, 5295098270249505007714254716928, 14657127839720296070146678587392, 127724630915735820310130196480,
    131373906084756843747562487808, 127724630915735820310130196480, 119688983643844883285714759843840, 99368035532543074586591232, 5156824199293652573356032, 438042659363338936676967784644608,
    160059889570383754873012224, 119688699816543173891957865840640, 160059889570383754873012224, 166803428907921608238170112
  ]
def negativeScales : Array ℕ := #[
    50, 17, 18, 17, 12, 31,
    35, 36, 28, 37, 18, 12,
    39, 18, 36, 18, 18, 18,
    13, 47, 47, 42, 52, 37,
    57, 32, 33, 38, 33, 32,
    42, 38, 54, 38, 33, 38,
    33, 38, 33, 42, 53, 36,
    58, 40, 36, 58, 36, 36,
    42, 34, 40, 42, 53, 36,
    34, 36, 56, 13, 8, 57,
    14, 56, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    50235261791633760, 17955632893125710, 18015170008642424, 17267874811582488, 12943064217429565, 31447405848805486,
    35733007227947319, 36733006698771722, 28447412729020287, 37223253973946130, 18079802463429916, 12811575389192290,
    39071317262477804, 18767560533841008, 36223264639004697, 18767560533841008, 18827097661601281, 18079802463429916,
    13754991860260137, 47986872238511831, 47986872157158978, 42132876499651890, 52233526833288242, 37218066651446811,
    57559431064800512, 32536246519651303, 33273251545386326, 38208669623471614, 33273197067275696, 32536246519651303,
    42210425565798718, 38245891218340152, 54233528505652528, 38208669623471614, 33273251545386326, 38245891218340152,
    33273251545386326, 38208669623471614, 33273198623821691, 42132876499651890, 53531362143967533, 36688951518595073,
    58817847088025610, 40185377344658876, 36688951518595073, 58817847294944357, 36688951518595073, 36688951518595073,
    42062500305661155, 34729593503179741, 40185377344658876, 42062500305661155, 53531373367125763, 36688951518595073,
    34729593503179741, 36688951518595073, 56560989406942934, 13360984215973970, 8092757140919853, 57432770411827195,
    14048742286056541, 56560985985769876, 14048742286056541, 14108279413033905
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
noncomputable def negativeCeiling : ℝ := 35463706371 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11937418223756270183103783239680, coefficient := (-11937418223756270183103783239680) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }, { argument := 2502051433618824123572551680, coefficient := (-2502051433618824123572551680) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 74377272105196912115712000, coefficient := (-74377272105196912115712000) }, { argument := 3376075778707165548726190080, coefficient := (-3376075778707165548726190080) }, { argument := 131685132889188017684065812480, coefficient := (-131685132889188017684065812480) }, { argument := 131685084587541582180211752960, coefficient := (-131685084587541582180211752960) }, { argument := 3376091879255977383344209920, coefficient := (-3376091879255977383344209920) }, { argument := 739904576483151564259201122304, coefficient := (-739904576483151564259201122304) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 2663779039599381530346524770304, coefficient := (-2663779039599381530346524770304) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 739910046214858894228471152640, coefficient := (-739910046214858894228471152640) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 157020994497425567086880489472, coefficient := (-157020994497425567086880489472) }, { argument := 157020985643093120397632077824, coefficient := (-157020985643093120397632077824) }, { argument := 86871915134549987565840105472, coefficient := (-86871915134549987565840105472) }, { argument := 11923071134115956325700557864960, coefficient := (-11923071134115956325700557864960) }, { argument := 737248968974637284341642690560, coefficient := (-737248968974637284341642690560) }, { argument := 119559770134164282882032192716800, coefficient := (-119559770134164282882032192716800) }, { argument := 459585017854833661067489443840, coefficient := (-459585017854833661067489443840) }, { argument := 23937373924462400746029056000, coefficient := (-23937373924462400746029056000) }, { argument := 732462485886706206817931755520, coefficient := (-732462485886706206817931755520) }, { argument := 765967041088089247295995904000, coefficient := (-765967041088089247295995904000) }, { argument := 459585017854833661067489443840, coefficient := (-459585017854833661067489443840) }, { argument := 11733672449966969811927239229440, coefficient := (-11733672449966969811927239229440) }, { argument := 751605938996027010349038305280, coefficient := (-751605938996027010349038305280) }, { argument := 11923084955283511426419408240640, coefficient := (-11923084955283511426419408240640) }, { argument := 732462485886706206817931755520, coefficient := (-732462485886706206817931755520) }, { argument := 23937373924462400746029056000, coefficient := (-23937373924462400746029056000) }, { argument := 751605938996027010349038305280, coefficient := (-751605938996027010349038305280) }, { argument := 23937373924462400746029056000, coefficient := (-23937373924462400746029056000) }, { argument := 732462485886706206817931755520, coefficient := (-732462485886706206817931755520) }, { argument := 765967867502223749483908300800, coefficient := (-765967867502223749483908300800) }, { argument := 86871915134549987565840105472, coefficient := (-86871915134549987565840105472) }, { argument := 14657013817962109024521043312640, coefficient := (-14657013817962109024521043312640) }, { argument := 127724630915735820310130196480, coefficient := (-127724630915735820310130196480) }, { argument := 572052696111379355891469054377984, coefficient := (-572052696111379355891469054377984) }, { argument := 1441463691763304257785755074560, coefficient := (-1441463691763304257785755074560) }, { argument := 127724630915735820310130196480, coefficient := (-127724630915735820310130196480) }, { argument := 572052778158125362852265170305024, coefficient := (-572052778158125362852265170305024) }, { argument := 127724630915735820310130196480, coefficient := (-127724630915735820310130196480) }, { argument := 127724630915735820310130196480, coefficient := (-127724630915735820310130196480) }, { argument := 5295098270249505007714254716928, coefficient := (-5295098270249505007714254716928) }, { argument := 131373906084756843747562487808, coefficient := (-131373906084756843747562487808) }, { argument := 1441463691763304257785755074560, coefficient := (-1441463691763304257785755074560) }, { argument := 5295098270249505007714254716928, coefficient := (-5295098270249505007714254716928) }, { argument := 14657127839720296070146678587392, coefficient := (-14657127839720296070146678587392) }, { argument := 127724630915735820310130196480, coefficient := (-127724630915735820310130196480) }, { argument := 131373906084756843747562487808, coefficient := (-131373906084756843747562487808) }, { argument := 127724630915735820310130196480, coefficient := (-127724630915735820310130196480) }, { argument := 119688983643844883285714759843840, coefficient := (-119688983643844883285714759843840) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 438042659363338936676967784644608, coefficient := (-438042659363338936676967784644608) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 119688699816543173891957865840640, coefficient := (-119688699816543173891957865840640) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
