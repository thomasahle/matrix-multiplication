import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1161629261684253333869443038576640)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10521, 525, 2928278955, 57109322865, 114218603835, 366036615,
    6250973205, 87675, 2275, 22504844465, 141225, 3125510045,
    141225, 147175, 87675, 4375, 16735258445922397, 16735263985975203,
    10418561059, 10521, 273, 37514191399, 16947, 5209325275,
    16947, 17661, 10521, 525, 18551408775, 18551404409,
    1828125, 16947, 254205, 446271, 16947, 141225,
    16947, 446271, 886893, 141225, 13687527, 875595,
    254205, 446271, 16947, 875595, 16947, 446271,
    446271, 16947, 2928278955, 57109322865, 114218603835, 366036615,
    17661, 264915, 465073, 17661, 147175, 17661,
    465073, 924259, 147175, 14264201
  ]
def negativeCoefficients : Array ℕ := #[
    99368035532543074586591232, 4958484807013127474380800, 3376075778707165548726190080, 131685132889188017684065812480, 131685084587541582180211752960, 3376091879255977383344209920,
    461240411697003808416721797120, 1656133925542384576443187200, 85947069988227542889267200, 1660564425057975818811877621760, 2667664826173062581216870400, 461243871199387391906031861760,
    2667664826173062581216870400, 2780057148465360137302835200, 1656133925542384576443187200, 82641413450218791239680000, 9421112962625631639165797924864, 9421116081398100728474643726336,
    24023566183961170017851015168, 99368035532543074586591232, 5156824199293652573356032, 86501835983688635407136718848, 160059889570383754873012224, 24023772536157907560536473600,
    160059889570383754873012224, 166803428907921608238170112, 99368035532543074586591232, 4958484807013127474380800, 85553272469798655662594457600, 85553252335177499208618868736,
    8633076226496070156288000000, 160059889570383754873012224, 2400898343555756323095183360, 4214910425353438878322655232, 160059889570383754873012224, 2667664826173062581216870400,
    160059889570383754873012224, 4214910425353438878322655232, 4188233777091708252510486528, 2667664826173062581216870400, 64637518738173306342884769792, 4134880480568247000886149120,
    2400898343555756323095183360, 4214910425353438878322655232, 160059889570383754873012224, 4134880480568247000886149120, 160059889570383754873012224, 4214910425353438878322655232,
    4214910425353438878322655232, 160059889570383754873012224, 3376075778707165548726190080, 131685132889188017684065812480, 131685084587541582180211752960, 3376091879255977383344209920,
    166803428907921608238170112, 2502051433618824123572551680, 4392490294575269016938479616, 166803428907921608238170112, 2780057148465360137302835200, 166803428907921608238170112,
    4392490294575269016938479616, 4364689723090615415565451264, 2780057148465360137302835200, 67360784707315676126847696896
  ]
def negativeScales : Array ℕ := #[
    13, 9, 31, 35, 36, 28,
    32, 16, 11, 34, 17, 31,
    17, 17, 16, 12, 53, 53,
    33, 13, 8, 35, 14, 32,
    14, 14, 13, 9, 34, 34,
    20, 14, 17, 18, 14, 17,
    14, 18, 19, 17, 23, 19,
    17, 18, 14, 19, 14, 18,
    18, 14, 31, 35, 36, 28,
    14, 18, 18, 14, 17, 14,
    18, 19, 17, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13360984215973970, 9036173612553486, 31447405848805486, 35733007227947319, 36733006698771722, 28447412729020287,
    32541433672358053, 16419877905027552, 11151650829973422, 34389516542908420, 17107635975110110, 31541444493153649,
    17107635975110110, 17167173102087474, 16419877905027552, 12095067301607054, 53893740353122819, 53893740830713647,
    33278436984993259, 13360984215973970, 8092757140919853, 35126717410826177, 14048742286056541, 32278449377075686,
    14048742286056541, 14108279413033905, 13360984215973970, 9036173612553486, 34110809696664923, 34110809357132365,
    20801933289579550, 14048742286056541, 17955632893125710, 18767560533841008, 14048742286056541, 17107635975110110,
    14048742286056541, 18767560533841008, 19758400534496915, 17107635975110110, 23706358474870738, 19739904190789689,
    17955632893125710, 18767560533841008, 14048742286056541, 19739904190789689, 14048742286056541, 18767560533841008,
    18767560533841008, 14048742286056541, 31447405848805486, 35733007227947319, 36733006698771722, 28447412729020287,
    14108279413033905, 18015170008642424, 18827097661601281, 14108279413033905, 17167173102087474, 14108279413033905,
    18827097661601281, 19817937662131590, 17167173102087474, 23765895602081147
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
noncomputable def negativeCeiling : ℝ := 1710515967 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 3376075778707165548726190080, coefficient := (-3376075778707165548726190080) }, { argument := 131685132889188017684065812480, coefficient := (-131685132889188017684065812480) }, { argument := 131685084587541582180211752960, coefficient := (-131685084587541582180211752960) }, { argument := 3376091879255977383344209920, coefficient := (-3376091879255977383344209920) }, { argument := 461240411697003808416721797120, coefficient := (-461240411697003808416721797120) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }, { argument := 85947069988227542889267200, coefficient := (-85947069988227542889267200) }, { argument := 1660564425057975818811877621760, coefficient := (-1660564425057975818811877621760) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 461243871199387391906031861760, coefficient := (-461243871199387391906031861760) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 2780057148465360137302835200, coefficient := (-2780057148465360137302835200) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }, { argument := 82641413450218791239680000, coefficient := (-82641413450218791239680000) }, { argument := 9421112962625631639165797924864, coefficient := (-9421112962625631639165797924864) }, { argument := 9421116081398100728474643726336, coefficient := (-9421116081398100728474643726336) }, { argument := 24023566183961170017851015168, coefficient := (-24023566183961170017851015168) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 5156824199293652573356032, coefficient := (-5156824199293652573356032) }, { argument := 86501835983688635407136718848, coefficient := (-86501835983688635407136718848) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 24023772536157907560536473600, coefficient := (-24023772536157907560536473600) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 85553272469798655662594457600, coefficient := (-85553272469798655662594457600) }, { argument := 85553252335177499208618868736, coefficient := (-85553252335177499208618868736) }, { argument := 8633076226496070156288000000, coefficient := (-8633076226496070156288000000) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4188233777091708252510486528, coefficient := (-4188233777091708252510486528) }, { argument := 2667664826173062581216870400, coefficient := (-2667664826173062581216870400) }, { argument := 64637518738173306342884769792, coefficient := (-64637518738173306342884769792) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 2400898343555756323095183360, coefficient := (-2400898343555756323095183360) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 4134880480568247000886149120, coefficient := (-4134880480568247000886149120) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 160059889570383754873012224, coefficient := (-160059889570383754873012224) }, { argument := 3376075778707165548726190080, coefficient := (-3376075778707165548726190080) }, { argument := 131685132889188017684065812480, coefficient := (-131685132889188017684065812480) }, { argument := 131685084587541582180211752960, coefficient := (-131685084587541582180211752960) }, { argument := 3376091879255977383344209920, coefficient := (-3376091879255977383344209920) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 2502051433618824123572551680, coefficient := (-2502051433618824123572551680) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 2780057148465360137302835200, coefficient := (-2780057148465360137302835200) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 4364689723090615415565451264, coefficient := (-4364689723090615415565451264) }, { argument := 2780057148465360137302835200, coefficient := (-2780057148465360137302835200) }, { argument := 67360784707315676126847696896, coefficient := (-67360784707315676126847696896) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1470990501526054486751437517750272)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    912485, 264915, 465073, 17661, 912485, 17661,
    465073, 465073, 17661, 121398078963, 2367589356489, 4735176976131,
    15174832239, 318799160367, 277053, 7189, 1147736442947, 446271,
    159400765895, 446271, 465073, 277053, 13825, 752986017,
    14685254451, 29370498129, 94123701, 10418184739, 550599, 14287,
    37505739879, 886893, 5209129275, 886893, 924259, 550599,
    27475, 1504051377, 1504051023, 10521, 157815, 277053,
    10521, 87675, 10521, 277053, 550599, 87675,
    8497461, 543585, 157815, 277053, 10521, 543585,
    10521, 277053, 277053, 10521, 33047719635, 644519500905,
    1289038528995, 4130984655, 6250973205, 87675
  ]
def negativeCoefficients : Array ℕ := #[
    4309088580121308212819394560, 2502051433618824123572551680, 4392490294575269016938479616, 166803428907921608238170112, 4309088580121308212819394560, 166803428907921608238170112,
    4392490294575269016938479616, 4392490294575269016938479616, 166803428907921608238170112, 139962455854402777462905765888, 5459289366348908961702271254528, 5459287363900652449813921529856,
    139963123337154948092355674112, 735100815275442276776106000384, 2616691602356967630780235776, 135796370581399517765042176, 2646500053389131643870766956544, 4214910425353438878322655232,
    735106283404588715341858734080, 4214910425353438878322655232, 4392490294575269016938479616, 2616691602356967630780235776, 130573433251345690158694400, 3472535086670227421546938368,
    135447565257450532475039121408, 135447515575757055956789231616, 3472551647234719594296901632, 768726350371838167057375952896, 2600130263101543785015803904, 134936899881517242336149504,
    2767435139372140982029680377856, 4188233777091708252510486528, 768731796662345465360233267200, 4188233777091708252510486528, 4364689723090615415565451264, 2600130263101543785015803904,
    129747019116843502246297600, 110979403300917762424389500928, 110979377180328154051664412672, 99368035532543074586591232, 1490520532988146118798868480, 2616691602356967630780235776,
    99368035532543074586591232, 1656133925542384576443187200, 99368035532543074586591232, 2616691602356967630780235776, 2600130263101543785015803904, 1656133925542384576443187200,
    40128125015891978287218425856, 2567007584590696093486940160, 1490520532988146118798868480, 2616691602356967630780235776, 99368035532543074586591232, 2567007584590696093486940160,
    99368035532543074586591232, 2616691602356967630780235776, 2616691602356967630780235776, 99368035532543074586591232, 38101426645409439764195573760, 1486160785463693342434457026560,
    1486160240345112141748104069120, 38101608351603173326313226240, 461240411697003808416721797120, 1656133925542384576443187200
  ]
def negativeScales : Array ℕ := #[
    19, 18, 18, 14, 19, 14,
    18, 18, 14, 36, 41, 42,
    33, 38, 18, 12, 40, 18,
    37, 18, 18, 18, 13, 29,
    33, 34, 26, 33, 19, 13,
    35, 19, 32, 19, 19, 19,
    14, 30, 30, 13, 17, 18,
    13, 16, 13, 18, 19, 16,
    23, 19, 17, 18, 13, 19,
    13, 18, 18, 13, 34, 39,
    40, 31, 32, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19799441318225700, 18015170008642424, 18827097661601281, 14108279413033905, 19799441318225700, 14108279413033905,
    18827097661601281, 18827097661601281, 14108279413033905, 36820954636911702, 41106556014914685, 42106555485739090,
    33820961517126636, 38213856873415719, 18079802463429916, 12811575389192290, 40061928529697848, 18767560533841008,
    37213867605023272, 18767560533841008, 18827097661601281, 18079802463429916, 13754991860260137, 29488047833302971,
    33773649212664100, 34773648683488501, 26488054713517771, 33278384873689209, 19070642464144440, 13802415389768912,
    35126392351449666, 19758400534496915, 32278395094892721, 19758400534496915, 19817937662131590, 19070642464144440,
    14745831860929201, 30486206702968167, 30486206363409219, 13360984215973970, 17267874811582488, 18079802463429916,
    13360984215973970, 16419877905027552, 13360984215973970, 18079802463429916, 19070642464144440, 16419877905027552,
    23018600404704159, 19052146120527051, 17267874811582488, 18079802463429916, 13360984215973970, 19052146120527051,
    13360984215973970, 18079802463429916, 18079802463429916, 13360984215973970, 34943831684314328, 39229433053912406,
    40229432524736811, 31943838564530227, 32541433672358053, 16419877905027552
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
noncomputable def negativeCeiling : ℝ := 5583715307 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4309088580121308212819394560, coefficient := (-4309088580121308212819394560) }, { argument := 2502051433618824123572551680, coefficient := (-2502051433618824123572551680) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 4309088580121308212819394560, coefficient := (-4309088580121308212819394560) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 166803428907921608238170112, coefficient := (-166803428907921608238170112) }, { argument := 139962455854402777462905765888, coefficient := (-139962455854402777462905765888) }, { argument := 5459289366348908961702271254528, coefficient := (-5459289366348908961702271254528) }, { argument := 5459287363900652449813921529856, coefficient := (-5459287363900652449813921529856) }, { argument := 139963123337154948092355674112, coefficient := (-139963123337154948092355674112) }, { argument := 735100815275442276776106000384, coefficient := (-735100815275442276776106000384) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 135796370581399517765042176, coefficient := (-135796370581399517765042176) }, { argument := 2646500053389131643870766956544, coefficient := (-2646500053389131643870766956544) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 735106283404588715341858734080, coefficient := (-735106283404588715341858734080) }, { argument := 4214910425353438878322655232, coefficient := (-4214910425353438878322655232) }, { argument := 4392490294575269016938479616, coefficient := (-4392490294575269016938479616) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 130573433251345690158694400, coefficient := (-130573433251345690158694400) }, { argument := 3472535086670227421546938368, coefficient := (-3472535086670227421546938368) }, { argument := 135447565257450532475039121408, coefficient := (-135447565257450532475039121408) }, { argument := 135447515575757055956789231616, coefficient := (-135447515575757055956789231616) }, { argument := 3472551647234719594296901632, coefficient := (-3472551647234719594296901632) }, { argument := 768726350371838167057375952896, coefficient := (-768726350371838167057375952896) }, { argument := 2600130263101543785015803904, coefficient := (-2600130263101543785015803904) }, { argument := 134936899881517242336149504, coefficient := (-134936899881517242336149504) }, { argument := 2767435139372140982029680377856, coefficient := (-2767435139372140982029680377856) }, { argument := 4188233777091708252510486528, coefficient := (-4188233777091708252510486528) }, { argument := 768731796662345465360233267200, coefficient := (-768731796662345465360233267200) }, { argument := 4188233777091708252510486528, coefficient := (-4188233777091708252510486528) }, { argument := 4364689723090615415565451264, coefficient := (-4364689723090615415565451264) }, { argument := 2600130263101543785015803904, coefficient := (-2600130263101543785015803904) }, { argument := 129747019116843502246297600, coefficient := (-129747019116843502246297600) }, { argument := 110979403300917762424389500928, coefficient := (-110979403300917762424389500928) }, { argument := 110979377180328154051664412672, coefficient := (-110979377180328154051664412672) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 2600130263101543785015803904, coefficient := (-2600130263101543785015803904) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }, { argument := 40128125015891978287218425856, coefficient := (-40128125015891978287218425856) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 1490520532988146118798868480, coefficient := (-1490520532988146118798868480) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 2567007584590696093486940160, coefficient := (-2567007584590696093486940160) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 2616691602356967630780235776, coefficient := (-2616691602356967630780235776) }, { argument := 99368035532543074586591232, coefficient := (-99368035532543074586591232) }, { argument := 38101426645409439764195573760, coefficient := (-38101426645409439764195573760) }, { argument := 1486160785463693342434457026560, coefficient := (-1486160785463693342434457026560) }, { argument := 1486160240345112141748104069120, coefficient := (-1486160240345112141748104069120) }, { argument := 38101608351603173326313226240, coefficient := (-38101608351603173326313226240) }, { argument := 461240411697003808416721797120, coefficient := (-461240411697003808416721797120) }, { argument := 1656133925542384576443187200, coefficient := (-1656133925542384576443187200) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
