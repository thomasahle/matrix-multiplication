import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 20, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

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
def constantNumerator : ℤ := (-1460797891728613166352245750497280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1259224839, 9956343805, 478150599, 1233125229, 1031798661, 28865196687,
    9698417, 1031798661, 931135377, 478150599, 478150599, 931135377,
    28865196687, 931135377, 1259223815, 1233125229, 150523525971, 25649138802717,
    181630728929, 724318589648439, 57478078775, 6897369453, 181630728929, 360962334707,
    57478078775, 5570775394873, 356364088405, 102596607976437, 181630728929, 6897369453,
    356364088405, 6897369453, 181630728929, 181630728929, 150523525971, 2819561,
    559217175, 559217175, 2819561, 919275, 592236225, 6298681305,
    296119005, 919275, 163690977791131, 1812430215, 2697182157378625, 18964208835,
    839906685, 5394362717571371, 839906685, 1635607755, 30899724885, 1635607755,
    18964208835, 30899724885, 20461438773303, 1635607755, 1635607755, 1812430215,
    761685, 490710015, 5218907367, 245355747
  ]
def negativeCoefficients : Array ℕ := #[
    23228598336291114266419789824, 183662126080698557601289338880, 17640643456887844514423635968, 22747145510197483715967320064, 304533213361011210564786978816, 532468895922377833106418696192,
    183197917510772703697911676928, 304533213361011210564786978816, 17176415997496059132465119232, 17640643456887844514423635968, 17640643456887844514423635968, 17176415997496059132465119232,
    532468895922377833106418696192, 17176415997496059132465119232, 23228579446825182787838935040, 22747145510197483715967320064, 21692726255151640867044851712, 924107615634323288931283501056,
    418811946559322095630478737408, 6524081860876466163445282111488, 265070852252735503563594137600, 15904251135164130213815648256, 418811946559322095630478737408, 416161238036794740594842796032,
    265070852252735503563594137600, 6422666750083781251345885954048, 410859820991740030523570913280, 924108090904317061715674005504, 418811946559322095630478737408, 15904251135164130213815648256,
    410859820991740030523570913280, 15904251135164130213815648256, 418811946559322095630478737408, 418811946559322095630478737408, 21692726255151640867044851712, 52011720167212577063960576,
    10315736108847847225216204800, 10315736108847847225216204800, 52011720167212577063960576, 135661045266874784494387200, 43699320295019466382009958400, 464760648140775579054526955520,
    43699452004772152668208496640, 135661045266874784494387200, 46074914161503106750989991936, 8358359081890844620735119360, 1518378569865090756044128256000, 87456976734906642495008931840,
    7746771831996392575315476480, 1518378120297232661930496229376, 7746771831996392575315476480, 7542909415364908560175595520, 284999658450814653165553582080, 7542909415364908560175595520,
    87456976734906642495008931840, 284999658450814653165553582080, 46075064017455804788867334144, 7542909415364908560175595520, 7542909415364908560175595520, 8358359081890844620735119360,
    7025304129891729911316480, 2263000515277793794782658560, 24067962135861592486752288768, 2263007335961415048889368576
  ]
def negativeScales : Array ℕ := #[
    30, 33, 28, 30, 29, 34,
    23, 29, 29, 28, 28, 29,
    34, 29, 30, 30, 37, 44,
    37, 49, 35, 32, 37, 38,
    35, 42, 38, 46, 37, 32,
    38, 32, 37, 37, 37, 21,
    29, 29, 21, 19, 29, 32,
    28, 19, 47, 30, 51, 34,
    29, 52, 29, 30, 34, 30,
    34, 34, 44, 30, 30, 30,
    19, 28, 32, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30229888758289822, 33212968903228933, 28832889843427055, 30199672172853704, 29942514342537762, 34748612004972475,
    23209317855528862, 29942514342537762, 29794415694943711, 28832889843427055, 28832889843427055, 29794415694943711,
    34748612004972475, 29794415694943711, 30229887585091616, 30199672172853704, 37131198033398312, 44543975620152485,
    37402217347287984, 49363617730991268, 35742292789075442, 32683399099880771, 37402217347287984, 38393057348002506,
    35742292789075442, 42341015288562221, 38374561004385114, 46543976362132613, 37402217347287984, 32683399099880771,
    38374561004385114, 32683399099880771, 37402217347287984, 37402217347287984, 37131198033398312, 21427039124705171,
    29058833429373802, 29058833429373802, 21427039124705171, 19810136981780274, 29141597496877949, 32552402670874124,
    28141601845154293, 19810136981780274, 47217968134934601, 30755278301552781, 51260374382285670, 34142560134181975,
    29645653810145083, 52260373955126444, 29645653810145083, 30607179662318269, 34846874943689492, 30607179662318269,
    34142560134181975, 34846874943689492, 44217972827207872, 30607179662318269, 30607179662318269, 30755278301552781,
    19538834959170594, 28870295477599567, 32281100649055299, 27870299825876117
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
noncomputable def negativeCeiling : ℝ := 6655462113 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23228598336291114266419789824, coefficient := (-23228598336291114266419789824) }, { argument := 183662126080698557601289338880, coefficient := (-183662126080698557601289338880) }, { argument := 17640643456887844514423635968, coefficient := (-17640643456887844514423635968) }, { argument := 22747145510197483715967320064, coefficient := (-22747145510197483715967320064) }, { argument := 304533213361011210564786978816, coefficient := (-304533213361011210564786978816) }, { argument := 532468895922377833106418696192, coefficient := (-532468895922377833106418696192) }, { argument := 183197917510772703697911676928, coefficient := (-183197917510772703697911676928) }, { argument := 304533213361011210564786978816, coefficient := (-304533213361011210564786978816) }, { argument := 17176415997496059132465119232, coefficient := (-17176415997496059132465119232) }, { argument := 17640643456887844514423635968, coefficient := (-17640643456887844514423635968) }, { argument := 17640643456887844514423635968, coefficient := (-17640643456887844514423635968) }, { argument := 17176415997496059132465119232, coefficient := (-17176415997496059132465119232) }, { argument := 532468895922377833106418696192, coefficient := (-532468895922377833106418696192) }, { argument := 17176415997496059132465119232, coefficient := (-17176415997496059132465119232) }, { argument := 23228579446825182787838935040, coefficient := (-23228579446825182787838935040) }, { argument := 22747145510197483715967320064, coefficient := (-22747145510197483715967320064) }, { argument := 21692726255151640867044851712, coefficient := (-21692726255151640867044851712) }, { argument := 924107615634323288931283501056, coefficient := (-924107615634323288931283501056) }, { argument := 418811946559322095630478737408, coefficient := (-418811946559322095630478737408) }, { argument := 6524081860876466163445282111488, coefficient := (-6524081860876466163445282111488) }, { argument := 265070852252735503563594137600, coefficient := (-265070852252735503563594137600) }, { argument := 15904251135164130213815648256, coefficient := (-15904251135164130213815648256) }, { argument := 418811946559322095630478737408, coefficient := (-418811946559322095630478737408) }, { argument := 416161238036794740594842796032, coefficient := (-416161238036794740594842796032) }, { argument := 265070852252735503563594137600, coefficient := (-265070852252735503563594137600) }, { argument := 6422666750083781251345885954048, coefficient := (-6422666750083781251345885954048) }, { argument := 410859820991740030523570913280, coefficient := (-410859820991740030523570913280) }, { argument := 924108090904317061715674005504, coefficient := (-924108090904317061715674005504) }, { argument := 418811946559322095630478737408, coefficient := (-418811946559322095630478737408) }, { argument := 15904251135164130213815648256, coefficient := (-15904251135164130213815648256) }, { argument := 410859820991740030523570913280, coefficient := (-410859820991740030523570913280) }, { argument := 15904251135164130213815648256, coefficient := (-15904251135164130213815648256) }, { argument := 418811946559322095630478737408, coefficient := (-418811946559322095630478737408) }, { argument := 418811946559322095630478737408, coefficient := (-418811946559322095630478737408) }, { argument := 21692726255151640867044851712, coefficient := (-21692726255151640867044851712) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 10315736108847847225216204800, coefficient := (-10315736108847847225216204800) }, { argument := 52011720167212577063960576, coefficient := (-52011720167212577063960576) }, { argument := 135661045266874784494387200, coefficient := (-135661045266874784494387200) }, { argument := 43699320295019466382009958400, coefficient := (-43699320295019466382009958400) }, { argument := 464760648140775579054526955520, coefficient := (-464760648140775579054526955520) }, { argument := 43699452004772152668208496640, coefficient := (-43699452004772152668208496640) }, { argument := 135661045266874784494387200, coefficient := (-135661045266874784494387200) }, { argument := 46074914161503106750989991936, coefficient := (-46074914161503106750989991936) }, { argument := 8358359081890844620735119360, coefficient := (-8358359081890844620735119360) }, { argument := 1518378569865090756044128256000, coefficient := (-1518378569865090756044128256000) }, { argument := 87456976734906642495008931840, coefficient := (-87456976734906642495008931840) }, { argument := 7746771831996392575315476480, coefficient := (-7746771831996392575315476480) }, { argument := 1518378120297232661930496229376, coefficient := (-1518378120297232661930496229376) }, { argument := 7746771831996392575315476480, coefficient := (-7746771831996392575315476480) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 284999658450814653165553582080, coefficient := (-284999658450814653165553582080) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 87456976734906642495008931840, coefficient := (-87456976734906642495008931840) }, { argument := 284999658450814653165553582080, coefficient := (-284999658450814653165553582080) }, { argument := 46075064017455804788867334144, coefficient := (-46075064017455804788867334144) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 7542909415364908560175595520, coefficient := (-7542909415364908560175595520) }, { argument := 8358359081890844620735119360, coefficient := (-8358359081890844620735119360) }, { argument := 7025304129891729911316480, coefficient := (-7025304129891729911316480) }, { argument := 2263000515277793794782658560, coefficient := (-2263000515277793794782658560) }, { argument := 24067962135861592486752288768, coefficient := (-24067962135861592486752288768) }, { argument := 2263007335961415048889368576, coefficient := (-2263007335961415048889368576) }] }

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
def constantNumerator : ℤ := (-10816028766089907001170921584066560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    761685, 3612006315, 141355722837, 141355722837, 3612006315, 75946244111,
    450625, 373375, 8787937489535, 2510625, 2430280197025, 10055375,
    10055375, 7197125, 373375, 1259225127, 9956344021, 478150713,
    1233125523, 1031798907, 28865203569, 4965589609, 1031798907, 931135599,
    478150713, 478150713, 931135599, 28865203569, 931135599, 1259224103,
    1233125523, 17419636347603, 3015137992266765, 653320330637, 85890267639464775, 206746940075,
    24809632809, 653320330637, 1298370783671, 206746940075, 20037913432069, 1281831028465,
    12060558486221349, 653320330637, 24809632809, 1281831028465, 24809632809, 653320330637,
    653320330637, 17419636347603, 2698950260544577, 70929384057, 42914153230461715, 742163555133,
    32869714563, 85828275311498993, 32869714563, 64009444149, 1209259498923, 64009444149,
    742163555133, 1209259498923, 337370080460757, 64009444149
  ]
def negativeCoefficients : Array ℕ := #[
    7025304129891729911316480, 8328719510678465739101306880, 325944105316044959583855181824, 325944105316044959583855181824, 8328719510678465739101306880, 21890014507423252880329539584,
    133001024771445867151360000, 6887553068521303834624000, 79154704006450076183135518720, 185251427360228172103680000, 21890017979455371203103948800, 185488929190177182580736000,
    185488929190177182580736000, 132763522941496856674304000, 6887553068521303834624000, 23228603648953407494770655232, 183662130065195277522552487936, 17640647662745493320201404416,
    22747150933540241386575495168, 304533285967395884685582139392, 532469022872870548375552917504, 183197921384588959176917516288, 304533285967395884685582139392, 17176420092673243495985577984,
    17640647662745493320201404416, 17640647662745493320201404416, 17176420092673243495985577984, 532469022872870548375552917504, 17176420092673243495985577984, 23228584759487476016189800448,
    22747150933540241386575495168, 78451067763994418732322521088, 3394743584610807076019880591360, 1506454117176505570108767207424, 24175961083490358235561879142400, 953451972896522512727067852800,
    57207118373791350763624071168, 1506454117176505570108767207424, 1496919597447540344981496528896, 953451972896522512727067852800, 23102141303282740483376854073344, 1477850557989609894726955171840,
    3394745419026658792046742994944, 1506454117176505570108767207424, 57207118373791350763624071168, 1477850557989609894726955171840, 57207118373791350763624071168, 1506454117176505570108767207424,
    1506454117176505570108767207424, 78451067763994418732322521088, 1519373923460007508725437825024, 327104048751333375810132246528, 48317041124406936706763362140160, 3422625290593219956647481311232,
    303169606159772397092317691904, 48317023588839900796935592738816, 303169606159772397092317691904, 295191458629252070853046173696, 11153450247667416082501582454784, 295191458629252070853046173696,
    3422625290593219956647481311232, 11153450247667416082501582454784, 1519379768649019478668027625472, 295191458629252070853046173696
  ]
def negativeScales : Array ℕ := #[
    19, 31, 37, 37, 31, 36,
    18, 18, 42, 21, 41, 23,
    23, 22, 18, 30, 33, 28,
    30, 29, 34, 32, 29, 29,
    28, 28, 29, 34, 29, 30,
    30, 43, 51, 39, 56, 37,
    34, 39, 40, 37, 44, 40,
    53, 39, 34, 40, 34, 39,
    39, 43, 51, 36, 55, 39,
    34, 56, 34, 35, 40, 35,
    39, 40, 48, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19538834959170594, 31750153269348281, 37040539336137203, 37040539336137203, 31750153269348281, 36144259567499343,
    18781567829231832, 18510265806973259, 42998661769426120, 21259615125594917, 41144259796328936, 23261463549987285,
    23261463549987285, 22778989285106841, 18510265806973259, 30229889088251646, 33212968934527785, 28832890187392365,
    30199672516819006, 29942514686503118, 34748612348937779, 32209317886035407, 29942514686503118, 29794416038909017,
    28832890187392365, 28832890187392365, 29794416038909017, 34748612348937779, 29794416038909017, 30229887915053708,
    30199672516819006, 43985779758918333, 51421145454027274, 39248999579340852, 56253344184791521, 37589075020942641,
    34530181331885626, 39248999579340852, 40239839580055376, 37589075020942641, 44187797520615096, 40221343236437987,
    53421146233615444, 39248999579340852, 34530181331885626, 40221343236437987, 34530181331885626, 39248999579340852,
    39248999579340852, 43985779758918333, 51261319812665441, 36045664368315071, 55252303050023695, 39432946201196557,
    34936039885359499, 56252302526430370, 34936039885359499, 35897565733506767, 40137261009072424, 35897565733506767,
    39432946201196557, 40137261009072424, 48261325362852166, 35897565733506767
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
noncomputable def negativeCeiling : ℝ := 61194425901 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7025304129891729911316480, coefficient := (-7025304129891729911316480) }, { argument := 8328719510678465739101306880, coefficient := (-8328719510678465739101306880) }, { argument := 325944105316044959583855181824, coefficient := (-325944105316044959583855181824) }, { argument := 325944105316044959583855181824, coefficient := (-325944105316044959583855181824) }, { argument := 8328719510678465739101306880, coefficient := (-8328719510678465739101306880) }, { argument := 21890014507423252880329539584, coefficient := (-21890014507423252880329539584) }, { argument := 133001024771445867151360000, coefficient := (-133001024771445867151360000) }, { argument := 6887553068521303834624000, coefficient := (-6887553068521303834624000) }, { argument := 79154704006450076183135518720, coefficient := (-79154704006450076183135518720) }, { argument := 185251427360228172103680000, coefficient := (-185251427360228172103680000) }, { argument := 21890017979455371203103948800, coefficient := (-21890017979455371203103948800) }, { argument := 185488929190177182580736000, coefficient := (-185488929190177182580736000) }, { argument := 185488929190177182580736000, coefficient := (-185488929190177182580736000) }, { argument := 132763522941496856674304000, coefficient := (-132763522941496856674304000) }, { argument := 6887553068521303834624000, coefficient := (-6887553068521303834624000) }, { argument := 23228603648953407494770655232, coefficient := (-23228603648953407494770655232) }, { argument := 183662130065195277522552487936, coefficient := (-183662130065195277522552487936) }, { argument := 17640647662745493320201404416, coefficient := (-17640647662745493320201404416) }, { argument := 22747150933540241386575495168, coefficient := (-22747150933540241386575495168) }, { argument := 304533285967395884685582139392, coefficient := (-304533285967395884685582139392) }, { argument := 532469022872870548375552917504, coefficient := (-532469022872870548375552917504) }, { argument := 183197921384588959176917516288, coefficient := (-183197921384588959176917516288) }, { argument := 304533285967395884685582139392, coefficient := (-304533285967395884685582139392) }, { argument := 17176420092673243495985577984, coefficient := (-17176420092673243495985577984) }, { argument := 17640647662745493320201404416, coefficient := (-17640647662745493320201404416) }, { argument := 17640647662745493320201404416, coefficient := (-17640647662745493320201404416) }, { argument := 17176420092673243495985577984, coefficient := (-17176420092673243495985577984) }, { argument := 532469022872870548375552917504, coefficient := (-532469022872870548375552917504) }, { argument := 17176420092673243495985577984, coefficient := (-17176420092673243495985577984) }, { argument := 23228584759487476016189800448, coefficient := (-23228584759487476016189800448) }, { argument := 22747150933540241386575495168, coefficient := (-22747150933540241386575495168) }, { argument := 78451067763994418732322521088, coefficient := (-78451067763994418732322521088) }, { argument := 3394743584610807076019880591360, coefficient := (-3394743584610807076019880591360) }, { argument := 1506454117176505570108767207424, coefficient := (-1506454117176505570108767207424) }, { argument := 24175961083490358235561879142400, coefficient := (-24175961083490358235561879142400) }, { argument := 953451972896522512727067852800, coefficient := (-953451972896522512727067852800) }, { argument := 57207118373791350763624071168, coefficient := (-57207118373791350763624071168) }, { argument := 1506454117176505570108767207424, coefficient := (-1506454117176505570108767207424) }, { argument := 1496919597447540344981496528896, coefficient := (-1496919597447540344981496528896) }, { argument := 953451972896522512727067852800, coefficient := (-953451972896522512727067852800) }, { argument := 23102141303282740483376854073344, coefficient := (-23102141303282740483376854073344) }, { argument := 1477850557989609894726955171840, coefficient := (-1477850557989609894726955171840) }, { argument := 3394745419026658792046742994944, coefficient := (-3394745419026658792046742994944) }, { argument := 1506454117176505570108767207424, coefficient := (-1506454117176505570108767207424) }, { argument := 57207118373791350763624071168, coefficient := (-57207118373791350763624071168) }, { argument := 1477850557989609894726955171840, coefficient := (-1477850557989609894726955171840) }, { argument := 57207118373791350763624071168, coefficient := (-57207118373791350763624071168) }, { argument := 1506454117176505570108767207424, coefficient := (-1506454117176505570108767207424) }, { argument := 1506454117176505570108767207424, coefficient := (-1506454117176505570108767207424) }, { argument := 78451067763994418732322521088, coefficient := (-78451067763994418732322521088) }, { argument := 1519373923460007508725437825024, coefficient := (-1519373923460007508725437825024) }, { argument := 327104048751333375810132246528, coefficient := (-327104048751333375810132246528) }, { argument := 48317041124406936706763362140160, coefficient := (-48317041124406936706763362140160) }, { argument := 3422625290593219956647481311232, coefficient := (-3422625290593219956647481311232) }, { argument := 303169606159772397092317691904, coefficient := (-303169606159772397092317691904) }, { argument := 48317023588839900796935592738816, coefficient := (-48317023588839900796935592738816) }, { argument := 303169606159772397092317691904, coefficient := (-303169606159772397092317691904) }, { argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }, { argument := 11153450247667416082501582454784, coefficient := (-11153450247667416082501582454784) }, { argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }, { argument := 3422625290593219956647481311232, coefficient := (-3422625290593219956647481311232) }, { argument := 11153450247667416082501582454784, coefficient := (-11153450247667416082501582454784) }, { argument := 1519379768649019478668027625472, coefficient := (-1519379768649019478668027625472) }, { argument := 295191458629252070853046173696, coefficient := (-295191458629252070853046173696) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
