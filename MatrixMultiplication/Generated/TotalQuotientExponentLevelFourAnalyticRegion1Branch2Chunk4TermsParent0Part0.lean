import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

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
def constantNumerator : ℤ := (-317594842671758673957148774367232)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1, 465873965, 430076627, 465873965, 430076627, 3485284421179,
    1169132079, 22412484559301, 1842574053, 57895643, 1842500325, 1246581505,
    3503506730555, 1169132079, 6958905, 4371, 52311, 78255,
    22701, 4371, 90663, 45543, 4371, 52311,
    4371, 729167772149, 40366093153803, 61220635, 54223991, 2538032611,
    690918595, 20183050209387, 2538032611, 61220635, 61220635, 26237415,
    61220635, 690918595, 26237415, 364580253589, 54223991, 1,
    790320091, 729648437, 790320091, 729648437, 60950802302129, 40429332945,
    394083828462415, 65091372315, 2017089317, 65091315483, 43487174911, 61280993563825,
    40429332945, 242059527, 108159, 1294419, 1936395, 561729,
    108159, 2243427, 1126947, 108159
  ]
def negativeCoefficients : Array ℕ := #[
    39614081257132168796771975168, 34375431211837284278872309760, 31734053881412973346766716928, 34375431211837284278872309760, 31734053881412973346766716928, 3924081405125484809285533696,
    10783340124838488661485944832, 50468428554857489430004891648, 16994745996274369632952909824, 533993054701926943025004544, 16994065975500836404042137600, 11497684994877341893174231040,
    3944597901554380683157176320, 10783340124838488661485944832, 513476558273031069153361920, 20641463896623219229065216, 494063426170788021547302912, 369548789116964086197780480,
    428809766110495263984451584, 20641463896623219229065216, 428143912436410644009320448, 430141473458664503934713856, 20641463896623219229065216, 494063426170788021547302912,
    20641463896623219229065216, 410484963367601391416639488, 22724090260733740060074049536, 141165173234373194437099520, 125032010579016257930002432, 5852304753230728717949468672,
    1593149812216497480075837440, 22724094350548826117256511488, 5852304753230728717949468672, 141165173234373194437099520, 141165173234373194437099520, 120998719915177023803228160,
    141165173234373194437099520, 1593149812216497480075837440, 120998719915177023803228160, 410480873552515334234177536, 125032010579016257930002432, 39614081257132168796771975168,
    116630659639902748325810536448, 107677103848969497028681793536, 116630659639902748325810536448, 107677103848969497028681793536, 137249005267900467077806292992, 372894778953604541754963394560,
    1774795783016070659629215907840, 600361943250674113704382955520, 18604365202256298562746843136, 600361419067994515173764235264, 401098393035929973868187353088, 137992529889468016842348953600,
    372894778953604541754963394560, 17860840580688748798204182528, 510766436420697956668145664, 12225441800779286575734325248, 9144366845596366643574865920, 10610760808223531744976961536,
    510766436420697956668145664, 10594284471564799552826376192, 10643713481540996129278132224, 510766436420697956668145664
  ]
def negativeScales : Array ℕ := #[
    0, 28, 28, 28, 28, 41,
    30, 44, 30, 25, 30, 30,
    41, 30, 22, 12, 15, 16,
    14, 12, 16, 15, 12, 15,
    12, 39, 45, 25, 25, 31,
    29, 44, 31, 25, 25, 24,
    25, 29, 24, 38, 25, 0,
    29, 29, 29, 29, 45, 35,
    48, 35, 30, 35, 35, 45,
    35, 27, 16, 20, 20, 19,
    16, 21, 20, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 28795364468508291, 28680018487665498, 28795364468508291, 28680018487665498, 41664413532586473,
    30122790776973474, 44349367822709561, 30779075456764498, 25786951445410328, 30779017728203273, 30215330067353296,
    41671936806467749, 30122790776973474, 22730428881958850, 12093747662785669, 15674826729059175, 16255895313636262,
    14470468230513509, 12093747662785669, 16468226279726832, 15474941707092834, 12093747662785669, 15674826729059175,
    12093747662785669, 39407459842126117, 45198209195375561, 25867514675659074, 25692427966750701, 31241063460370056,
    29363940499367778, 44198209455027558, 31241063460370056, 25867514675659074, 25867514675659074, 24645122251930640,
    25867514675659074, 29363940499367778, 24645122251930640, 38407445467944689, 25692427966750701, 0,
    29557861842984200, 29442626263684090, 29557861842984200, 29442626263684090, 45792710445416436, 35234683349246043,
    48485495876996257, 35921747286035966, 30909627827277061, 35921746026402214, 35339870937871623, 45800504922410549,
    35234683349246043, 27850786637890816, 16722794192703879, 20303873258815179, 20884941846757732, 19099514760308992,
    16722794192703879, 21097272809522322, 20103988236888300, 16722794192703879
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
noncomputable def negativeCeiling : ℝ := 2511906327 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 34375431211837284278872309760, coefficient := (-34375431211837284278872309760) }, { argument := 31734053881412973346766716928, coefficient := (-31734053881412973346766716928) }, { argument := 34375431211837284278872309760, coefficient := (-34375431211837284278872309760) }, { argument := 31734053881412973346766716928, coefficient := (-31734053881412973346766716928) }, { argument := 3924081405125484809285533696, coefficient := (-3924081405125484809285533696) }, { argument := 10783340124838488661485944832, coefficient := (-10783340124838488661485944832) }, { argument := 50468428554857489430004891648, coefficient := (-50468428554857489430004891648) }, { argument := 16994745996274369632952909824, coefficient := (-16994745996274369632952909824) }, { argument := 533993054701926943025004544, coefficient := (-533993054701926943025004544) }, { argument := 16994065975500836404042137600, coefficient := (-16994065975500836404042137600) }, { argument := 11497684994877341893174231040, coefficient := (-11497684994877341893174231040) }, { argument := 3944597901554380683157176320, coefficient := (-3944597901554380683157176320) }, { argument := 10783340124838488661485944832, coefficient := (-10783340124838488661485944832) }, { argument := 513476558273031069153361920, coefficient := (-513476558273031069153361920) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 369548789116964086197780480, coefficient := (-369548789116964086197780480) }, { argument := 428809766110495263984451584, coefficient := (-428809766110495263984451584) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 428143912436410644009320448, coefficient := (-428143912436410644009320448) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 410484963367601391416639488, coefficient := (-410484963367601391416639488) }, { argument := 22724090260733740060074049536, coefficient := (-22724090260733740060074049536) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 125032010579016257930002432, coefficient := (-125032010579016257930002432) }, { argument := 5852304753230728717949468672, coefficient := (-5852304753230728717949468672) }, { argument := 1593149812216497480075837440, coefficient := (-1593149812216497480075837440) }, { argument := 22724094350548826117256511488, coefficient := (-22724094350548826117256511488) }, { argument := 5852304753230728717949468672, coefficient := (-5852304753230728717949468672) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 120998719915177023803228160, coefficient := (-120998719915177023803228160) }, { argument := 141165173234373194437099520, coefficient := (-141165173234373194437099520) }, { argument := 1593149812216497480075837440, coefficient := (-1593149812216497480075837440) }, { argument := 120998719915177023803228160, coefficient := (-120998719915177023803228160) }, { argument := 410480873552515334234177536, coefficient := (-410480873552515334234177536) }, { argument := 125032010579016257930002432, coefficient := (-125032010579016257930002432) }, { argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 116630659639902748325810536448, coefficient := (-116630659639902748325810536448) }, { argument := 107677103848969497028681793536, coefficient := (-107677103848969497028681793536) }, { argument := 116630659639902748325810536448, coefficient := (-116630659639902748325810536448) }, { argument := 107677103848969497028681793536, coefficient := (-107677103848969497028681793536) }, { argument := 137249005267900467077806292992, coefficient := (-137249005267900467077806292992) }, { argument := 372894778953604541754963394560, coefficient := (-372894778953604541754963394560) }, { argument := 1774795783016070659629215907840, coefficient := (-1774795783016070659629215907840) }, { argument := 600361943250674113704382955520, coefficient := (-600361943250674113704382955520) }, { argument := 18604365202256298562746843136, coefficient := (-18604365202256298562746843136) }, { argument := 600361419067994515173764235264, coefficient := (-600361419067994515173764235264) }, { argument := 401098393035929973868187353088, coefficient := (-401098393035929973868187353088) }, { argument := 137992529889468016842348953600, coefficient := (-137992529889468016842348953600) }, { argument := 372894778953604541754963394560, coefficient := (-372894778953604541754963394560) }, { argument := 17860840580688748798204182528, coefficient := (-17860840580688748798204182528) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 9144366845596366643574865920, coefficient := (-9144366845596366643574865920) }, { argument := 10610760808223531744976961536, coefficient := (-10610760808223531744976961536) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 10594284471564799552826376192, coefficient := (-10594284471564799552826376192) }, { argument := 10643713481540996129278132224, coefficient := (-10643713481540996129278132224) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }] }

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
def constantNumerator : ℤ := (-642583521489308789679279197650944)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1294419, 108159, 76020216933535, 3303590032700257, 4520983705, 4004299853,
    187427067313, 51022530385, 1651795510571649, 187427067313, 4520983705, 4520983705,
    1937564445, 4520983705, 51022530385, 1937564445, 38009614245247, 4004299853,
    3441, 41181, 61605, 17871, 3441, 71373,
    35853, 3441, 41181, 3441, 444967911, 37417014297,
    18708502635, 222488469, 1473049971227, 152881632111505, 460051569, 1536742929039435,
    472079061, 15034365, 460051569, 261597951, 472079061, 7369845723,
    9020619, 76440843034615, 460051569, 15034365, 9020619, 15034365,
    231529221, 261597951, 1473049971227, 465873949, 430076611, 465873949,
    430076611, 60950831177591, 323434782297, 394084004640649, 520731169779, 16136720461,
    520730715123, 347897527031, 61281022560631, 323434782297
  ]
def negativeCoefficients : Array ℕ := #[
    12225441800779286575734325248, 510766436420697956668145664, 42795577581811562010556497920, 1859755855031720265094931677184, 20849357341886550439698104320, 18466573645670944675161178112,
    864354785802210991085769981952, 235299890001291069248021463040, 1859756411475684155664919166976, 864354785802210991085769981952, 20849357341886550439698104320, 20849357341886550439698104320,
    17870877721617043234026946560, 20849357341886550439698104320, 235299890001291069248021463040, 17870877721617043234026946560, 42795021137847671440569008128, 18466573645670944675161178112,
    16249663067554449180327936, 388943548262109719090429952, 290921387177184493389742080, 337573645661453718455844864, 16249663067554449180327936, 337049462981855187837124608,
    338622011020650779693285376, 16249663067554449180327936, 388943548262109719090429952, 16249663067554449180327936, 2052052293807542300829548544, 172555521684772578660332863488,
    172555480055082890316302254080, 2052093923497230644860157952, 414626706344752315904294912, 43032353838072948348713697280, 2121613388512882717806821376, 432554680161640252658008719360,
    2177080405206029978403078144, 69333770866434075745320960, 2121613388512882717806821376, 1206407613075952917968584704, 2177080405206029978403078144, 33987414478725983930356334592,
    1331208400635534254310162432, 43032369025822336083694714880, 2121613388512882717806821376, 69333770866434075745320960, 1331208400635534254310162432, 69333770866434075745320960,
    2135480142686169532955885568, 1206407613075952917968584704, 414626706344752315904294912, 34375430031245663561461006336, 31734052700821352629355413504, 34375430031245663561461006336,
    31734052700821352629355413504, 137249070289660418753264877568, 372894915848045234258152783872, 1774796576452299652821264891904, 600362163757288163305328738304, 18604372033316213358315175936,
    600361639574608564774710018048, 401098540313581736860640608256, 137992595184470365109630271488, 372894915848045234258152783872
  ]
def negativeScales : Array ℕ := #[
    20, 16, 46, 51, 32, 31,
    37, 35, 50, 37, 32, 32,
    30, 32, 35, 30, 45, 31,
    11, 15, 15, 14, 11, 16,
    15, 11, 15, 11, 28, 35,
    34, 27, 40, 47, 28, 50,
    28, 23, 28, 27, 28, 32,
    23, 46, 28, 23, 23, 23,
    27, 27, 40, 28, 28, 28,
    28, 45, 38, 48, 38, 33,
    38, 38, 45, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20303873258815179, 16722794192703879, 46111448375658618, 51552956086313810, 32073989571740908, 31898902869465304,
    37447538358862728, 35570415397862847, 50552956517971990, 37447538358862728, 32073989571740908, 32073989571740908,
    30851597152190147, 32073989571740908, 35570415397862847, 30851597152190147, 45111429617080941, 31898902869465304,
    11748612176955137, 15329691242970910, 15910759832877788, 14125332744464723, 11748612176955137, 16123090793678054,
    15129806221044031, 11748612176955137, 15329691242970910, 11748612176955137, 28729126058666865, 35122975391718365,
    34122975043662542, 27729155326116844, 40421943511329346, 47119408413647298, 28777220347129473, 50448797270174705,
    28814453253790313, 23841760600399908, 28777220347129473, 27962776012795654, 28814453253790313, 32778987273318904,
    23104795004754893, 46119408922828993, 28777220347129473, 23841760600399908, 23104795004754893, 23841760600399908,
    27786619045219200, 27962776012795654, 40421943511329346, 28795364418960295, 28680018433993386, 28795364418960295,
    28680018433993386, 45792711128893517, 38234683878877739, 48485496521964127, 38921747815922611, 33909628356998729,
    38921746556289321, 38339871467608722, 45800505605061669, 38234683878877739
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
noncomputable def negativeCeiling : ℝ := 3092200823 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 42795577581811562010556497920, coefficient := (-42795577581811562010556497920) }, { argument := 1859755855031720265094931677184, coefficient := (-1859755855031720265094931677184) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 18466573645670944675161178112, coefficient := (-18466573645670944675161178112) }, { argument := 864354785802210991085769981952, coefficient := (-864354785802210991085769981952) }, { argument := 235299890001291069248021463040, coefficient := (-235299890001291069248021463040) }, { argument := 1859756411475684155664919166976, coefficient := (-1859756411475684155664919166976) }, { argument := 864354785802210991085769981952, coefficient := (-864354785802210991085769981952) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 17870877721617043234026946560, coefficient := (-17870877721617043234026946560) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 235299890001291069248021463040, coefficient := (-235299890001291069248021463040) }, { argument := 17870877721617043234026946560, coefficient := (-17870877721617043234026946560) }, { argument := 42795021137847671440569008128, coefficient := (-42795021137847671440569008128) }, { argument := 18466573645670944675161178112, coefficient := (-18466573645670944675161178112) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 337573645661453718455844864, coefficient := (-337573645661453718455844864) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 337049462981855187837124608, coefficient := (-337049462981855187837124608) }, { argument := 338622011020650779693285376, coefficient := (-338622011020650779693285376) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 2052052293807542300829548544, coefficient := (-2052052293807542300829548544) }, { argument := 172555521684772578660332863488, coefficient := (-172555521684772578660332863488) }, { argument := 172555480055082890316302254080, coefficient := (-172555480055082890316302254080) }, { argument := 2052093923497230644860157952, coefficient := (-2052093923497230644860157952) }, { argument := 414626706344752315904294912, coefficient := (-414626706344752315904294912) }, { argument := 43032353838072948348713697280, coefficient := (-43032353838072948348713697280) }, { argument := 2121613388512882717806821376, coefficient := (-2121613388512882717806821376) }, { argument := 432554680161640252658008719360, coefficient := (-432554680161640252658008719360) }, { argument := 2177080405206029978403078144, coefficient := (-2177080405206029978403078144) }, { argument := 69333770866434075745320960, coefficient := (-69333770866434075745320960) }, { argument := 2121613388512882717806821376, coefficient := (-2121613388512882717806821376) }, { argument := 1206407613075952917968584704, coefficient := (-1206407613075952917968584704) }, { argument := 2177080405206029978403078144, coefficient := (-2177080405206029978403078144) }, { argument := 33987414478725983930356334592, coefficient := (-33987414478725983930356334592) }, { argument := 1331208400635534254310162432, coefficient := (-1331208400635534254310162432) }, { argument := 43032369025822336083694714880, coefficient := (-43032369025822336083694714880) }, { argument := 2121613388512882717806821376, coefficient := (-2121613388512882717806821376) }, { argument := 69333770866434075745320960, coefficient := (-69333770866434075745320960) }, { argument := 1331208400635534254310162432, coefficient := (-1331208400635534254310162432) }, { argument := 69333770866434075745320960, coefficient := (-69333770866434075745320960) }, { argument := 2135480142686169532955885568, coefficient := (-2135480142686169532955885568) }, { argument := 1206407613075952917968584704, coefficient := (-1206407613075952917968584704) }, { argument := 414626706344752315904294912, coefficient := (-414626706344752315904294912) }, { argument := 34375430031245663561461006336, coefficient := (-34375430031245663561461006336) }, { argument := 31734052700821352629355413504, coefficient := (-31734052700821352629355413504) }, { argument := 34375430031245663561461006336, coefficient := (-34375430031245663561461006336) }, { argument := 31734052700821352629355413504, coefficient := (-31734052700821352629355413504) }, { argument := 137249070289660418753264877568, coefficient := (-137249070289660418753264877568) }, { argument := 372894915848045234258152783872, coefficient := (-372894915848045234258152783872) }, { argument := 1774796576452299652821264891904, coefficient := (-1774796576452299652821264891904) }, { argument := 600362163757288163305328738304, coefficient := (-600362163757288163305328738304) }, { argument := 18604372033316213358315175936, coefficient := (-18604372033316213358315175936) }, { argument := 600361639574608564774710018048, coefficient := (-600361639574608564774710018048) }, { argument := 401098540313581736860640608256, coefficient := (-401098540313581736860640608256) }, { argument := 137992595184470365109630271488, coefficient := (-137992595184470365109630271488) }, { argument := 372894915848045234258152783872, coefficient := (-372894915848045234258152783872) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
