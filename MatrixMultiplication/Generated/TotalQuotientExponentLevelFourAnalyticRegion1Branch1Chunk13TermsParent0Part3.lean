import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 531776020733082477199879014853902336
def positiveArguments : Array ℕ := #[
    34601, 9, 1503, 39, 1617, 2421,
    75, 2421, 2523, 1503, 75, 3813,
    4305, 1845, 48585, 4305, 1845, 4305,
    4305
  ]
def positiveCoefficients : Array ℕ := #[
    5482747302312120690148428451151872, 2785365088392105618523029504, 58144496220185204786668240896, 3017478845758114420066615296, 62554657610139372015996370944, 93657901097184551422836867072,
    2901421967075110019294822400, 93657901097184551422836867072, 97603834972406701049077825536, 58144496220185204786668240896, 2901421967075110019294822400, 73754146403049296690474385408,
    83270810455055657553761402880, 71374980390047706474652631040, 939770575135628135249592975360, 83270810455055657553761402880, 71374980390047706474652631040, 83270810455055657553761402880,
    83270810455055657553761402880
  ]
def positiveScales : Array ℕ := #[
    15, 3, 10, 5, 10, 11,
    6, 11, 11, 10, 6, 11,
    12, 10, 15, 12, 10, 12,
    12
  ]
def negativeArguments : Array ℕ := #[
    1561091475, 89577, 93351, 55611, 2775, 6534724907,
    6534726357, 12542967, 55611, 1443, 1478854599, 89577,
    401403225, 89577, 93351, 55611, 2775, 202668746515,
    202668792045, 133, 6534724907, 6534726357, 519, 48789789,
    61623, 1599, 5759426253, 99261, 1561398675, 99261,
    103443, 61623, 3075, 198029846871, 198029891241, 259,
    6454508843, 6454510293, 8133, 259, 142267943743869, 142267952139907,
    1618383, 673, 3
  ]
def negativeCoefficients : Array ℕ := #[
    7199263728743688163452518400, 423015422436014209307246592, 440837633542364250343735296, 262615522478863839978848256, 13104566989963265468006400, 7534024871970278176804831232,
    7534026543706459856732946432, 7404060869567503152137109504, 262615522478863839978848256, 13628749669561796086726656, 27280052309981365397549481984, 423015422436014209307246592,
    7404582561936651731966361600, 423015422436014209307246592, 440837633542364250343735296, 262615522478863839978848256, 13104566989963265468006400, 233661156168857474512338288640,
    233661208661373579262081105920, 20580753153119447070197940224, 7534024871970278176804831232, 7534026543706459856732946432, 20077840012159761333520171008, 7200102008746315765033992192,
    291006389773876147003588608, 15102128012217125393399808, 26560665525123739668512243712, 468746819456123853556678656, 7200680438688549057016627200, 468746819456123853556678656,
    488495756087484709840355328, 291006389773876147003588608, 14521276934824159032115200, 228312869011576827715409412096, 228312920166703987121209737216, 20039154385932093199929573376,
    238129345496632289438073880576, 238129398992190103195773566976, 629260396219249860984661082112, 20039154385932093199929573376, 80089732303956889502773936128, 80089737030506090526339497984,
    61140781085168200239015788544, 26035426451220653906472206336, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    30, 16, 16, 15, 11, 32,
    32, 23, 15, 10, 30, 16,
    28, 16, 16, 15, 11, 37,
    37, 7, 32, 32, 9, 25,
    15, 10, 32, 16, 30, 16,
    16, 15, 11, 37, 37, 8,
    32, 32, 12, 8, 47, 47,
    20, 9, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15078526113197376, 3169925001442312, 10553629293916271, 5285402218862248, 10659103963471994, 11241387363998936,
    6228818690495880, 11241387363998936, 11300924490976300, 10553629293916271, 6228818690495880, 11896710815471615,
    12071797522284206, 10849405100841772, 15568223348403562, 12071797522284206, 10849405100841772, 12071797522284206,
    12071797522284206
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30539907931125137, 16450840729627935, 16510377856605633, 15763082659843835, 11438272056124861, 32605479358007361,
    32605479678129112, 23580375317767797, 15763082659843835, 10494855584491427, 30461833067604137, 16450840729627935,
    28580476966915837, 16450840729627935, 16510377856605633, 15763082659843835, 11438272056124861, 37560332672161885,
    37560332996266607, 7055282435501190, 32605479358007361, 32605479678129112, 9019590728357881, 25540075908302205,
    15911181303864252, 10642954223498123, 32423277953296301, 16598939368622512, 30540191804506134, 16598939368622512,
    16658476495620780, 15911181303864252, 11586370695117825, 37526926932084899, 37526927255330979, 8016808287686554,
    32587660171563375, 32587660495663570, 12989571918588865, 8016808287686554, 47015603954365735, 47015604039507347,
    20626121639905208, 9394462694610323, 1584962500724866
  ]

abbrev PositiveTerm := Fin 19
abbrev NegativeTerm := Fin 45
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
noncomputable def positiveFloor : ℝ := 497720420943 / 500000000000
noncomputable def negativeCeiling : ℝ := 873727497 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7199263728743688163452518400, coefficient := (-7199263728743688163452518400) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 7534024871970278176804831232, coefficient := (-7534024871970278176804831232) }, { argument := 7534026543706459856732946432, coefficient := (-7534026543706459856732946432) }, { argument := 7404060869567503152137109504, coefficient := (-7404060869567503152137109504) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 27280052309981365397549481984, coefficient := (-27280052309981365397549481984) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 7404582561936651731966361600, coefficient := (-7404582561936651731966361600) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 233661156168857474512338288640, coefficient := (-233661156168857474512338288640) }, { argument := 233661208661373579262081105920, coefficient := (-233661208661373579262081105920) }, { argument := 20580753153119447070197940224, coefficient := (-20580753153119447070197940224) }, { argument := 7534024871970278176804831232, coefficient := (-7534024871970278176804831232) }, { argument := 7534026543706459856732946432, coefficient := (-7534026543706459856732946432) }, { argument := 20077840012159761333520171008, coefficient := (-20077840012159761333520171008) }, { argument := 7200102008746315765033992192, coefficient := (-7200102008746315765033992192) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 15102128012217125393399808, coefficient := (-15102128012217125393399808) }, { argument := 26560665525123739668512243712, coefficient := (-26560665525123739668512243712) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 7200680438688549057016627200, coefficient := (-7200680438688549057016627200) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 488495756087484709840355328, coefficient := (-488495756087484709840355328) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 14521276934824159032115200, coefficient := (-14521276934824159032115200) }, { argument := 228312869011576827715409412096, coefficient := (-228312869011576827715409412096) }, { argument := 228312920166703987121209737216, coefficient := (-228312920166703987121209737216) }, { argument := 20039154385932093199929573376, coefficient := (-20039154385932093199929573376) }, { argument := 238129345496632289438073880576, coefficient := (-238129345496632289438073880576) }, { argument := 238129398992190103195773566976, coefficient := (-238129398992190103195773566976) }, { argument := 629260396219249860984661082112, coefficient := (-629260396219249860984661082112) }, { argument := 20039154385932093199929573376, coefficient := (-20039154385932093199929573376) }, { argument := 80089732303956889502773936128, coefficient := (-80089732303956889502773936128) }, { argument := 80089737030506090526339497984, coefficient := (-80089737030506090526339497984) }, { argument := 61140781085168200239015788544, coefficient := (-61140781085168200239015788544) }, { argument := 26035426451220653906472206336, coefficient := (-26035426451220653906472206336) }, { argument := 5482747302312120690148428451151872, coefficient := 5482747302312120690148428451151872 }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 3017478845758114420066615296, coefficient := 3017478845758114420066615296 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 97603834972406701049077825536, coefficient := 97603834972406701049077825536 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 73754146403049296690474385408, coefficient := 73754146403049296690474385408 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 71374980390047706474652631040, coefficient := 71374980390047706474652631040 }, { argument := 939770575135628135249592975360, coefficient := 939770575135628135249592975360 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 71374980390047706474652631040, coefficient := 71374980390047706474652631040 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }] }

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

end TermShard6


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-554172175995739428707314937364480)
def positiveArguments : Array ℕ := #[
    178473, 1107, 48585, 178473, 3813, 4305,
    1107, 4305, 435, 12615, 11165, 725,
    435, 725, 22185, 725, 435, 355395,
    22765, 12615, 22185, 725, 22765, 725,
    22185, 725, 435, 2397, 1785, 1887,
    153, 32793, 59313, 1785, 32793, 969,
    969, 1887, 1887, 59313, 1887, 2397,
    153, 15, 45, 95, 245, 205,
    5735, 175, 205, 185, 95, 95,
    185, 5735, 185, 15, 245, 27
  ]
def positiveCoefficients : Array ℕ := #[
    3452169884865307403157365587968, 85649976468057247769583157248, 939770575135628135249592975360, 3452169884865307403157365587968, 73754146403049296690474385408, 83270810455055657553761402880,
    85649976468057247769583157248, 83270810455055657553761402880, 33656494818071276223819939840, 488019174862033505245389127680, 863850033663829423078045122560, 28047079015059396853183283200,
    538503917089140419581119037440, 28047079015059396853183283200, 858240617860817543707408465920, 897506528481900699301865062400, 538503917089140419581119037440, 13748678133182116337430445424640,
    880678281072865061189955092480, 488019174862033505245389127680, 858240617860817543707408465920, 28047079015059396853183283200, 880678281072865061189955092480, 28047079015059396853183283200,
    858240617860817543707408465920, 897506528481900699301865062400, 33656494818071276223819939840, 46364723033860258108331261952, 34526921408193809229608386560, 36499888345804884042728865792,
    47351206502665795514891501568, 634308870441960552418234073088, 1147280274220840003829558673408, 34526921408193809229608386560, 634308870441960552418234073088, 37486371814610421449289105408,
    37486371814610421449289105408, 36499888345804884042728865792, 36499888345804884042728865792, 1147280274220840003829558673408, 36499888345804884042728865792, 46364723033860258108331261952,
    47351206502665795514891501568, 4642275147320176030871715840, 3481706360490132023153786880, 3675134491628472691106775040, 4738989212889346364848209920, 63444427013375739088580116480,
    110931033207838373071038709760, 3384992294920961689177292800, 63444427013375739088580116480, 3578420426059302357130280960, 3675134491628472691106775040, 3675134491628472691106775040,
    3578420426059302357130280960, 110931033207838373071038709760, 3578420426059302357130280960, 4642275147320176030871715840, 4738989212889346364848209920, 2089023816294079213892272128
  ]
def positiveScales : Array ℕ := #[
    17, 10, 15, 17, 11, 12,
    10, 12, 8, 13, 13, 9,
    8, 9, 14, 9, 8, 18,
    14, 13, 14, 9, 14, 9,
    14, 9, 8, 11, 10, 10,
    7, 15, 15, 10, 15, 9,
    9, 10, 10, 15, 10, 11,
    7, 3, 5, 6, 7, 7,
    12, 7, 7, 7, 6, 6,
    7, 12, 7, 3, 7, 4
  ]
def negativeArguments : Array ℕ := #[
    123, 145, 51, 5
  ]
def negativeCoefficients : Array ℕ := #[
    9745063989254513524005905891328, 22976167129136657902127745597440, 4040636288227481217270741467136, 396140812571321687967719751680
  ]
def negativeScales : Array ℕ := #[
    6, 7, 5, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17445346309405981, 10112439506781552, 15568223348403562, 17445346309405981, 11896710815471615, 12071797522284206,
    10112439506781552, 12071797522284206, 8764871590716857, 13622852585863008, 13446695630709832, 9501837184902278,
    8764871590716857, 9501837184902278, 14437296932707584, 9501837184902278, 8764871590716857, 18439063858881771,
    14474529838906553, 13622852585863008, 14437296932707584, 9501837184902278, 14474529838906553, 9501837184902278,
    14437296932707584, 9501837184902278, 8764871590716857, 11227014193649132, 10801708358875019, 10881878707405986,
    7257387842692651, 15001100269299442, 15856060723324442, 10801708358875019, 15001100269299442, 9920352855028171,
    9920352855028171, 10881878707405986, 10881878707405986, 15856060723324442, 10881878707405986, 11227014193649132,
    7257387842692651, 3906890595303263, 5491853096329661, 6569855608330797, 7936637938489789, 7679480099502692,
    12485577770903176, 7451211111832325, 7679480099502692, 7531381460516264, 6569855608330797, 6569855608330797,
    7531381460516264, 12485577770903176, 7531381460516264, 3906890595303263, 7936637938489789, 4754887502147955
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6942514514520450, 7179909090014935, 5672425342008812, 2321928094887363
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 6899965299 / 1000000000000
noncomputable def negativeCeiling : ℝ := 3087049727 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3452169884865307403157365587968, coefficient := 3452169884865307403157365587968 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 939770575135628135249592975360, coefficient := 939770575135628135249592975360 }, { argument := 3452169884865307403157365587968, coefficient := 3452169884865307403157365587968 }, { argument := 73754146403049296690474385408, coefficient := 73754146403049296690474385408 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 9745063989254513524005905891328, coefficient := (-9745063989254513524005905891328) }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 488019174862033505245389127680, coefficient := 488019174862033505245389127680 }, { argument := 863850033663829423078045122560, coefficient := 863850033663829423078045122560 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 538503917089140419581119037440, coefficient := 538503917089140419581119037440 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 858240617860817543707408465920, coefficient := 858240617860817543707408465920 }, { argument := 897506528481900699301865062400, coefficient := 897506528481900699301865062400 }, { argument := 538503917089140419581119037440, coefficient := 538503917089140419581119037440 }, { argument := 13748678133182116337430445424640, coefficient := 13748678133182116337430445424640 }, { argument := 880678281072865061189955092480, coefficient := 880678281072865061189955092480 }, { argument := 488019174862033505245389127680, coefficient := 488019174862033505245389127680 }, { argument := 858240617860817543707408465920, coefficient := 858240617860817543707408465920 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 880678281072865061189955092480, coefficient := 880678281072865061189955092480 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 858240617860817543707408465920, coefficient := 858240617860817543707408465920 }, { argument := 897506528481900699301865062400, coefficient := 897506528481900699301865062400 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 22976167129136657902127745597440, coefficient := (-22976167129136657902127745597440) }, { argument := 46364723033860258108331261952, coefficient := 46364723033860258108331261952 }, { argument := 34526921408193809229608386560, coefficient := 34526921408193809229608386560 }, { argument := 36499888345804884042728865792, coefficient := 36499888345804884042728865792 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 634308870441960552418234073088, coefficient := 634308870441960552418234073088 }, { argument := 1147280274220840003829558673408, coefficient := 1147280274220840003829558673408 }, { argument := 34526921408193809229608386560, coefficient := 34526921408193809229608386560 }, { argument := 634308870441960552418234073088, coefficient := 634308870441960552418234073088 }, { argument := 37486371814610421449289105408, coefficient := 37486371814610421449289105408 }, { argument := 37486371814610421449289105408, coefficient := 37486371814610421449289105408 }, { argument := 36499888345804884042728865792, coefficient := 36499888345804884042728865792 }, { argument := 36499888345804884042728865792, coefficient := 36499888345804884042728865792 }, { argument := 1147280274220840003829558673408, coefficient := 1147280274220840003829558673408 }, { argument := 36499888345804884042728865792, coefficient := 36499888345804884042728865792 }, { argument := 46364723033860258108331261952, coefficient := 46364723033860258108331261952 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 4040636288227481217270741467136, coefficient := (-4040636288227481217270741467136) }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 3675134491628472691106775040, coefficient := 3675134491628472691106775040 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }, { argument := 63444427013375739088580116480, coefficient := 63444427013375739088580116480 }, { argument := 110931033207838373071038709760, coefficient := 110931033207838373071038709760 }, { argument := 3384992294920961689177292800, coefficient := 3384992294920961689177292800 }, { argument := 63444427013375739088580116480, coefficient := 63444427013375739088580116480 }, { argument := 3578420426059302357130280960, coefficient := 3578420426059302357130280960 }, { argument := 3675134491628472691106775040, coefficient := 3675134491628472691106775040 }, { argument := 3675134491628472691106775040, coefficient := 3675134491628472691106775040 }, { argument := 3578420426059302357130280960, coefficient := 3578420426059302357130280960 }, { argument := 110931033207838373071038709760, coefficient := 110931033207838373071038709760 }, { argument := 3578420426059302357130280960, coefficient := 3578420426059302357130280960 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }, { argument := 396140812571321687967719751680, coefficient := (-396140812571321687967719751680) }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }] }

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

end TermShard7


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
