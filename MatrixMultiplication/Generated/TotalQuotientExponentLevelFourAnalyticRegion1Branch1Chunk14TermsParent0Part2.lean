import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1498822434535655182121646084325376)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    34718475, 6885883125, 6885883125, 34718475, 65007, 199215,
    589257, 1314819, 65007, 656361, 1335789, 65007,
    199215, 65007, 3364914597, 667379792475, 667379792475, 3364914597,
    950175, 612143325, 6510401685, 306072585, 950175, 215254545,
    42692475375, 42692475375, 215254545, 26581725, 17125082775, 182132456895,
    8562567195, 26581725, 5897377455, 11685, 224364472657, 122265,
    5415, 224364472657, 5415, 10545, 199215, 10545,
    122265, 199215, 5897377455, 10545, 10545, 11685,
    590566262097, 727361775, 20090840604663, 306820413, 30013983, 306806589,
    612976761, 74050748247, 727361775, 30013983, 130337643044783, 6593470017953873,
    564202093, 1455047503, 1217488727, 34059989509
  ]
def negativeCoefficients : Array ℕ := #[
    640442822954483225041305600, 127022123728350357623930880000, 127022123728350357623930880000, 640442822954483225041305600, 613973755903814052813471744, 15052259822158021939943178240,
    11130750026385274118747455488, 12418114353280368100453122048, 613973755903814052813471744, 12398308748251212808426881024, 12616170403571921020715532288, 613973755903814052813471744,
    15052259822158021939943178240, 613973755903814052813471744, 15517929600187128542750834688, 3077746057937929165227845222400, 3077746057937929165227845222400, 15517929600187128542750834688,
    1121768643215166285230899200, 361345640086547520335275622400, 3843062838407757729324827934720, 361346729182317632147203031040, 1121768643215166285230899200, 992686375579448998814023680,
    196884291778943054317092864000, 196884291778943054317092864000, 992686375579448998814023680, 1961385112450908123719270400, 631804038383033545464270028800, 6719501639716003224901795184640,
    631805942640424274501283348480, 1961385112450908123719270400, 13598426577306195989794652160, 441446818818654434576302080, 517349250792060435763470270464, 4619041104224457376420331520,
    409145832075826061314621440, 517349250792060435763470270464, 409145832075826061314621440, 398378836494883270227394560, 15052259822158021939943178240, 398378836494883270227394560,
    4619041104224457376420331520, 15052259822158021939943178240, 13598426577306195989794652160, 398378836494883270227394560, 398378836494883270227394560, 441446818818654434576302080,
    1329836998958817937830445056, 13417456512424110297867878400, 45240551130360158670683111424, 11319675270401734137731874816, 553660263033669229140246528, 11319165254821584216048795648,
    11307425433298426204337995776, 1333979688846782439566082048, 13417456512424110297867878400, 553660263033669229140246528, 36686785040552089905841307648, 1855896819745975000861075570688,
    20815383230844550591677464576, 26840888902931131026110414848, 359339247353526978635274125312, 628295909625755250754053996544
  ]
def negativeScales : Array ℕ := #[
    25, 32, 32, 25, 15, 17,
    19, 20, 15, 19, 20, 15,
    17, 15, 31, 39, 39, 31,
    19, 29, 32, 28, 19, 27,
    35, 35, 27, 24, 33, 37,
    32, 24, 32, 13, 37, 16,
    12, 37, 12, 13, 17, 13,
    16, 17, 32, 13, 13, 13,
    39, 29, 44, 28, 24, 28,
    29, 36, 29, 24, 46, 52,
    29, 30, 30, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25049200243380557, 32680994548095196, 32680994548095196, 25049200243380557, 15988307476108722, 17603966754433849,
    19168537466317519, 20326432778898632, 15988307476108722, 19324129993029212, 20349260708352894, 15988307476108722,
    17603966754433849, 15988307476108722, 31647922743077386, 39279717047725830, 39279717047725830, 31647922743077386,
    19857833725028331, 29189294238909246, 32600099412909660, 28189298587185590, 19857833725028331, 27681468458926589,
    35313262763548721, 35313262763548721, 27681468458926589, 24663931394446331, 33995391932302008, 37406197084301740,
    32995396280579884, 24663931394446331, 32457426389172021, 13512370113670596, 37707053292077454, 16899651950892089,
    12402745622495697, 37707053292077454, 12402745622495697, 13364271474681056, 17603966754433849, 13364271474681056,
    16899651950892089, 17603966754433849, 32457426389172021, 13364271474681056, 13364271474681056, 13512370113670596,
    39103307984222639, 29438097869018137, 44191603161509741, 28192819228752624, 24839131449833303, 28192754225693164,
    29191257139009122, 36107795262197097, 29438097869018137, 24839131449833303, 46889247143408793, 52549959351387975,
    29071636776945673, 30438419107617326, 30181261268120171, 34987358958844556
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
noncomputable def negativeCeiling : ℝ := 532302753 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 640442822954483225041305600, coefficient := (-640442822954483225041305600) }, { argument := 127022123728350357623930880000, coefficient := (-127022123728350357623930880000) }, { argument := 127022123728350357623930880000, coefficient := (-127022123728350357623930880000) }, { argument := 640442822954483225041305600, coefficient := (-640442822954483225041305600) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 11130750026385274118747455488, coefficient := (-11130750026385274118747455488) }, { argument := 12418114353280368100453122048, coefficient := (-12418114353280368100453122048) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 12398308748251212808426881024, coefficient := (-12398308748251212808426881024) }, { argument := 12616170403571921020715532288, coefficient := (-12616170403571921020715532288) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 15517929600187128542750834688, coefficient := (-15517929600187128542750834688) }, { argument := 3077746057937929165227845222400, coefficient := (-3077746057937929165227845222400) }, { argument := 3077746057937929165227845222400, coefficient := (-3077746057937929165227845222400) }, { argument := 15517929600187128542750834688, coefficient := (-15517929600187128542750834688) }, { argument := 1121768643215166285230899200, coefficient := (-1121768643215166285230899200) }, { argument := 361345640086547520335275622400, coefficient := (-361345640086547520335275622400) }, { argument := 3843062838407757729324827934720, coefficient := (-3843062838407757729324827934720) }, { argument := 361346729182317632147203031040, coefficient := (-361346729182317632147203031040) }, { argument := 1121768643215166285230899200, coefficient := (-1121768643215166285230899200) }, { argument := 992686375579448998814023680, coefficient := (-992686375579448998814023680) }, { argument := 196884291778943054317092864000, coefficient := (-196884291778943054317092864000) }, { argument := 196884291778943054317092864000, coefficient := (-196884291778943054317092864000) }, { argument := 992686375579448998814023680, coefficient := (-992686375579448998814023680) }, { argument := 1961385112450908123719270400, coefficient := (-1961385112450908123719270400) }, { argument := 631804038383033545464270028800, coefficient := (-631804038383033545464270028800) }, { argument := 6719501639716003224901795184640, coefficient := (-6719501639716003224901795184640) }, { argument := 631805942640424274501283348480, coefficient := (-631805942640424274501283348480) }, { argument := 1961385112450908123719270400, coefficient := (-1961385112450908123719270400) }, { argument := 13598426577306195989794652160, coefficient := (-13598426577306195989794652160) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 517349250792060435763470270464, coefficient := (-517349250792060435763470270464) }, { argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 517349250792060435763470270464, coefficient := (-517349250792060435763470270464) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 13598426577306195989794652160, coefficient := (-13598426577306195989794652160) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 1329836998958817937830445056, coefficient := (-1329836998958817937830445056) }, { argument := 13417456512424110297867878400, coefficient := (-13417456512424110297867878400) }, { argument := 45240551130360158670683111424, coefficient := (-45240551130360158670683111424) }, { argument := 11319675270401734137731874816, coefficient := (-11319675270401734137731874816) }, { argument := 553660263033669229140246528, coefficient := (-553660263033669229140246528) }, { argument := 11319165254821584216048795648, coefficient := (-11319165254821584216048795648) }, { argument := 11307425433298426204337995776, coefficient := (-11307425433298426204337995776) }, { argument := 1333979688846782439566082048, coefficient := (-1333979688846782439566082048) }, { argument := 13417456512424110297867878400, coefficient := (-13417456512424110297867878400) }, { argument := 553660263033669229140246528, coefficient := (-553660263033669229140246528) }, { argument := 36686785040552089905841307648, coefficient := (-36686785040552089905841307648) }, { argument := 1855896819745975000861075570688, coefficient := (-1855896819745975000861075570688) }, { argument := 20815383230844550591677464576, coefficient := (-20815383230844550591677464576) }, { argument := 26840888902931131026110414848, coefficient := (-26840888902931131026110414848) }, { argument := 359339247353526978635274125312, coefficient := (-359339247353526978635274125312) }, { argument := 628295909625755250754053996544, coefficient := (-628295909625755250754053996544) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2074973564557871533373559266082816)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1647881167463373, 1217488727, 1098709339, 564202093, 564202093, 1098709339,
    34059989509, 1098709339, 32584227413043, 1455047503, 624760768569, 207425501181351,
    89015689125, 7394246471677269, 28169521875, 3380342625, 89015689125, 176904597375,
    28169521875, 2730190060125, 174651035625, 829702558101743, 89015689125, 3380342625,
    174651035625, 3380342625, 89015689125, 89015689125, 624760768569, 109710381,
    21759390675, 21759390675, 109710381, 950175, 612143325, 6510401685,
    306072585, 950175, 154476231874141, 34563, 2995599046279719, 361647,
    16017, 5991196405789773, 16017, 31191, 589257, 31191,
    361647, 589257, 19309599266337, 31191, 31191, 34563,
    857475, 552422025, 5875240545, 276211845, 857475, 2487691389,
    77121, 94703675267, 806949, 35739
  ]
def negativeCoefficients : Array ℕ := #[
    1855349252934726139995595210752, 359339247353526978635274125312, 20267609987927588734001741824, 20815383230844550591677464576, 20815383230844550591677464576, 20267609987927588734001741824,
    628295909625755250754053996544, 20267609987927588734001741824, 36686578608883988913645944832, 26840888902931131026110414848, 22509378916184424715797921792, 1868322819654941482883525640192,
    205256204479220691524124672000, 16650362827265676736774602227712, 129908990176721956660838400000, 7794539410603317399650304000, 205256204479220691524124672000, 203957114577453471957516288000,
    129908990176721956660838400000, 3147694831981973009892114432000, 201358934773919032824299520000, 1868324065747678540908162187264, 205256204479220691524124672000, 7794539410603317399650304000,
    201358934773919032824299520000, 7794539410603317399650304000, 205256204479220691524124672000, 205256204479220691524124672000, 22509378916184424715797921792, 1011899660268083495565262848,
    200694955490793565045810790400, 200694955490793565045810790400, 1011899660268083495565262848, 1121768643215166285230899200, 361345640086547520335275622400, 3843062838407757729324827934720,
    361346729182317632147203031040, 1121768643215166285230899200, 43481193769123734034365546496, 326438305494847095041949696, 1686372343572094461289407971328, 3415659342860717165195034624,
    302552575824492429551075328, 1686371868788642289173384921088, 302552575824492429551075328, 294590665934374207720783872, 11130750026385274118747455488, 294590665934374207720783872,
    3415659342860717165195034624, 11130750026385274118747455488, 43481352030274458073039896576, 294590665934374207720783872, 294590665934374207720783872, 326438305494847095041949696,
    63270487498416391087718400, 20380775431710759531105484800, 216758117410193652416186941440, 20380836859368524983912366080, 63270487498416391087718400, 11472451596813508210543558656,
    364193625525389908525449216, 436743615122511522079459770368, 3810708910985177335546773504, 337545311462556500584562688
  ]
def negativeScales : Array ℕ := #[
    50, 30, 30, 29, 29, 30,
    34, 30, 44, 30, 39, 47,
    36, 52, 34, 31, 36, 37,
    34, 41, 37, 49, 36, 31,
    37, 31, 36, 36, 39, 26,
    34, 34, 26, 19, 29, 32,
    28, 19, 47, 15, 51, 18,
    13, 52, 13, 14, 19, 14,
    18, 19, 44, 14, 14, 15,
    19, 29, 32, 28, 19, 31,
    16, 36, 19, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    50549533633495150, 30181261268120171, 30033162629131037, 29071636776945673, 29071636776945673, 30033162629131037,
    34987358958844556, 30033162629131037, 44889239025531992, 30438419107617326, 39184512907023271, 47559586600426737,
    36373340584143966, 52715324556949808, 34713416025840520, 31654522336711911, 36373340584143966, 37364180584858489,
    34713416025840520, 41312138525418208, 37345684241241099, 49559587562643327, 36373340584143966, 31654522336711911,
    37345684241241099, 31654522336711911, 36373340584143966, 36373340584143966, 39184512907023271, 26709124801872523,
    34340919106451587, 34340919106451587, 26709124801872523, 19857833725028331, 29189294238909246, 32600099412909660,
    28189298587185590, 19857833725028331, 47134378206713498, 15076940825560167, 51411765958771168, 18464222658441707,
    13967316348309272, 52411765552592882, 13967316348309272, 14928842193830838, 19168537466317519, 14928842193830838,
    18464222658441707, 19168537466317519, 44134383457769000, 14928842193830838, 14928842193830838, 15076940825560167,
    19709735084120070, 29041195599920112, 32452000773914906, 28041199948196456, 19709735084120070, 31212160376763956,
    16234836138141279, 36462701363866067, 19622117971033051, 15125211646966781
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
noncomputable def negativeCeiling : ℝ := 5287150341 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1855349252934726139995595210752, coefficient := (-1855349252934726139995595210752) }, { argument := 359339247353526978635274125312, coefficient := (-359339247353526978635274125312) }, { argument := 20267609987927588734001741824, coefficient := (-20267609987927588734001741824) }, { argument := 20815383230844550591677464576, coefficient := (-20815383230844550591677464576) }, { argument := 20815383230844550591677464576, coefficient := (-20815383230844550591677464576) }, { argument := 20267609987927588734001741824, coefficient := (-20267609987927588734001741824) }, { argument := 628295909625755250754053996544, coefficient := (-628295909625755250754053996544) }, { argument := 20267609987927588734001741824, coefficient := (-20267609987927588734001741824) }, { argument := 36686578608883988913645944832, coefficient := (-36686578608883988913645944832) }, { argument := 26840888902931131026110414848, coefficient := (-26840888902931131026110414848) }, { argument := 22509378916184424715797921792, coefficient := (-22509378916184424715797921792) }, { argument := 1868322819654941482883525640192, coefficient := (-1868322819654941482883525640192) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 16650362827265676736774602227712, coefficient := (-16650362827265676736774602227712) }, { argument := 129908990176721956660838400000, coefficient := (-129908990176721956660838400000) }, { argument := 7794539410603317399650304000, coefficient := (-7794539410603317399650304000) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 203957114577453471957516288000, coefficient := (-203957114577453471957516288000) }, { argument := 129908990176721956660838400000, coefficient := (-129908990176721956660838400000) }, { argument := 3147694831981973009892114432000, coefficient := (-3147694831981973009892114432000) }, { argument := 201358934773919032824299520000, coefficient := (-201358934773919032824299520000) }, { argument := 1868324065747678540908162187264, coefficient := (-1868324065747678540908162187264) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 7794539410603317399650304000, coefficient := (-7794539410603317399650304000) }, { argument := 201358934773919032824299520000, coefficient := (-201358934773919032824299520000) }, { argument := 7794539410603317399650304000, coefficient := (-7794539410603317399650304000) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 22509378916184424715797921792, coefficient := (-22509378916184424715797921792) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 1121768643215166285230899200, coefficient := (-1121768643215166285230899200) }, { argument := 361345640086547520335275622400, coefficient := (-361345640086547520335275622400) }, { argument := 3843062838407757729324827934720, coefficient := (-3843062838407757729324827934720) }, { argument := 361346729182317632147203031040, coefficient := (-361346729182317632147203031040) }, { argument := 1121768643215166285230899200, coefficient := (-1121768643215166285230899200) }, { argument := 43481193769123734034365546496, coefficient := (-43481193769123734034365546496) }, { argument := 326438305494847095041949696, coefficient := (-326438305494847095041949696) }, { argument := 1686372343572094461289407971328, coefficient := (-1686372343572094461289407971328) }, { argument := 3415659342860717165195034624, coefficient := (-3415659342860717165195034624) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 1686371868788642289173384921088, coefficient := (-1686371868788642289173384921088) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 11130750026385274118747455488, coefficient := (-11130750026385274118747455488) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 3415659342860717165195034624, coefficient := (-3415659342860717165195034624) }, { argument := 11130750026385274118747455488, coefficient := (-11130750026385274118747455488) }, { argument := 43481352030274458073039896576, coefficient := (-43481352030274458073039896576) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 326438305494847095041949696, coefficient := (-326438305494847095041949696) }, { argument := 63270487498416391087718400, coefficient := (-63270487498416391087718400) }, { argument := 20380775431710759531105484800, coefficient := (-20380775431710759531105484800) }, { argument := 216758117410193652416186941440, coefficient := (-216758117410193652416186941440) }, { argument := 20380836859368524983912366080, coefficient := (-20380836859368524983912366080) }, { argument := 63270487498416391087718400, coefficient := (-63270487498416391087718400) }, { argument := 11472451596813508210543558656, coefficient := (-11472451596813508210543558656) }, { argument := 364193625525389908525449216, coefficient := (-364193625525389908525449216) }, { argument := 436743615122511522079459770368, coefficient := (-436743615122511522079459770368) }, { argument := 3810708910985177335546773504, coefficient := (-3810708910985177335546773504) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
