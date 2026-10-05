import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 11, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-22117537190943607171146800168960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1975930179, 1783156503, 915674961, 915674961, 1783156503, 55277851593,
    1783156503, 625674915, 2361477531, 39451953, 1783156503, 4957815,
    105528983, 18508792169, 4627198597, 26381691, 5397, 1915065,
    20303, 69207027, 6425, 771, 20303, 40349,
    6425, 622711, 39835, 7660265, 20303, 771,
    39835, 771, 20303, 20303, 5397, 771,
    3075, 1527, 3075, 39835, 158875, 78895,
    158875, 20259111, 915674961, 2545905, 771, 3075,
    1527, 3075, 20259111, 915674961, 2545905, 10319869,
    1810008067, 452502071, 2579913, 20303, 80975, 40211,
    80975, 39451953, 1783156503, 4957815
  ]
def negativeCoefficients : Array ℕ := #[
    36449478319532103518612619264, 2055839478388243643580284928, 2111402707533871850163535872, 2111402707533871850163535872, 2055839478388243643580284928, 63731023830035552950988832768,
    2055839478388243643580284928, 2885416257586244360507228160, 2722598228135782122579296256, 45485005012438610375344128, 2055839478388243643580284928, 45727772234899160322539520,
    243333267719980752427810816, 42678369031877813466340261888, 42678374148543450911527141376, 243328151054343307240931328, 101946447632189900873269248, 9043638768516757111166730240,
    767025653613619254189359104, 81705236170963643446169960448, 485459274438999527967948800, 29127556466339971678076928, 767025653613619254189359104, 762171060869229258909679616,
    485459274438999527967948800, 11762678219656958562663399424, 752461875380449268350320640, 9043644671474860698223247360, 767025653613619254189359104, 29127556466339971678076928,
    752461875380449268350320640, 29127556466339971678076928, 767025653613619254189359104, 767025653613619254189359104, 101946447632189900873269248, 29127556466339971678076928,
    29042553869648318064230400, 28844214477367792965255168, 29042553869648318064230400, 752461875380449268350320640, 750265974965914883325952000, 745142207332001318269091840,
    750265974965914883325952000, 46714329472234248493596672, 2111402707533871850163535872, 46963657970977516006932480, 29127556466339971678076928, 29042553869648318064230400,
    28844214477367792965255168, 29042553869648318064230400, 46714329472234248493596672, 2111402707533871850163535872, 46963657970977516006932480, 11897998894825557295366144,
    2086797223956170689994555392, 2086797474140137189680349184, 11897748710859057609572352, 767025653613619254189359104, 764787251900739042358067200, 759564314570685214751719424,
    764787251900739042358067200, 45485005012438610375344128, 2055839478388243643580284928, 45727772234899160322539520
  ]
def negativeScales : Array ℕ := #[
    30, 30, 29, 29, 30, 35,
    30, 29, 31, 25, 30, 22,
    26, 34, 32, 24, 12, 20,
    14, 26, 12, 9, 14, 15,
    12, 19, 15, 22, 14, 9,
    15, 9, 14, 14, 12, 9,
    11, 10, 11, 15, 17, 16,
    17, 24, 29, 21, 9, 11,
    10, 11, 24, 29, 21, 23,
    30, 28, 21, 14, 16, 15,
    16, 25, 30, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30879884826111423, 30731786184240952, 29770260332253290, 29770260332253290, 30731786184240952, 35685982494529454,
    30731786184240952, 29220838022748475, 31137042662576968, 25233593384315263, 30731786184240952, 22241273007839948,
    26653064041351958, 34107491700989241, 32107491873952451, 24653033704909163, 12397941971972645, 20868961931881295,
    14309405297370982, 26044415194896637, 12649480738989629, 9590587049919383, 14309405297370982, 15300245298085506,
    12649480738989629, 19248203238645225, 15281748954468116, 22868962873556014, 14309405297370982, 9590587049919383,
    15281748954468116, 9590587049919383, 14309405297370982, 14309405297370982, 12397941971972645, 9590587049919383,
    11586370695117825, 10576484346799762, 11586370695117825, 15281748954468116, 17277532599667047, 16267646251349933,
    17277532599667047, 24272067532129899, 29770260332253290, 21279747155654583, 9590587049919383, 11586370695117825,
    10576484346799762, 11586370695117825, 24272067532129899, 29770260332253290, 21279747155654583, 23298921321576397,
    30753348981478623, 28753349154441834, 21298890985133620, 14309405297370982, 16305188942569912, 15295302594252799,
    16305188942569912, 25233593384315263, 30731786184240952, 22241273007839948
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
noncomputable def negativeCeiling : ℝ := 60562771 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 36449478319532103518612619264, coefficient := (-36449478319532103518612619264) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 63731023830035552950988832768, coefficient := (-63731023830035552950988832768) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 2885416257586244360507228160, coefficient := (-2885416257586244360507228160) }, { argument := 2722598228135782122579296256, coefficient := (-2722598228135782122579296256) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 243333267719980752427810816, coefficient := (-243333267719980752427810816) }, { argument := 42678369031877813466340261888, coefficient := (-42678369031877813466340261888) }, { argument := 42678374148543450911527141376, coefficient := (-42678374148543450911527141376) }, { argument := 243328151054343307240931328, coefficient := (-243328151054343307240931328) }, { argument := 101946447632189900873269248, coefficient := (-101946447632189900873269248) }, { argument := 9043638768516757111166730240, coefficient := (-9043638768516757111166730240) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 81705236170963643446169960448, coefficient := (-81705236170963643446169960448) }, { argument := 485459274438999527967948800, coefficient := (-485459274438999527967948800) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 762171060869229258909679616, coefficient := (-762171060869229258909679616) }, { argument := 485459274438999527967948800, coefficient := (-485459274438999527967948800) }, { argument := 11762678219656958562663399424, coefficient := (-11762678219656958562663399424) }, { argument := 752461875380449268350320640, coefficient := (-752461875380449268350320640) }, { argument := 9043644671474860698223247360, coefficient := (-9043644671474860698223247360) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 752461875380449268350320640, coefficient := (-752461875380449268350320640) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 101946447632189900873269248, coefficient := (-101946447632189900873269248) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 752461875380449268350320640, coefficient := (-752461875380449268350320640) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 745142207332001318269091840, coefficient := (-745142207332001318269091840) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 11897998894825557295366144, coefficient := (-11897998894825557295366144) }, { argument := 2086797223956170689994555392, coefficient := (-2086797223956170689994555392) }, { argument := 2086797474140137189680349184, coefficient := (-2086797474140137189680349184) }, { argument := 11897748710859057609572352, coefficient := (-11897748710859057609572352) }, { argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }] }

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

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-24155939315248101490459007778816)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    20303, 80975, 40211, 80975, 1223010543, 55277851593,
    153692265, 105528983, 18508792169, 4627198597, 26381691, 39451953,
    1783156503, 4957815, 210725067, 36959196981, 9239800353, 52680159,
    10785, 1914795, 80975, 69206955, 25625, 3075,
    80975, 160925, 25625, 2483575, 158875, 7659185,
    80975, 3075, 158875, 3075, 80975, 80975,
    10785, 5397, 10785, 2691, 10785, 15375141,
    62500473, 625674915, 26381691, 2579913, 26381691, 52680159,
    15443433, 62500473, 2579913, 61773949, 1848598627, 2545905,
    6565755, 5493795, 153692265, 461881721, 5493795, 4957815,
    2545905, 2545905, 4957815, 153692265
  ]
def negativeCoefficients : Array ℕ := #[
    767025653613619254189359104, 764787251900739042358067200, 759564314570685214751719424, 764787251900739042358067200, 1410035155385596921635667968, 63731023830035552950988832768,
    1417560939281873969998725120, 243333267719980752427810816, 42678369031877813466340261888, 42678374148543450911527141376, 243328151054343307240931328, 45485005012438610375344128,
    2055839478388243643580284928, 45727772234899160322539520, 242949461304018637676347392, 42611052992395356347308179456, 42611058100990543260247130112, 242944352708831724737396736,
    101861445035498247259422720, 9042363729566382306959032320, 764787251900739042358067200, 81705151168366951792556113920, 484042564494138634403840000, 29042553869648318064230400,
    764787251900739042358067200, 759946826255797656014028800, 484042564494138634403840000, 11728351337692979111605043200, 750265974965914883325952000, 9042369632524485894015549440,
    764787251900739042358067200, 29042553869648318064230400, 750265974965914883325952000, 29042553869648318064230400, 764787251900739042358067200, 764787251900739042358067200,
    101861445035498247259422720, 101946447632189900873269248, 101861445035498247259422720, 101663105643217722160447488, 101861445035498247259422720, 70905322781049687285694464,
    288232557479198460154478592, 2885416257586244360507228160, 243328151054343307240931328, 11897748710859057609572352, 243328151054343307240931328, 242944352708831724737396736,
    71220264042620130460434432, 288232557479198460154478592, 11897748710859057609572352, 71220514226586630146228224, 2131289110454991494632701952, 46963657970977516006932480,
    60558401067839428535255040, 810741042867401328961781760, 1417560939281873969998725120, 2130053474902879638634102784, 810741042867401328961781760, 45727772234899160322539520,
    46963657970977516006932480, 46963657970977516006932480, 45727772234899160322539520, 1417560939281873969998725120
  ]
def negativeScales : Array ℕ := #[
    14, 16, 15, 16, 30, 35,
    27, 26, 34, 32, 24, 25,
    30, 22, 27, 35, 33, 25,
    13, 20, 16, 26, 14, 11,
    16, 17, 14, 21, 17, 22,
    16, 11, 17, 11, 16, 16,
    13, 12, 13, 11, 13, 23,
    25, 29, 24, 21, 24, 25,
    23, 25, 21, 25, 30, 21,
    22, 22, 27, 28, 22, 22,
    21, 21, 22, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14309405297370982, 16305188942569912, 15295302594252799, 16305188942569912, 30187789694702138, 35685982494529454,
    27195469318226823, 26653064041351958, 34107491700989241, 32107491873952451, 24653033704909163, 25233593384315263,
    30731786184240952, 22241273007839948, 27650786700639600, 35105214360278175, 33105214533241385, 25650756364196806,
    13396738556047823, 20868758515735728, 16305188942569912, 26044413693978284, 14645264384186412, 11586370695117825,
    16305188942569912, 17296028943284436, 14645264384186412, 21243986883844155, 17277532599667047, 22868759457543230,
    16305188942569912, 11586370695117825, 17277532599667047, 11586370695117825, 16305188942569912, 16305188942569912,
    13396738556047823, 12397941971972645, 13396738556047823, 11393926675640423, 13396738556047823, 23874096307896467,
    25897363776426689, 29220838022748475, 24653033704909163, 21298890985133620, 24653033704909163, 25650756364196806,
    23880490159620450, 25897363776426689, 21298890985133620, 25880495227539798, 30783784871134843, 21279747155654583,
    22646529486345706, 22389371646829086, 27195469318226823, 28782948212117327, 22389371646829086, 22241273007839948,
    21279747155654583, 21279747155654583, 22241273007839948, 27195469318226823
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
noncomputable def negativeCeiling : ℝ := 138344863 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 767025653613619254189359104, coefficient := (-767025653613619254189359104) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 759564314570685214751719424, coefficient := (-759564314570685214751719424) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 1410035155385596921635667968, coefficient := (-1410035155385596921635667968) }, { argument := 63731023830035552950988832768, coefficient := (-63731023830035552950988832768) }, { argument := 1417560939281873969998725120, coefficient := (-1417560939281873969998725120) }, { argument := 243333267719980752427810816, coefficient := (-243333267719980752427810816) }, { argument := 42678369031877813466340261888, coefficient := (-42678369031877813466340261888) }, { argument := 42678374148543450911527141376, coefficient := (-42678374148543450911527141376) }, { argument := 243328151054343307240931328, coefficient := (-243328151054343307240931328) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 242949461304018637676347392, coefficient := (-242949461304018637676347392) }, { argument := 42611052992395356347308179456, coefficient := (-42611052992395356347308179456) }, { argument := 42611058100990543260247130112, coefficient := (-42611058100990543260247130112) }, { argument := 242944352708831724737396736, coefficient := (-242944352708831724737396736) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 9042363729566382306959032320, coefficient := (-9042363729566382306959032320) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 81705151168366951792556113920, coefficient := (-81705151168366951792556113920) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 759946826255797656014028800, coefficient := (-759946826255797656014028800) }, { argument := 484042564494138634403840000, coefficient := (-484042564494138634403840000) }, { argument := 11728351337692979111605043200, coefficient := (-11728351337692979111605043200) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 9042369632524485894015549440, coefficient := (-9042369632524485894015549440) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 750265974965914883325952000, coefficient := (-750265974965914883325952000) }, { argument := 29042553869648318064230400, coefficient := (-29042553869648318064230400) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 764787251900739042358067200, coefficient := (-764787251900739042358067200) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 101946447632189900873269248, coefficient := (-101946447632189900873269248) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }, { argument := 101861445035498247259422720, coefficient := (-101861445035498247259422720) }, { argument := 70905322781049687285694464, coefficient := (-70905322781049687285694464) }, { argument := 288232557479198460154478592, coefficient := (-288232557479198460154478592) }, { argument := 2885416257586244360507228160, coefficient := (-2885416257586244360507228160) }, { argument := 243328151054343307240931328, coefficient := (-243328151054343307240931328) }, { argument := 11897748710859057609572352, coefficient := (-11897748710859057609572352) }, { argument := 243328151054343307240931328, coefficient := (-243328151054343307240931328) }, { argument := 242944352708831724737396736, coefficient := (-242944352708831724737396736) }, { argument := 71220264042620130460434432, coefficient := (-71220264042620130460434432) }, { argument := 288232557479198460154478592, coefficient := (-288232557479198460154478592) }, { argument := 11897748710859057609572352, coefficient := (-11897748710859057609572352) }, { argument := 71220514226586630146228224, coefficient := (-71220514226586630146228224) }, { argument := 2131289110454991494632701952, coefficient := (-2131289110454991494632701952) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 60558401067839428535255040, coefficient := (-60558401067839428535255040) }, { argument := 810741042867401328961781760, coefficient := (-810741042867401328961781760) }, { argument := 1417560939281873969998725120, coefficient := (-1417560939281873969998725120) }, { argument := 2130053474902879638634102784, coefficient := (-2130053474902879638634102784) }, { argument := 810741042867401328961781760, coefficient := (-810741042867401328961781760) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 1417560939281873969998725120, coefficient := (-1417560939281873969998725120) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
