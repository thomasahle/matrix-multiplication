import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-38414431800294441232254057735782400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4453385, 21827773, 5469, 14239124517, 1705, 89,
    2717, 11357, 1705, 173993, 11145, 1396978807,
    2717, 89, 11145, 89, 2717, 5679,
    4453385, 15258988186097827, 2075738891, 598826648773847863, 23409314099, 2074236683,
    37426670296840651, 2074236683, 2073735947, 85903110227, 533114049, 23409314099,
    85903110227, 7629555644452795, 2073735947, 533114049, 2075738891, 11673546346050831,
    325284771, 8440523, 340572801841251211, 523961697, 93391806286140413, 523961697,
    546036911, 325284771, 16231775, 4815, 21935, 535,
    229515, 10165, 535, 10165, 19795, 373965,
    19795, 229515, 373965, 4815, 19795, 19795,
    21935, 325284771, 38019474675, 10409109165
  ]
def negativeCoefficients : Array ℕ := #[
    42061032118628869899991121920, 6597039591096768276165937856512, 211571689839117022606978449408, 67242364364488225677430417784832, 131917985436348335543937925120, 6886041468524927779126378496,
    210217692921148637931307532288, 219676328533813496594208653312, 131917985436348335543937925120, 3365514082115330783914426892288, 215575652153680674433605304320, 6597045895456022907142298140672,
    210217692921148637931307532288, 6886041468524927779126378496, 215575652153680674433605304320, 6886041468524927779126378496, 210217692921148637931307532288, 219695671346927330661003952128,
    42061032118628869899991121920, 4295023344310060896856689344512, 19145312043061343463751548928, 168554717017339007576603914928128, 215912813062666850937698516992, 19131456619800603924694564864,
    168554738402569966760335450832896, 19131456619800603924694564864, 19126838145380357411675570176, 792316344746565312625996988416, 19668436848004107023960506368, 215912813062666850937698516992,
    792316344746565312625996988416, 4295057994670009003644330967040, 19126838145380357411675570176, 19668436848004107023960506368, 19145312043061343463751548928, 52572978974166737641666485682176,
    12000889843424437235846479872, 622800670517036662938140672, 191725442933098090982984313208832, 19330774657971099499656904704, 52574912998714938739776978681856, 19330774657971099499656904704,
    20145206304031839751191396352, 12000889843424437235846479872, 598846798574073714363596800, 181905556920138733631569920, 207170217603491335524843520, 161693828373456652116951040,
    2167707886631653242442874880, 192011421193479774388879360, 161693828373456652116951040, 192011421193479774388879360, 186958489056809254010224640, 7063999127065387489359298560,
    186958489056809254010224640, 2167707886631653242442874880, 7063999127065387489359298560, 181905556920138733631569920, 186958489056809254010224640, 186958489056809254010224640,
    207170217603491335524843520, 12000889843424437235846479872, 43833469946662914435632332800, 12000885800128720579634135040
  ]
def negativeScales : Array ℕ := #[
    22, 24, 12, 33, 10, 6,
    11, 13, 10, 17, 13, 30,
    11, 6, 13, 6, 11, 12,
    22, 53, 30, 59, 34, 30,
    55, 30, 30, 36, 28, 34,
    36, 52, 30, 28, 30, 53,
    28, 23, 58, 28, 56, 28,
    29, 28, 23, 12, 14, 9,
    17, 13, 9, 13, 14, 18,
    14, 17, 18, 12, 14, 14,
    14, 28, 35, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22086470909059394, 24379661609668544, 12417061346760304, 33729141394911448, 10735556024075001, 6475733430966516,
    11407798850221984, 13471294170667373, 10735556024075001, 17408669739887666, 13444108996147153, 30379662988357176,
    11407798850221984, 6475733430966516, 13444108996147153, 6475733430966516, 11407798850221984, 12471421196424963,
    22086470909059394, 53760508819624186, 30950977841829076, 59054916038219645, 34446363612479160, 30949933388206536,
    55054916221260293, 30949933388206536, 30949585068900397, 36321991315718589, 28989868980738031, 34446363612479160,
    36321991315718589, 52760520458606588, 30949585068900397, 28989868980738031, 30950977841829076, 53374092427026584,
    28277128039771587, 23008900964717471, 58240740839013223, 28964886123228136, 56374145499086757, 28964886123228136,
    29024423236831523, 28277128039771587, 23952317447190580, 12233320082730822, 14420947085906609, 9063395081288510,
    17808228919551386, 13311322594732096, 9063395081288510, 13311322594732096, 14272848446917460, 18512543726664356,
    14272848446917460, 17808228919551386, 18512543726664356, 12233320082730822, 14272848446917460, 14272848446917460,
    14420947085906609, 28277128039771587, 35146019546904059, 33277127553703992
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
noncomputable def negativeCeiling : ℝ := 237272091481 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 42061032118628869899991121920, coefficient := (-42061032118628869899991121920) }, { argument := 6597039591096768276165937856512, coefficient := (-6597039591096768276165937856512) }, { argument := 211571689839117022606978449408, coefficient := (-211571689839117022606978449408) }, { argument := 67242364364488225677430417784832, coefficient := (-67242364364488225677430417784832) }, { argument := 131917985436348335543937925120, coefficient := (-131917985436348335543937925120) }, { argument := 6886041468524927779126378496, coefficient := (-6886041468524927779126378496) }, { argument := 210217692921148637931307532288, coefficient := (-210217692921148637931307532288) }, { argument := 219676328533813496594208653312, coefficient := (-219676328533813496594208653312) }, { argument := 131917985436348335543937925120, coefficient := (-131917985436348335543937925120) }, { argument := 3365514082115330783914426892288, coefficient := (-3365514082115330783914426892288) }, { argument := 215575652153680674433605304320, coefficient := (-215575652153680674433605304320) }, { argument := 6597045895456022907142298140672, coefficient := (-6597045895456022907142298140672) }, { argument := 210217692921148637931307532288, coefficient := (-210217692921148637931307532288) }, { argument := 6886041468524927779126378496, coefficient := (-6886041468524927779126378496) }, { argument := 215575652153680674433605304320, coefficient := (-215575652153680674433605304320) }, { argument := 6886041468524927779126378496, coefficient := (-6886041468524927779126378496) }, { argument := 210217692921148637931307532288, coefficient := (-210217692921148637931307532288) }, { argument := 219695671346927330661003952128, coefficient := (-219695671346927330661003952128) }, { argument := 42061032118628869899991121920, coefficient := (-42061032118628869899991121920) }, { argument := 4295023344310060896856689344512, coefficient := (-4295023344310060896856689344512) }, { argument := 19145312043061343463751548928, coefficient := (-19145312043061343463751548928) }, { argument := 168554717017339007576603914928128, coefficient := (-168554717017339007576603914928128) }, { argument := 215912813062666850937698516992, coefficient := (-215912813062666850937698516992) }, { argument := 19131456619800603924694564864, coefficient := (-19131456619800603924694564864) }, { argument := 168554738402569966760335450832896, coefficient := (-168554738402569966760335450832896) }, { argument := 19131456619800603924694564864, coefficient := (-19131456619800603924694564864) }, { argument := 19126838145380357411675570176, coefficient := (-19126838145380357411675570176) }, { argument := 792316344746565312625996988416, coefficient := (-792316344746565312625996988416) }, { argument := 19668436848004107023960506368, coefficient := (-19668436848004107023960506368) }, { argument := 215912813062666850937698516992, coefficient := (-215912813062666850937698516992) }, { argument := 792316344746565312625996988416, coefficient := (-792316344746565312625996988416) }, { argument := 4295057994670009003644330967040, coefficient := (-4295057994670009003644330967040) }, { argument := 19126838145380357411675570176, coefficient := (-19126838145380357411675570176) }, { argument := 19668436848004107023960506368, coefficient := (-19668436848004107023960506368) }, { argument := 19145312043061343463751548928, coefficient := (-19145312043061343463751548928) }, { argument := 52572978974166737641666485682176, coefficient := (-52572978974166737641666485682176) }, { argument := 12000889843424437235846479872, coefficient := (-12000889843424437235846479872) }, { argument := 622800670517036662938140672, coefficient := (-622800670517036662938140672) }, { argument := 191725442933098090982984313208832, coefficient := (-191725442933098090982984313208832) }, { argument := 19330774657971099499656904704, coefficient := (-19330774657971099499656904704) }, { argument := 52574912998714938739776978681856, coefficient := (-52574912998714938739776978681856) }, { argument := 19330774657971099499656904704, coefficient := (-19330774657971099499656904704) }, { argument := 20145206304031839751191396352, coefficient := (-20145206304031839751191396352) }, { argument := 12000889843424437235846479872, coefficient := (-12000889843424437235846479872) }, { argument := 598846798574073714363596800, coefficient := (-598846798574073714363596800) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 12000889843424437235846479872, coefficient := (-12000889843424437235846479872) }, { argument := 43833469946662914435632332800, coefficient := (-43833469946662914435632332800) }, { argument := 12000885800128720579634135040, coefficient := (-12000885800128720579634135040) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-103024499915313606755954659279503360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1901906675527927, 4815, 1901906959372041, 4815, 8440523, 986533275,
    270096645, 2075738891, 21935, 2075739381, 21935, 4412491,
    15258990468999005, 2075739381, 598826736629322953, 23409319629, 2074237173, 37426675787810357,
    2074237173, 2073736437, 85903130541, 533114175, 23409319629, 85903130541,
    7629556785918021, 2073736437, 533114175, 2075739381, 170289748043650491, 38019474675,
    986533275, 1241684920847592845, 61240950225, 340593410550499069, 61240950225, 63821114175,
    38019474675, 1897179375, 597111165504928757, 535, 597111252886012939, 535,
    523961697, 61240950225, 16766768655, 23409314099, 229515, 23409319629,
    229515, 87074705, 2074236683, 10165, 2074237173, 10165,
    2619, 46695889883551241, 10409109165, 270096645, 42573327405645277, 16766768655,
    46697605064876675, 16766768655, 17473175265, 10409109165
  ]
def negativeCoefficients : Array ℕ := #[
    4282713097600515440469811920896, 181905556920138733631569920, 4282713736760638461324105351168, 181905556920138733631569920, 622800670517036662938140672, 2274790855515440669314252800,
    622800460685322824491991040, 19145312043061343463751548928, 207170217603491335524843520, 19145316562513641522591694848, 207170217603491335524843520, 41674799208727927357253353472,
    4295023986889616807135836897280, 19145316562513641522591694848, 168554741746456812437972260487168, 215912864067914214744608735232, 19131461139252901983534710784, 168554763131699088604617425027072,
    19131461139252901983534710784, 19126842664832655470515716096, 792316532110144869293912752128, 19668441496583613598767513600, 215912864067914214744608735232, 792316532110144869293912752128,
    4295058637257804812391706263552, 19126842664832655470515716096, 19668441496583613598767513600, 19145316562513641522591694848, 191729211458600000369286797328384, 43833469946662914435632332800,
    2274790855515440669314252800, 699006468355097869628027321712640, 70606008476960023851407769600, 191737044605009246005945620758528, 70606008476960023851407769600, 73580734980326369342049484800,
    43833469946662914435632332800, 2187298899534077566648320000, 168071851404172482191355482734592, 161693828373456652116951040, 168071875999761117271676875177984, 161693828373456652116951040,
    19330774657971099499656904704, 70606008476960023851407769600, 19330768145117519975578337280, 215912813062666850937698516992, 2167707886631653242442874880, 215912864067914214744608735232,
    2167707886631653242442874880, 6579178694364190566995858554880, 19131456619800603924694564864, 192011421193479774388879360, 19131461139252901983534710784, 192011421193479774388879360,
    202635310180525683747550396416, 52574898069823770705320826896384, 12000885800128720579634135040, 622800460685322824491991040, 191733221439986194701993631547392, 19330768145117519975578337280,
    52576829192318295054279193395200, 19330768145117519975578337280, 20145199516782942130683248640, 12000885800128720579634135040
  ]
def negativeScales : Array ℕ := #[
    50, 12, 50, 12, 23, 29,
    28, 30, 14, 30, 14, 22,
    53, 30, 59, 34, 30, 55,
    30, 30, 36, 28, 34, 36,
    52, 30, 28, 30, 57, 35,
    29, 60, 35, 58, 35, 35,
    35, 30, 59, 9, 59, 9,
    28, 35, 33, 34, 17, 34,
    17, 26, 30, 13, 30, 13,
    11, 55, 33, 28, 55, 33,
    55, 33, 34, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    50756367880042556, 12233320082730822, 50756368095353051, 12233320082730822, 23008900964717471, 29877792474767005,
    28008900478649876, 30950977841829076, 14420947085906609, 30950978182392437, 14420947085906609, 22073161905097543,
    53760509035466151, 30950978182392437, 59054916249881315, 34446363953288062, 30949933729016539, 55054916432922034,
    30949933729016539, 30949585409792694, 36321991656880900, 28989869321715000, 34446363953288062, 36321991656880900,
    52760520674449579, 30949585409792694, 28989869321715000, 30950978182392437, 57240769196123984, 35146019546904059,
    29877792474767005, 60107004842240435, 35833777618253350, 58240828136598157, 35833777618253350, 35893314747836377,
    35146019546904059, 30821208944473030, 59050777159303542, 9063395081288510, 59050777370427123, 9063395081288510,
    28964886123228136, 35833777618253350, 33964885637160433, 34446363612479160, 17808228919551386, 34446363953288062,
    17808228919551386, 26375750344331800, 30949933388206536, 13311322594732096, 30949933729016539, 13311322594732096,
    11354800344350598, 55374145089426730, 33277127553703992, 28008900478649876, 55240799369511330, 33964885637160433,
    55374198079918071, 33964885637160433, 34024422750763928, 33277127553703992
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
noncomputable def negativeCeiling : ℝ := 45453219603 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4282713097600515440469811920896, coefficient := (-4282713097600515440469811920896) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 4282713736760638461324105351168, coefficient := (-4282713736760638461324105351168) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 622800670517036662938140672, coefficient := (-622800670517036662938140672) }, { argument := 2274790855515440669314252800, coefficient := (-2274790855515440669314252800) }, { argument := 622800460685322824491991040, coefficient := (-622800460685322824491991040) }, { argument := 19145312043061343463751548928, coefficient := (-19145312043061343463751548928) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 19145316562513641522591694848, coefficient := (-19145316562513641522591694848) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 41674799208727927357253353472, coefficient := (-41674799208727927357253353472) }, { argument := 4295023986889616807135836897280, coefficient := (-4295023986889616807135836897280) }, { argument := 19145316562513641522591694848, coefficient := (-19145316562513641522591694848) }, { argument := 168554741746456812437972260487168, coefficient := (-168554741746456812437972260487168) }, { argument := 215912864067914214744608735232, coefficient := (-215912864067914214744608735232) }, { argument := 19131461139252901983534710784, coefficient := (-19131461139252901983534710784) }, { argument := 168554763131699088604617425027072, coefficient := (-168554763131699088604617425027072) }, { argument := 19131461139252901983534710784, coefficient := (-19131461139252901983534710784) }, { argument := 19126842664832655470515716096, coefficient := (-19126842664832655470515716096) }, { argument := 792316532110144869293912752128, coefficient := (-792316532110144869293912752128) }, { argument := 19668441496583613598767513600, coefficient := (-19668441496583613598767513600) }, { argument := 215912864067914214744608735232, coefficient := (-215912864067914214744608735232) }, { argument := 792316532110144869293912752128, coefficient := (-792316532110144869293912752128) }, { argument := 4295058637257804812391706263552, coefficient := (-4295058637257804812391706263552) }, { argument := 19126842664832655470515716096, coefficient := (-19126842664832655470515716096) }, { argument := 19668441496583613598767513600, coefficient := (-19668441496583613598767513600) }, { argument := 19145316562513641522591694848, coefficient := (-19145316562513641522591694848) }, { argument := 191729211458600000369286797328384, coefficient := (-191729211458600000369286797328384) }, { argument := 43833469946662914435632332800, coefficient := (-43833469946662914435632332800) }, { argument := 2274790855515440669314252800, coefficient := (-2274790855515440669314252800) }, { argument := 699006468355097869628027321712640, coefficient := (-699006468355097869628027321712640) }, { argument := 70606008476960023851407769600, coefficient := (-70606008476960023851407769600) }, { argument := 191737044605009246005945620758528, coefficient := (-191737044605009246005945620758528) }, { argument := 70606008476960023851407769600, coefficient := (-70606008476960023851407769600) }, { argument := 73580734980326369342049484800, coefficient := (-73580734980326369342049484800) }, { argument := 43833469946662914435632332800, coefficient := (-43833469946662914435632332800) }, { argument := 2187298899534077566648320000, coefficient := (-2187298899534077566648320000) }, { argument := 168071851404172482191355482734592, coefficient := (-168071851404172482191355482734592) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 168071875999761117271676875177984, coefficient := (-168071875999761117271676875177984) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 19330774657971099499656904704, coefficient := (-19330774657971099499656904704) }, { argument := 70606008476960023851407769600, coefficient := (-70606008476960023851407769600) }, { argument := 19330768145117519975578337280, coefficient := (-19330768145117519975578337280) }, { argument := 215912813062666850937698516992, coefficient := (-215912813062666850937698516992) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 215912864067914214744608735232, coefficient := (-215912864067914214744608735232) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 6579178694364190566995858554880, coefficient := (-6579178694364190566995858554880) }, { argument := 19131456619800603924694564864, coefficient := (-19131456619800603924694564864) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 19131461139252901983534710784, coefficient := (-19131461139252901983534710784) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 202635310180525683747550396416, coefficient := (-202635310180525683747550396416) }, { argument := 52574898069823770705320826896384, coefficient := (-52574898069823770705320826896384) }, { argument := 12000885800128720579634135040, coefficient := (-12000885800128720579634135040) }, { argument := 622800460685322824491991040, coefficient := (-622800460685322824491991040) }, { argument := 191733221439986194701993631547392, coefficient := (-191733221439986194701993631547392) }, { argument := 19330768145117519975578337280, coefficient := (-19330768145117519975578337280) }, { argument := 52576829192318295054279193395200, coefficient := (-52576829192318295054279193395200) }, { argument := 19330768145117519975578337280, coefficient := (-19330768145117519975578337280) }, { argument := 20145199516782942130683248640, coefficient := (-20145199516782942130683248640) }, { argument := 12000885800128720579634135040, coefficient := (-12000885800128720579634135040) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12
