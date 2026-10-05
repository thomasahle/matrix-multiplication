import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 18, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2543795175956686021900222079172608)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    92128617, 7747025559, 3873511845, 46065243, 85819279, 13700807003,
    546853802417, 13700807003, 343237947, 22351791, 825421905, 6603373623,
    178815945, 221293191, 35328836787, 1410114654393, 35328836787, 885071763,
    8367020431, 308982933105, 2471862859543, 66936768745, 45075674205, 161255248335,
    11268914805, 335276865, 12381328575, 99050604345, 2682239175, 3167479809,
    11331449883, 791869689, 371, 371, 336976963, 2727307859,
    5464336605, 29443222693, 180142965, 420333585, 5464336605, 5464336605,
    180142965, 67433516565, 2702144475, 2727307859, 5464336605, 420333585,
    2702144475, 420333585, 5464336605, 5464336605, 198510213, 332055611,
    1668134203, 94993352933, 26251164563, 790168833, 94993330295, 790168833,
    790168833, 67691130027, 790168833, 26251164563
  ]
def negativeCoefficients : Array ℕ := #[
    424868254915951762518048768, 35726849454839919077895438336, 35726840835598750637107445760, 424876874157120203306041344, 791543138151638287549202432, 126367640193814286484241383424,
    1260959017365166102957715881984, 126367640193814286484241383424, 791452820586810396370796544, 13194168581313423757585416192, 487243092299801552370385551360, 487242972986260883617005699072,
    13194287894854092510965268480, 4082138859631525884283846656, 651702010631644246684616097792, 6503006036043766323614708662272, 651702010631644246684616097792, 4081673074731978699678154752,
    308688569100311976661842132992, 11399458180264107152332145295360, 11399455388824395256289529167872, 308691360540023872704458260480, 103937428251193281804930908160, 371829287072277911312447569920,
    103937393698135788737727037440, 24739066089962669545472655360, 913580798062127910694472908800, 913580574349239156781885685760, 24739289802851423458059878400, 233718757581061649896493285376,
    836113423903068168140422643712, 233718679883375611431861878784, 7176183665232438781055860736, 7176183665232438781055860736, 777015974399611605956427776, 25154975042594867702841475072,
    25199804721259480258361425920, 135782898430752083707766505472, 13292204688136868707707125760, 969223258509980009936977920, 25199804721259480258361425920, 25199804721259480258361425920,
    13292204688136868707707125760, 310982205516202157474064629760, 24922883790256628826950860800, 25154975042594867702841475072, 25199804721259480258361425920, 969223258509980009936977920,
    24922883790256628826950860800, 969223258509980009936977920, 25199804721259480258361425920, 25199804721259480258361425920, 915466773807142697856663552, 24501379497425016793547669504,
    15385822361671228069221761024, 438079517564654400797967122432, 121062128582623610334139645952, 14576042237372742381367984128, 438079413165306315638759751680, 14576042237372742381367984128,
    14576042237372742381367984128, 624340475834132465335261986816, 14576042237372742381367984128, 121062128582623610334139645952
  ]
def negativeScales : Array ℕ := #[
    26, 32, 31, 25, 26, 33,
    38, 33, 28, 24, 29, 32,
    27, 27, 35, 40, 35, 29,
    32, 38, 41, 35, 35, 37,
    33, 28, 33, 36, 31, 31,
    33, 29, 8, 8, 28, 31,
    32, 34, 27, 28, 32, 32,
    27, 35, 31, 31, 32, 28,
    31, 28, 32, 32, 27, 28,
    30, 36, 34, 29, 36, 29,
    29, 35, 29, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26457146020216069, 32850995355174355, 31850995007118521, 25457175287665954, 26354798444725779, 33673541822020179,
    38992364254733428, 33673541822020179, 28354633819285892, 24413887100241872, 29620556484121458, 32620556130841797,
    27413900146329171, 27721383820561463, 35040127197698756, 40358949609498899, 35040127197698756, 29721219195121131,
    32962066824682974, 38168736195791014, 41168735842511353, 35962079870773045, 35391630019342910, 37230555160102510,
    33391629539731919, 28320777695850379, 33527447079720749, 36527446726441088, 31320790741937678, 31560688276969518,
    33399613417727297, 29560687797358527, 8535275376621650, 8535275376621650, 28328074725871975, 31344830415106315,
    32347399210858556, 34777216538767841, 27424567071381033, 28646959492737179, 32347399210858556, 32347399210858556,
    27424567071381033, 35972746798289042, 31331457666989534, 31344830415106315, 32347399210858556, 28646959492737179,
    31331457666989534, 28646959492737179, 32347399210858556, 32347399210858556, 27564637992491462, 28306849636199141,
    30635588213655331, 36467107514674095, 34611662374402932, 29557585701641027, 36467107170863363, 29557585701641027,
    29557585701641027, 35978247766777855, 29557585701641027, 34611662374402932
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
noncomputable def negativeCeiling : ℝ := 185899083 / 10000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 424868254915951762518048768, coefficient := (-424868254915951762518048768) }, { argument := 35726849454839919077895438336, coefficient := (-35726849454839919077895438336) }, { argument := 35726840835598750637107445760, coefficient := (-35726840835598750637107445760) }, { argument := 424876874157120203306041344, coefficient := (-424876874157120203306041344) }, { argument := 791543138151638287549202432, coefficient := (-791543138151638287549202432) }, { argument := 126367640193814286484241383424, coefficient := (-126367640193814286484241383424) }, { argument := 1260959017365166102957715881984, coefficient := (-1260959017365166102957715881984) }, { argument := 126367640193814286484241383424, coefficient := (-126367640193814286484241383424) }, { argument := 791452820586810396370796544, coefficient := (-791452820586810396370796544) }, { argument := 13194168581313423757585416192, coefficient := (-13194168581313423757585416192) }, { argument := 487243092299801552370385551360, coefficient := (-487243092299801552370385551360) }, { argument := 487242972986260883617005699072, coefficient := (-487242972986260883617005699072) }, { argument := 13194287894854092510965268480, coefficient := (-13194287894854092510965268480) }, { argument := 4082138859631525884283846656, coefficient := (-4082138859631525884283846656) }, { argument := 651702010631644246684616097792, coefficient := (-651702010631644246684616097792) }, { argument := 6503006036043766323614708662272, coefficient := (-6503006036043766323614708662272) }, { argument := 651702010631644246684616097792, coefficient := (-651702010631644246684616097792) }, { argument := 4081673074731978699678154752, coefficient := (-4081673074731978699678154752) }, { argument := 308688569100311976661842132992, coefficient := (-308688569100311976661842132992) }, { argument := 11399458180264107152332145295360, coefficient := (-11399458180264107152332145295360) }, { argument := 11399455388824395256289529167872, coefficient := (-11399455388824395256289529167872) }, { argument := 308691360540023872704458260480, coefficient := (-308691360540023872704458260480) }, { argument := 103937428251193281804930908160, coefficient := (-103937428251193281804930908160) }, { argument := 371829287072277911312447569920, coefficient := (-371829287072277911312447569920) }, { argument := 103937393698135788737727037440, coefficient := (-103937393698135788737727037440) }, { argument := 24739066089962669545472655360, coefficient := (-24739066089962669545472655360) }, { argument := 913580798062127910694472908800, coefficient := (-913580798062127910694472908800) }, { argument := 913580574349239156781885685760, coefficient := (-913580574349239156781885685760) }, { argument := 24739289802851423458059878400, coefficient := (-24739289802851423458059878400) }, { argument := 233718757581061649896493285376, coefficient := (-233718757581061649896493285376) }, { argument := 836113423903068168140422643712, coefficient := (-836113423903068168140422643712) }, { argument := 233718679883375611431861878784, coefficient := (-233718679883375611431861878784) }, { argument := 7176183665232438781055860736, coefficient := (-7176183665232438781055860736) }, { argument := 7176183665232438781055860736, coefficient := (-7176183665232438781055860736) }, { argument := 777015974399611605956427776, coefficient := (-777015974399611605956427776) }, { argument := 25154975042594867702841475072, coefficient := (-25154975042594867702841475072) }, { argument := 25199804721259480258361425920, coefficient := (-25199804721259480258361425920) }, { argument := 135782898430752083707766505472, coefficient := (-135782898430752083707766505472) }, { argument := 13292204688136868707707125760, coefficient := (-13292204688136868707707125760) }, { argument := 969223258509980009936977920, coefficient := (-969223258509980009936977920) }, { argument := 25199804721259480258361425920, coefficient := (-25199804721259480258361425920) }, { argument := 25199804721259480258361425920, coefficient := (-25199804721259480258361425920) }, { argument := 13292204688136868707707125760, coefficient := (-13292204688136868707707125760) }, { argument := 310982205516202157474064629760, coefficient := (-310982205516202157474064629760) }, { argument := 24922883790256628826950860800, coefficient := (-24922883790256628826950860800) }, { argument := 25154975042594867702841475072, coefficient := (-25154975042594867702841475072) }, { argument := 25199804721259480258361425920, coefficient := (-25199804721259480258361425920) }, { argument := 969223258509980009936977920, coefficient := (-969223258509980009936977920) }, { argument := 24922883790256628826950860800, coefficient := (-24922883790256628826950860800) }, { argument := 969223258509980009936977920, coefficient := (-969223258509980009936977920) }, { argument := 25199804721259480258361425920, coefficient := (-25199804721259480258361425920) }, { argument := 25199804721259480258361425920, coefficient := (-25199804721259480258361425920) }, { argument := 915466773807142697856663552, coefficient := (-915466773807142697856663552) }, { argument := 24501379497425016793547669504, coefficient := (-24501379497425016793547669504) }, { argument := 15385822361671228069221761024, coefficient := (-15385822361671228069221761024) }, { argument := 438079517564654400797967122432, coefficient := (-438079517564654400797967122432) }, { argument := 121062128582623610334139645952, coefficient := (-121062128582623610334139645952) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 438079413165306315638759751680, coefficient := (-438079413165306315638759751680) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 624340475834132465335261986816, coefficient := (-624340475834132465335261986816) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 121062128582623610334139645952, coefficient := (-121062128582623610334139645952) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-380044055833395734771420853436416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    67691130027, 2656456207, 790168833, 790168833, 1668134203, 3588711885,
    1660076505, 93262725, 21982528395, 5042404665, 897177735, 5042404665,
    5042404665, 1660076505, 93262725, 678004327, 25037797785, 200302333231,
    5424083665, 45075674205, 161255248335, 11268914805, 555, 555,
    406087155, 1452749985, 101521755, 161, 161, 5175765,
    435226155, 217613025, 2587935, 2583189, 412398873, 16460482347,
    412398873, 10331577, 52154179, 1925984445, 15407871787, 417237205,
    2583189, 412398873, 16460482347, 412398873, 10331577, 335276865,
    12381328575, 99050604345, 2682239175, 3167479809, 11331449883, 791869689,
    52154179, 1925984445, 15407871787, 417237205, 3167479809, 11331449883,
    791869689, 31, 31, 5453399
  ]
def negativeCoefficients : Array ℕ := #[
    624340475834132465335261986816, 24501483896773101952755040256, 14576042237372742381367984128, 14576042237372742381367984128, 15385822361671228069221761024, 8275006212109347990295019520,
    30623006430513214831806382080, 1720393619691753642236313600, 50688259424452273922679767040, 46507974185667073461788344320, 8275004033087704283354234880, 46507974185667073461788344320,
    46507974185667073461788344320, 30623006430513214831806382080, 1720393619691753642236313600, 25013944602073365873755684864, 923731695818373776368855941120, 923731469619786258523906637824,
    25014170800660883718704988160, 103937428251193281804930908160, 371829287072277911312447569920, 103937393698135788737727037440, 5367630639088953535695421440, 5367630639088953535695421440,
    7490985819905822112067092480, 26798507176380390004500725760, 7490983329595372161277624320, 6228385822654569508086218752, 6228385822654569508086218752, 23869003085165829354946560,
    2007126373867411184151429120, 2007125889640379249275699200, 23869487312197764230676480, 95302852754043405858766848, 15214832933034496031547457536, 151821152592461470590226661376,
    15214832933034496031547457536, 95291978398411954078089216, 962074792387437148990603264, 35528142146860529860340613120, 35528133446914856097073332224, 962083492333110912257884160,
    95302852754043405858766848, 15214832933034496031547457536, 151821152592461470590226661376, 15214832933034496031547457536, 95291978398411954078089216, 24739066089962669545472655360,
    913580798062127910694472908800, 913580574349239156781885685760, 24739289802851423458059878400, 7303711174408176559265415168, 26128544496970880254388207616, 7303708746355487857245683712,
    962074792387437148990603264, 35528142146860529860340613120, 35528133446914856097073332224, 962083492333110912257884160, 7303711174408176559265415168, 26128544496970880254388207616,
    7303708746355487857245683712, 299813603264428035327131648, 299813603264428035327131648, 100597455684823595073142784
  ]
def negativeScales : Array ℕ := #[
    35, 31, 29, 29, 30, 31,
    30, 26, 34, 32, 29, 32,
    32, 30, 26, 29, 34, 37,
    32, 35, 37, 33, 9, 9,
    28, 30, 26, 7, 7, 22,
    28, 27, 21, 21, 28, 33,
    28, 23, 25, 30, 33, 28,
    21, 28, 33, 28, 23, 28,
    33, 36, 31, 31, 33, 29,
    25, 30, 33, 28, 31, 33,
    29, 4, 4, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35978247766777855, 31306855783448968, 29557585701641027, 29557585701641027, 30635588213655331, 31740818957104808,
    30628602584029001, 26474797247937837, 34355638281163654, 32231464756546478, 29740818577206103, 32231464756546478,
    32231464756546478, 30628602584029001, 26474797247937837, 29336719239719401, 34543388623590196, 37543388270310535,
    32336732285806700, 35391630019342910, 37230555160102510, 33391629539731919, 9116343961237469, 9116343961237469,
    28597214152998034, 30436139293752432, 26597213673387043, 7330916878114618, 7330916878114618, 22303340684136973,
    28697190017397742, 27697189669341918, 21303369951586859, 21300721771969986, 28619465149235639, 33938287569567980,
    28619465149235639, 23300557146530098, 25636279521593277, 30842948906961092, 33842948553681421, 28636292567680581,
    21300721771969986, 28619465149235639, 33938287569567980, 28619465149235639, 23300557146530098, 28320777695850379,
    33527447079720749, 36527446726441088, 31320790741937678, 31560688276969518, 33399613417727297, 29560687797358527,
    25636279521593277, 30842948906961092, 33842948553681421, 28636292567680581, 31560688276969518, 33399613417727297,
    29560687797358527, 4954196321574415, 4954196321574415, 22378724283971261
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
noncomputable def negativeCeiling : ℝ := 1256726041 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 624340475834132465335261986816, coefficient := (-624340475834132465335261986816) }, { argument := 24501483896773101952755040256, coefficient := (-24501483896773101952755040256) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 15385822361671228069221761024, coefficient := (-15385822361671228069221761024) }, { argument := 8275006212109347990295019520, coefficient := (-8275006212109347990295019520) }, { argument := 30623006430513214831806382080, coefficient := (-30623006430513214831806382080) }, { argument := 1720393619691753642236313600, coefficient := (-1720393619691753642236313600) }, { argument := 50688259424452273922679767040, coefficient := (-50688259424452273922679767040) }, { argument := 46507974185667073461788344320, coefficient := (-46507974185667073461788344320) }, { argument := 8275004033087704283354234880, coefficient := (-8275004033087704283354234880) }, { argument := 46507974185667073461788344320, coefficient := (-46507974185667073461788344320) }, { argument := 46507974185667073461788344320, coefficient := (-46507974185667073461788344320) }, { argument := 30623006430513214831806382080, coefficient := (-30623006430513214831806382080) }, { argument := 1720393619691753642236313600, coefficient := (-1720393619691753642236313600) }, { argument := 25013944602073365873755684864, coefficient := (-25013944602073365873755684864) }, { argument := 923731695818373776368855941120, coefficient := (-923731695818373776368855941120) }, { argument := 923731469619786258523906637824, coefficient := (-923731469619786258523906637824) }, { argument := 25014170800660883718704988160, coefficient := (-25014170800660883718704988160) }, { argument := 103937428251193281804930908160, coefficient := (-103937428251193281804930908160) }, { argument := 371829287072277911312447569920, coefficient := (-371829287072277911312447569920) }, { argument := 103937393698135788737727037440, coefficient := (-103937393698135788737727037440) }, { argument := 5367630639088953535695421440, coefficient := (-5367630639088953535695421440) }, { argument := 5367630639088953535695421440, coefficient := (-5367630639088953535695421440) }, { argument := 7490985819905822112067092480, coefficient := (-7490985819905822112067092480) }, { argument := 26798507176380390004500725760, coefficient := (-26798507176380390004500725760) }, { argument := 7490983329595372161277624320, coefficient := (-7490983329595372161277624320) }, { argument := 6228385822654569508086218752, coefficient := (-6228385822654569508086218752) }, { argument := 6228385822654569508086218752, coefficient := (-6228385822654569508086218752) }, { argument := 23869003085165829354946560, coefficient := (-23869003085165829354946560) }, { argument := 2007126373867411184151429120, coefficient := (-2007126373867411184151429120) }, { argument := 2007125889640379249275699200, coefficient := (-2007125889640379249275699200) }, { argument := 23869487312197764230676480, coefficient := (-23869487312197764230676480) }, { argument := 95302852754043405858766848, coefficient := (-95302852754043405858766848) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 151821152592461470590226661376, coefficient := (-151821152592461470590226661376) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 95291978398411954078089216, coefficient := (-95291978398411954078089216) }, { argument := 962074792387437148990603264, coefficient := (-962074792387437148990603264) }, { argument := 35528142146860529860340613120, coefficient := (-35528142146860529860340613120) }, { argument := 35528133446914856097073332224, coefficient := (-35528133446914856097073332224) }, { argument := 962083492333110912257884160, coefficient := (-962083492333110912257884160) }, { argument := 95302852754043405858766848, coefficient := (-95302852754043405858766848) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 151821152592461470590226661376, coefficient := (-151821152592461470590226661376) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 95291978398411954078089216, coefficient := (-95291978398411954078089216) }, { argument := 24739066089962669545472655360, coefficient := (-24739066089962669545472655360) }, { argument := 913580798062127910694472908800, coefficient := (-913580798062127910694472908800) }, { argument := 913580574349239156781885685760, coefficient := (-913580574349239156781885685760) }, { argument := 24739289802851423458059878400, coefficient := (-24739289802851423458059878400) }, { argument := 7303711174408176559265415168, coefficient := (-7303711174408176559265415168) }, { argument := 26128544496970880254388207616, coefficient := (-26128544496970880254388207616) }, { argument := 7303708746355487857245683712, coefficient := (-7303708746355487857245683712) }, { argument := 962074792387437148990603264, coefficient := (-962074792387437148990603264) }, { argument := 35528142146860529860340613120, coefficient := (-35528142146860529860340613120) }, { argument := 35528133446914856097073332224, coefficient := (-35528133446914856097073332224) }, { argument := 962083492333110912257884160, coefficient := (-962083492333110912257884160) }, { argument := 7303711174408176559265415168, coefficient := (-7303711174408176559265415168) }, { argument := 26128544496970880254388207616, coefficient := (-26128544496970880254388207616) }, { argument := 7303708746355487857245683712, coefficient := (-7303708746355487857245683712) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 100597455684823595073142784, coefficient := (-100597455684823595073142784) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18
