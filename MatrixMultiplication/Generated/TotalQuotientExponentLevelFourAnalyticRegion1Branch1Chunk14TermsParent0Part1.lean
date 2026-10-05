import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4481810058760851494874270163533824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1141815777, 1324593076001685, 58823767636943979, 12001016873, 30949990883, 25896931147,
    724482439649, 14700769316002559, 25896931147, 23370401279, 12001016873, 12001016873,
    23370401279, 724482439649, 23370401279, 331146529064193, 30949990883, 1767,
    5415, 16017, 35739, 1767, 17841, 36309,
    1767, 5415, 1767, 34718475, 6885883125, 6885883125,
    34718475, 2499232728813, 829946530949427, 89015689125, 29587388866199673, 28169521875,
    3380342625, 89015689125, 176904597375, 28169521875, 2730190060125, 174651035625,
    3319788340251931, 89015689125, 3380342625, 174651035625, 3380342625, 89015689125,
    89015689125, 2499232728813, 4166217, 826305975, 826305975, 4166217,
    440325, 283676175, 3017015415, 141838515, 440325, 4602001034683,
    3813, 88806423093665, 39897, 1767
  ]
def negativeCoefficients : Array ℕ := #[
    21062783417642816950744645632, 372839805218670478353613455360, 16557418625641846616169564340224, 221379686880501084644880416768, 285463280451172451252608958464, 3821712489305492408606356668416,
    6682171075050914318096785211392, 16551594803402186517986794274816, 3821712489305492408606356668416, 215553905646803687680541458432, 221379686880501084644880416768, 221379686880501084644880416768,
    215553905646803687680541458432, 6682171075050914318096785211392, 215553905646803687680541458432, 372837846224633179572044562432, 285463280451172451252608958464, 16688843150461326185201664,
    409145832075826061314621440, 302552575824492429551075328, 337545311462556500584562688, 16688843150461326185201664, 337006961683509361030201344, 342928809253027896128176128,
    16688843150461326185201664, 409145832075826061314621440, 16688843150461326185201664, 640442822954483225041305600, 127022123728350357623930880000, 127022123728350357623930880000,
    640442822954483225041305600, 22511087172388749363690602496, 1868873443760637631497183952896, 205256204479220691524124672000, 16656219184085351181961685630976, 129908990176721956660838400000,
    7794539410603317399650304000, 205256204479220691524124672000, 203957114577453471957516288000, 129908990176721956660838400000, 3147694831981973009892114432000, 201358934773919032824299520000,
    1868874691513439229817464553472, 205256204479220691524124672000, 7794539410603317399650304000, 201358934773919032824299520000, 7794539410603317399650304000, 205256204479220691524124672000,
    205256204479220691524124672000, 22511087172388749363690602496, 38426569377268993502478336, 7621327423701021457435852800, 7621327423701021457435852800, 38426569377268993502478336,
    64980500674049266522521600, 20931607200135374653567795200, 222616444907766453832840642560, 20931670288000106740234321920, 64980500674049266522521600, 1295348134059812239911682048,
    18006383399181957199822848, 49993571744092038074183188480, 188408255567050235090829312, 16688843150461326185201664
  ]
def negativeScales : Array ℕ := #[
    30, 50, 55, 33, 34, 34,
    39, 53, 34, 34, 33, 33,
    34, 39, 34, 48, 34, 10,
    12, 13, 15, 10, 14, 15,
    10, 12, 10, 25, 32, 32,
    25, 41, 49, 36, 54, 34,
    31, 36, 37, 34, 41, 37,
    51, 36, 31, 37, 31, 36,
    36, 41, 21, 29, 29, 21,
    18, 28, 31, 27, 18, 42,
    11, 46, 15, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30088682755958533, 50234470645325384, 55707248709462959, 33482437602664223, 34849219935042207, 34592062093843104,
    39398159765236319, 53706741173979577, 34592062093843104, 34443963454849475, 33482437602664223, 33482437602664223,
    34443963454849475, 39398159765236319, 34443963454849475, 48234463065023152, 34849219935042207, 10787086325046961,
    12402745622495697, 13967316348309272, 15125211646966781, 10787086325046961, 14122908861097361, 15148039576421043,
    10787086325046961, 12402745622495697, 10787086325046961, 25049200243380557, 32680994548095196, 32680994548095196,
    25049200243380557, 41184622390241454, 49560011722692992, 36373340584143966, 54715831900335918, 34713416025840520,
    31654522336711911, 36373340584143966, 37364180584858489, 34713416025840520, 41312138525418208, 37345684241241099,
    51560012685907588, 36373340584143966, 31654522336711911, 37345684241241099, 31654522336711911, 36373340584143966,
    36373340584143966, 41184622390241454, 21990306574595697, 29622100859005944, 29622100859005944, 21990306574595697,
    18748209232060080, 28079669747734747, 31490474921729688, 27079674096011091, 18748209232060080, 42065398446576250,
    11896710819843133, 46335729259550942, 15283992648607578, 10787086325046961
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
noncomputable def negativeCeiling : ℝ := 48453108149 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21062783417642816950744645632, coefficient := (-21062783417642816950744645632) }, { argument := 372839805218670478353613455360, coefficient := (-372839805218670478353613455360) }, { argument := 16557418625641846616169564340224, coefficient := (-16557418625641846616169564340224) }, { argument := 221379686880501084644880416768, coefficient := (-221379686880501084644880416768) }, { argument := 285463280451172451252608958464, coefficient := (-285463280451172451252608958464) }, { argument := 3821712489305492408606356668416, coefficient := (-3821712489305492408606356668416) }, { argument := 6682171075050914318096785211392, coefficient := (-6682171075050914318096785211392) }, { argument := 16551594803402186517986794274816, coefficient := (-16551594803402186517986794274816) }, { argument := 3821712489305492408606356668416, coefficient := (-3821712489305492408606356668416) }, { argument := 215553905646803687680541458432, coefficient := (-215553905646803687680541458432) }, { argument := 221379686880501084644880416768, coefficient := (-221379686880501084644880416768) }, { argument := 221379686880501084644880416768, coefficient := (-221379686880501084644880416768) }, { argument := 215553905646803687680541458432, coefficient := (-215553905646803687680541458432) }, { argument := 6682171075050914318096785211392, coefficient := (-6682171075050914318096785211392) }, { argument := 215553905646803687680541458432, coefficient := (-215553905646803687680541458432) }, { argument := 372837846224633179572044562432, coefficient := (-372837846224633179572044562432) }, { argument := 285463280451172451252608958464, coefficient := (-285463280451172451252608958464) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 640442822954483225041305600, coefficient := (-640442822954483225041305600) }, { argument := 127022123728350357623930880000, coefficient := (-127022123728350357623930880000) }, { argument := 127022123728350357623930880000, coefficient := (-127022123728350357623930880000) }, { argument := 640442822954483225041305600, coefficient := (-640442822954483225041305600) }, { argument := 22511087172388749363690602496, coefficient := (-22511087172388749363690602496) }, { argument := 1868873443760637631497183952896, coefficient := (-1868873443760637631497183952896) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 16656219184085351181961685630976, coefficient := (-16656219184085351181961685630976) }, { argument := 129908990176721956660838400000, coefficient := (-129908990176721956660838400000) }, { argument := 7794539410603317399650304000, coefficient := (-7794539410603317399650304000) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 203957114577453471957516288000, coefficient := (-203957114577453471957516288000) }, { argument := 129908990176721956660838400000, coefficient := (-129908990176721956660838400000) }, { argument := 3147694831981973009892114432000, coefficient := (-3147694831981973009892114432000) }, { argument := 201358934773919032824299520000, coefficient := (-201358934773919032824299520000) }, { argument := 1868874691513439229817464553472, coefficient := (-1868874691513439229817464553472) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 7794539410603317399650304000, coefficient := (-7794539410603317399650304000) }, { argument := 201358934773919032824299520000, coefficient := (-201358934773919032824299520000) }, { argument := 7794539410603317399650304000, coefficient := (-7794539410603317399650304000) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 205256204479220691524124672000, coefficient := (-205256204479220691524124672000) }, { argument := 22511087172388749363690602496, coefficient := (-22511087172388749363690602496) }, { argument := 38426569377268993502478336, coefficient := (-38426569377268993502478336) }, { argument := 7621327423701021457435852800, coefficient := (-7621327423701021457435852800) }, { argument := 7621327423701021457435852800, coefficient := (-7621327423701021457435852800) }, { argument := 38426569377268993502478336, coefficient := (-38426569377268993502478336) }, { argument := 64980500674049266522521600, coefficient := (-64980500674049266522521600) }, { argument := 20931607200135374653567795200, coefficient := (-20931607200135374653567795200) }, { argument := 222616444907766453832840642560, coefficient := (-222616444907766453832840642560) }, { argument := 20931670288000106740234321920, coefficient := (-20931670288000106740234321920) }, { argument := 64980500674049266522521600, coefficient := (-64980500674049266522521600) }, { argument := 1295348134059812239911682048, coefficient := (-1295348134059812239911682048) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 49993571744092038074183188480, coefficient := (-49993571744092038074183188480) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-83228589691388890079614658936832)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    177612808867915, 1767, 3441, 65007, 3441, 39897,
    65007, 575251684311, 3441, 3441, 3813, 3441,
    10545, 31191, 69597, 3441, 34743, 70707,
    3441, 10545, 3441, 65007, 199215, 589257,
    1314819, 65007, 656361, 1335789, 65007, 199215,
    65007, 109710381, 21759390675, 21759390675, 109710381, 3441,
    10545, 31191, 69597, 3441, 34743, 70707,
    3441, 10545, 3441, 218032023, 43243346025, 43243346025,
    218032023, 1135575, 731585925, 7780723965, 365794065, 1135575,
    39897, 122265, 361647, 806949, 39897, 402831,
    819819, 39897, 122265, 39897
  ]
def negativeCoefficients : Array ℕ := #[
    49993561239610570093877002240, 16688843150461326185201664, 16249663067554449180327936, 613973755903814052813471744, 16249663067554449180327936, 188408255567050235090829312,
    613973755903814052813471744, 1295351635553634900013744128, 16249663067554449180327936, 16249663067554449180327936, 18006383399181957199822848, 16249663067554449180327936,
    398378836494883270227394560, 294590665934374207720783872, 328662540108278697937600512, 16249663067554449180327936, 328138357428680167318880256, 333904366904264004124803072,
    16249663067554449180327936, 398378836494883270227394560, 16249663067554449180327936, 613973755903814052813471744, 15052259822158021939943178240, 11130750026385274118747455488,
    12418114353280368100453122048, 613973755903814052813471744, 12398308748251212808426881024, 12616170403571921020715532288, 613973755903814052813471744, 15052259822158021939943178240,
    613973755903814052813471744, 1011899660268083495565262848, 200694955490793565045810790400, 200694955490793565045810790400, 1011899660268083495565262848, 16249663067554449180327936,
    398378836494883270227394560, 294590665934374207720783872, 328662540108278697937600512, 16249663067554449180327936, 328138357428680167318880256, 333904366904264004124803072,
    16249663067554449180327936, 398378836494883270227394560, 16249663067554449180327936, 1005495232038538663314849792, 199424734253510061469571481600, 199424734253510061469571481600,
    1005495232038538663314849792, 83790645606010896305356800, 26990756652806141000653209600, 287058047381067269416031354880, 26990838002947506059775836160, 83790645606010896305356800,
    188408255567050235090829312, 4619041104224457376420331520, 3415659342860717165195034624, 3810708910985177335546773504, 188408255567050235090829312, 3804631225321724102156746752,
    3871485767619709669447041024, 188408255567050235090829312, 4619041104224457376420331520, 188408255567050235090829312
  ]
def negativeScales : Array ℕ := #[
    47, 10, 11, 15, 11, 15,
    15, 39, 11, 11, 11, 11,
    13, 14, 16, 11, 15, 16,
    11, 13, 11, 15, 17, 19,
    20, 15, 19, 20, 15, 17,
    15, 26, 34, 34, 26, 11,
    13, 14, 16, 11, 15, 16,
    11, 13, 11, 27, 35, 35,
    27, 20, 29, 32, 28, 20,
    15, 16, 18, 19, 15, 18,
    19, 15, 16, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47335728956416671, 10787086325046961, 11748612176955137, 15988307476108722, 11748612176955137, 15283992648607578,
    15988307476108722, 39065402346362580, 11748612176955137, 11748612176955137, 11896710819843133, 11748612176955137,
    13364271474681056, 14928842193830838, 16086737499152145, 11748612176955137, 15084434713282725, 16109565428606407,
    11748612176955137, 13364271474681056, 11748612176955137, 15988307476108722, 17603966754433849, 19168537466317519,
    20326432778898632, 15988307476108722, 19324129993029212, 20349260708352894, 15988307476108722, 17603966754433849,
    15988307476108722, 26709124801872523, 34340919106451587, 34340919106451587, 26709124801872523, 11748612176955137,
    13364271474681056, 14928842193830838, 16086737499152145, 11748612176955137, 15084434713282725, 16109565428606407,
    11748612176955137, 13364271474681056, 11748612176955137, 27699964802569787, 35331759107166111, 35331759107166111,
    27699964802569787, 20114991562515464, 29446452078406411, 32857257254389320, 28446456426682755, 20114991562515464,
    15283992648607578, 16899651950892089, 18464222658441707, 19622117971033051, 15283992648607578, 18619815185163015,
    19644945900495728, 15283992648607578, 16899651950892089, 15283992648607578
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
noncomputable def negativeCeiling : ℝ := 32704019 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 49993561239610570093877002240, coefficient := (-49993561239610570093877002240) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 1295351635553634900013744128, coefficient := (-1295351635553634900013744128) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 11130750026385274118747455488, coefficient := (-11130750026385274118747455488) }, { argument := 12418114353280368100453122048, coefficient := (-12418114353280368100453122048) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 12398308748251212808426881024, coefficient := (-12398308748251212808426881024) }, { argument := 12616170403571921020715532288, coefficient := (-12616170403571921020715532288) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 15052259822158021939943178240, coefficient := (-15052259822158021939943178240) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 1005495232038538663314849792, coefficient := (-1005495232038538663314849792) }, { argument := 199424734253510061469571481600, coefficient := (-199424734253510061469571481600) }, { argument := 199424734253510061469571481600, coefficient := (-199424734253510061469571481600) }, { argument := 1005495232038538663314849792, coefficient := (-1005495232038538663314849792) }, { argument := 83790645606010896305356800, coefficient := (-83790645606010896305356800) }, { argument := 26990756652806141000653209600, coefficient := (-26990756652806141000653209600) }, { argument := 287058047381067269416031354880, coefficient := (-287058047381067269416031354880) }, { argument := 26990838002947506059775836160, coefficient := (-26990838002947506059775836160) }, { argument := 83790645606010896305356800, coefficient := (-83790645606010896305356800) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 3415659342860717165195034624, coefficient := (-3415659342860717165195034624) }, { argument := 3810708910985177335546773504, coefficient := (-3810708910985177335546773504) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 3804631225321724102156746752, coefficient := (-3804631225321724102156746752) }, { argument := 3871485767619709669447041024, coefficient := (-3871485767619709669447041024) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 4619041104224457376420331520, coefficient := (-4619041104224457376420331520) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
