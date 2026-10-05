import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-652322054961313560367444785102848)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1144093417, 2390752425, 15296604191, 15778966005, 780140265, 7876900095,
    16030624155, 1146035945, 2390752425, 780140265, 51067787942571, 700796834108757,
    18340317435, 1487052765, 318724975965, 576480788565, 700796834280789, 318724975965,
    9418000845, 9418000845, 18340317435, 18340317435, 576480788565, 18340317435,
    51067787770539, 1487052765, 166782399, 29252065857, 7313017341, 41694723,
    6625358947909, 106257431526777, 1782333861, 1856734918472663, 69441579, 115735965,
    3541520529, 115735965, 69441579, 56733770043, 3634109301, 106257460794745,
    3541520529, 115735965, 3634109301, 115735965, 3541520529, 115735965,
    6625358947909, 4327687, 759035641, 189758933, 1081899, 8309525,
    5353350975, 56935138855, 2676683555, 8309525, 6619627780583, 2036825,
    64048768518683, 22987025, 2036825, 128097560232419
  ]
def negativeCoefficients : Array ℕ := #[
    2638099807476857596735913984, 44101598127575489271614668800, 70543135677052485041509105664, 36383818455249778649082101760, 1798880976256368641342177280, 36325790036660863531619450880,
    36964102641138929823708610560, 2642578972085859455221104640, 44101598127575489271614668800, 1798880976256368641342177280, 57497217687199566045646946304, 789027090238655331620899258368,
    42289892744254776828619653120, 54862563560114305074966036480, 734929757690697878400065863680, 1329274196258602850045531258880, 789027090432346144394849550336, 734929757690697878400065863680,
    43432862818423824851014778880, 43432862818423824851014778880, 42289892744254776828619653120, 42289892744254776828619653120, 1329274196258602850045531258880, 42289892744254776828619653120,
    57497217493508753271696654336, 54862563560114305074966036480, 192287014397019490483175424, 33725335780711016635073298432, 33725339824006733291285643264, 192282971101302834270830592,
    3729745511124844227338436608, 239270464514669445531561885696, 65756513175547227448648138752, 2090497671739818339212787187712, 40991073148393076851105333248, 2134951726478806085995069440,
    65329522830251466231449124864, 68318455247321794751842222080, 40991073148393076851105333248, 1046553336319910743354783039488, 67037484211434511100245180416, 239270530420274334877362421760,
    65329522830251466231449124864, 2134951726478806085995069440, 67037484211434511100245180416, 2134951726478806085995069440, 65329522830251466231449124864, 68318455247321794751842222080,
    3729745511124844227338436608, 9978966815014983538049024, 1750217026543885094834143232, 1750217236375598933280292864, 9978756983301145091899392, 76641840524545680945971200,
    24687973843142125002581606400, 262566983814825419049187409920, 24688048252696032328485437440, 76641840524545680945971200, 3726519150745622782091984896, 75145578995866914940518400,
    144225005017139956936169488384, 848071534381926611471564800, 75145578995866914940518400, 144225031132447968845895827456
  ]
def negativeScales : Array ℕ := #[
    30, 31, 33, 33, 29, 32,
    33, 30, 31, 29, 45, 49,
    34, 30, 38, 39, 49, 38,
    33, 33, 34, 34, 39, 34,
    45, 30, 27, 34, 32, 25,
    42, 46, 30, 50, 26, 26,
    31, 26, 26, 35, 31, 46,
    31, 26, 31, 26, 31, 26,
    42, 22, 29, 27, 20, 22,
    32, 35, 31, 22, 42, 20,
    45, 24, 20, 46
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30091557709197235, 31154817593104060, 33832492363774622, 33877283620464980, 29539158295160941, 32874980834475251,
    33900111551405769, 30094005148395205, 31154817593104060, 29539158295160941, 45537478802017143, 49315989585916508,
    34094299558250270, 30469808693342572, 38213521119949268, 39068481574094539, 49315989586270661, 38213521119949268,
    33132773706064906, 33132773706064906, 34094299558250270, 34094299558250270, 39068481574094539, 34094299558250270,
    45537478797157137, 30469808693342572, 27313391804384731, 34767819464375381, 32767819637338592, 25313361467941953,
    42591135757493689, 46594557073696121, 30731120457265026, 50721689283343607, 26049296417143267, 26786262011796411,
    31721721759234435, 26786262011796411, 26049296417143267, 35723488685413530, 31758954665586889, 46594557471077705,
    31721721759234435, 26786262011796411, 31758954665586889, 26786262011796411, 31721721759234435, 26786262011796411,
    42591135757493689, 22045164729330614, 29499592388991193, 27499592561954403, 20045134392887837, 22986334598453789,
    32317795095335792, 35728600269470391, 31317799443612136, 22986334598453789, 42589887235714655, 20957890613333172,
    45864236067586742, 24454316427550289, 20957890613333172, 46864236328820386
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
noncomputable def negativeCeiling : ℝ := 357772041 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2638099807476857596735913984, coefficient := (-2638099807476857596735913984) }, { argument := 44101598127575489271614668800, coefficient := (-44101598127575489271614668800) }, { argument := 70543135677052485041509105664, coefficient := (-70543135677052485041509105664) }, { argument := 36383818455249778649082101760, coefficient := (-36383818455249778649082101760) }, { argument := 1798880976256368641342177280, coefficient := (-1798880976256368641342177280) }, { argument := 36325790036660863531619450880, coefficient := (-36325790036660863531619450880) }, { argument := 36964102641138929823708610560, coefficient := (-36964102641138929823708610560) }, { argument := 2642578972085859455221104640, coefficient := (-2642578972085859455221104640) }, { argument := 44101598127575489271614668800, coefficient := (-44101598127575489271614668800) }, { argument := 1798880976256368641342177280, coefficient := (-1798880976256368641342177280) }, { argument := 57497217687199566045646946304, coefficient := (-57497217687199566045646946304) }, { argument := 789027090238655331620899258368, coefficient := (-789027090238655331620899258368) }, { argument := 42289892744254776828619653120, coefficient := (-42289892744254776828619653120) }, { argument := 54862563560114305074966036480, coefficient := (-54862563560114305074966036480) }, { argument := 734929757690697878400065863680, coefficient := (-734929757690697878400065863680) }, { argument := 1329274196258602850045531258880, coefficient := (-1329274196258602850045531258880) }, { argument := 789027090432346144394849550336, coefficient := (-789027090432346144394849550336) }, { argument := 734929757690697878400065863680, coefficient := (-734929757690697878400065863680) }, { argument := 43432862818423824851014778880, coefficient := (-43432862818423824851014778880) }, { argument := 43432862818423824851014778880, coefficient := (-43432862818423824851014778880) }, { argument := 42289892744254776828619653120, coefficient := (-42289892744254776828619653120) }, { argument := 42289892744254776828619653120, coefficient := (-42289892744254776828619653120) }, { argument := 1329274196258602850045531258880, coefficient := (-1329274196258602850045531258880) }, { argument := 42289892744254776828619653120, coefficient := (-42289892744254776828619653120) }, { argument := 57497217493508753271696654336, coefficient := (-57497217493508753271696654336) }, { argument := 54862563560114305074966036480, coefficient := (-54862563560114305074966036480) }, { argument := 192287014397019490483175424, coefficient := (-192287014397019490483175424) }, { argument := 33725335780711016635073298432, coefficient := (-33725335780711016635073298432) }, { argument := 33725339824006733291285643264, coefficient := (-33725339824006733291285643264) }, { argument := 192282971101302834270830592, coefficient := (-192282971101302834270830592) }, { argument := 3729745511124844227338436608, coefficient := (-3729745511124844227338436608) }, { argument := 239270464514669445531561885696, coefficient := (-239270464514669445531561885696) }, { argument := 65756513175547227448648138752, coefficient := (-65756513175547227448648138752) }, { argument := 2090497671739818339212787187712, coefficient := (-2090497671739818339212787187712) }, { argument := 40991073148393076851105333248, coefficient := (-40991073148393076851105333248) }, { argument := 2134951726478806085995069440, coefficient := (-2134951726478806085995069440) }, { argument := 65329522830251466231449124864, coefficient := (-65329522830251466231449124864) }, { argument := 68318455247321794751842222080, coefficient := (-68318455247321794751842222080) }, { argument := 40991073148393076851105333248, coefficient := (-40991073148393076851105333248) }, { argument := 1046553336319910743354783039488, coefficient := (-1046553336319910743354783039488) }, { argument := 67037484211434511100245180416, coefficient := (-67037484211434511100245180416) }, { argument := 239270530420274334877362421760, coefficient := (-239270530420274334877362421760) }, { argument := 65329522830251466231449124864, coefficient := (-65329522830251466231449124864) }, { argument := 2134951726478806085995069440, coefficient := (-2134951726478806085995069440) }, { argument := 67037484211434511100245180416, coefficient := (-67037484211434511100245180416) }, { argument := 2134951726478806085995069440, coefficient := (-2134951726478806085995069440) }, { argument := 65329522830251466231449124864, coefficient := (-65329522830251466231449124864) }, { argument := 68318455247321794751842222080, coefficient := (-68318455247321794751842222080) }, { argument := 3729745511124844227338436608, coefficient := (-3729745511124844227338436608) }, { argument := 9978966815014983538049024, coefficient := (-9978966815014983538049024) }, { argument := 1750217026543885094834143232, coefficient := (-1750217026543885094834143232) }, { argument := 1750217236375598933280292864, coefficient := (-1750217236375598933280292864) }, { argument := 9978756983301145091899392, coefficient := (-9978756983301145091899392) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 24687973843142125002581606400, coefficient := (-24687973843142125002581606400) }, { argument := 262566983814825419049187409920, coefficient := (-262566983814825419049187409920) }, { argument := 24688048252696032328485437440, coefficient := (-24688048252696032328485437440) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 3726519150745622782091984896, coefficient := (-3726519150745622782091984896) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 144225005017139956936169488384, coefficient := (-144225005017139956936169488384) }, { argument := 848071534381926611471564800, coefficient := (-848071534381926611471564800) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 144225031132447968845895827456, coefficient := (-144225031132447968845895827456) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10432795616098174626820056147820544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2036825, 2036825, 84440945, 523755, 22987025, 84440945,
    6619693177319, 2036825, 523755, 2036825, 1144093975, 2390754135,
    15296609249, 15778977291, 780140823, 7876905729, 16030635621, 1146036503,
    2390754135, 780140823, 366793762191347, 5155520701065229, 65738939145, 5330184255,
    1142436158655, 2066334762855, 5155520708792333, 1142436158655, 33757833615, 33757833615,
    65738939145, 65738939145, 2066334762855, 65738939145, 366793754464243, 5330184255,
    64084174782369, 963850013259717, 279014369711, 16543052785982795, 10870689729, 18117816215,
    554405176179, 18117816215, 10870689729, 8881353508593, 568899429151, 963850020340677,
    554405176179, 18117816215, 568899429151, 18117816215, 554405176179, 18117816215,
    64084174782369, 268649493, 47118597099, 11779650687, 67160961, 93778925,
    60416389575, 642553709935, 30208285835, 93778925
  ]
def negativeCoefficients : Array ℕ := #[
    75145578995866914940518400, 75145578995866914940518400, 3115321003514368387962634240, 77292595538605969653104640, 848071534381926611471564800, 3115321003514368387962634240,
    3726555965835107887929622528, 75145578995866914940518400, 77292595538605969653104640, 75145578995866914940518400, 2638101094137256737977139200, 44101629671507855314947932160,
    70543159002960366247237124096, 36383844478993980634832044032, 1798882262916767782583402496, 36325816018899891351522902016, 36964129079934873467923464192, 2642580258746258596462329856,
    44101629671507855314947932160, 1798882262916767782583402496, 206486531340846584193051787264, 2902300138527280453091430760448, 151583673260622701011182551040, 196649089635402422933426012160,
    2634278429907578290545685954560, 4764643567624437872324467752960, 2902300142877253289973064400896, 2634278429907578290545685954560, 155680529294693584822295592960, 155680529294693584822295592960,
    151583673260622701011182551040, 151583673260622701011182551040, 4764643567624437872324467752960, 151583673260622701011182551040, 206486526990873747311418146816, 196649089635402422933426012160,
    144304732835111382498265792512, 8681589121115018219676462219264, 2573453335473097534909330751488, 74503286362522561275412946616320, 1604230650684528333449972416512, 83553679723152517367186063360,
    2556742599528467031435893538816, 2673717751140880555749954027520, 1604230650684528333449972416512, 40958013800289364013394608259072, 2623585543306989045329642389504, 8681589184894635854527236931584,
    2556742599528467031435893538816, 83553679723152517367186063360, 2623585543306989045329642389504, 83553679723152517367186063360, 2556742599528467031435893538816, 2673717751140880555749954027520,
    144304732835111382498265792512, 309731777681426604430983168, 54324043862342895058890522624, 54324050375196474582969090048, 309725264827847080352415744, 864957914491301256390246400,
    278621419086889696457706700800, 2963255960195886872126543626240, 278622258851855221992907079680, 864957914491301256390246400
  ]
def negativeScales : Array ℕ := #[
    20, 20, 26, 18, 24, 26,
    42, 20, 18, 20, 30, 31,
    33, 33, 29, 32, 33, 30,
    31, 29, 48, 52, 35, 32,
    40, 40, 52, 40, 34, 34,
    35, 35, 40, 35, 48, 32,
    45, 49, 38, 53, 33, 34,
    39, 34, 33, 43, 39, 49,
    39, 34, 39, 34, 39, 34,
    45, 28, 35, 33, 26, 26,
    35, 39, 34, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20957890613333172, 20957890613333172, 26331439388552514, 18998532609056515, 24454316427550289, 26331439388552514,
    42589901488340908, 20957890613333172, 18998532609056515, 20957890613333172, 30091558412831768, 31154818624999965,
    33832492840818442, 33877284652360940, 29539159327056846, 32874981866371209, 33900112583301755, 30094005850837079,
    31154818624999965, 29539159327056846, 48381962432644672, 52195039568635641, 35936029132362365, 32311538259237163,
    40055250685843954, 40910211145228308, 52195039570797955, 40055250685843954, 34974503287634041, 34974503287634041,
    35936029132362365, 35936029132362365, 40910211145228308, 35936029132362365, 48381962402251966, 32311538259237163,
    45865033371437048, 49775801991906874, 38021548468958625, 53877075009080477, 33339724428984880, 34076690023151086,
    39012149770956375, 34076690023151086, 33339724428984880, 43013916697130563, 39049382677155350, 49775802002505687,
    39012149770956375, 34076690023151086, 39049382677155350, 34076690023151086, 39012149770956375, 34076690023151086,
    45865033371437048, 28001149874467302, 35455577534127671, 33455577707090881, 26001119538024525, 26482760405564535,
    35814220922316231, 39225026095450035, 34814225270592649, 26482760405564535
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
noncomputable def negativeCeiling : ℝ := 26094444573 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 3115321003514368387962634240, coefficient := (-3115321003514368387962634240) }, { argument := 77292595538605969653104640, coefficient := (-77292595538605969653104640) }, { argument := 848071534381926611471564800, coefficient := (-848071534381926611471564800) }, { argument := 3115321003514368387962634240, coefficient := (-3115321003514368387962634240) }, { argument := 3726555965835107887929622528, coefficient := (-3726555965835107887929622528) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 77292595538605969653104640, coefficient := (-77292595538605969653104640) }, { argument := 75145578995866914940518400, coefficient := (-75145578995866914940518400) }, { argument := 2638101094137256737977139200, coefficient := (-2638101094137256737977139200) }, { argument := 44101629671507855314947932160, coefficient := (-44101629671507855314947932160) }, { argument := 70543159002960366247237124096, coefficient := (-70543159002960366247237124096) }, { argument := 36383844478993980634832044032, coefficient := (-36383844478993980634832044032) }, { argument := 1798882262916767782583402496, coefficient := (-1798882262916767782583402496) }, { argument := 36325816018899891351522902016, coefficient := (-36325816018899891351522902016) }, { argument := 36964129079934873467923464192, coefficient := (-36964129079934873467923464192) }, { argument := 2642580258746258596462329856, coefficient := (-2642580258746258596462329856) }, { argument := 44101629671507855314947932160, coefficient := (-44101629671507855314947932160) }, { argument := 1798882262916767782583402496, coefficient := (-1798882262916767782583402496) }, { argument := 206486531340846584193051787264, coefficient := (-206486531340846584193051787264) }, { argument := 2902300138527280453091430760448, coefficient := (-2902300138527280453091430760448) }, { argument := 151583673260622701011182551040, coefficient := (-151583673260622701011182551040) }, { argument := 196649089635402422933426012160, coefficient := (-196649089635402422933426012160) }, { argument := 2634278429907578290545685954560, coefficient := (-2634278429907578290545685954560) }, { argument := 4764643567624437872324467752960, coefficient := (-4764643567624437872324467752960) }, { argument := 2902300142877253289973064400896, coefficient := (-2902300142877253289973064400896) }, { argument := 2634278429907578290545685954560, coefficient := (-2634278429907578290545685954560) }, { argument := 155680529294693584822295592960, coefficient := (-155680529294693584822295592960) }, { argument := 155680529294693584822295592960, coefficient := (-155680529294693584822295592960) }, { argument := 151583673260622701011182551040, coefficient := (-151583673260622701011182551040) }, { argument := 151583673260622701011182551040, coefficient := (-151583673260622701011182551040) }, { argument := 4764643567624437872324467752960, coefficient := (-4764643567624437872324467752960) }, { argument := 151583673260622701011182551040, coefficient := (-151583673260622701011182551040) }, { argument := 206486526990873747311418146816, coefficient := (-206486526990873747311418146816) }, { argument := 196649089635402422933426012160, coefficient := (-196649089635402422933426012160) }, { argument := 144304732835111382498265792512, coefficient := (-144304732835111382498265792512) }, { argument := 8681589121115018219676462219264, coefficient := (-8681589121115018219676462219264) }, { argument := 2573453335473097534909330751488, coefficient := (-2573453335473097534909330751488) }, { argument := 74503286362522561275412946616320, coefficient := (-74503286362522561275412946616320) }, { argument := 1604230650684528333449972416512, coefficient := (-1604230650684528333449972416512) }, { argument := 83553679723152517367186063360, coefficient := (-83553679723152517367186063360) }, { argument := 2556742599528467031435893538816, coefficient := (-2556742599528467031435893538816) }, { argument := 2673717751140880555749954027520, coefficient := (-2673717751140880555749954027520) }, { argument := 1604230650684528333449972416512, coefficient := (-1604230650684528333449972416512) }, { argument := 40958013800289364013394608259072, coefficient := (-40958013800289364013394608259072) }, { argument := 2623585543306989045329642389504, coefficient := (-2623585543306989045329642389504) }, { argument := 8681589184894635854527236931584, coefficient := (-8681589184894635854527236931584) }, { argument := 2556742599528467031435893538816, coefficient := (-2556742599528467031435893538816) }, { argument := 83553679723152517367186063360, coefficient := (-83553679723152517367186063360) }, { argument := 2623585543306989045329642389504, coefficient := (-2623585543306989045329642389504) }, { argument := 83553679723152517367186063360, coefficient := (-83553679723152517367186063360) }, { argument := 2556742599528467031435893538816, coefficient := (-2556742599528467031435893538816) }, { argument := 2673717751140880555749954027520, coefficient := (-2673717751140880555749954027520) }, { argument := 144304732835111382498265792512, coefficient := (-144304732835111382498265792512) }, { argument := 309731777681426604430983168, coefficient := (-309731777681426604430983168) }, { argument := 54324043862342895058890522624, coefficient := (-54324043862342895058890522624) }, { argument := 54324050375196474582969090048, coefficient := (-54324050375196474582969090048) }, { argument := 309725264827847080352415744, coefficient := (-309725264827847080352415744) }, { argument := 864957914491301256390246400, coefficient := (-864957914491301256390246400) }, { argument := 278621419086889696457706700800, coefficient := (-278621419086889696457706700800) }, { argument := 2963255960195886872126543626240, coefficient := (-2963255960195886872126543626240) }, { argument := 278622258851855221992907079680, coefficient := (-278622258851855221992907079680) }, { argument := 864957914491301256390246400, coefficient := (-864957914491301256390246400) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
