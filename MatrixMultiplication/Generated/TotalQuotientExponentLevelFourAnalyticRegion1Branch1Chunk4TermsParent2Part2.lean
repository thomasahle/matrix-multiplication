import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9222658035582007734592203116249088)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    221934636135, 2360368185103, 110967652523, 344489165, 7091035461, 1110061831311,
    277515559611, 28364548977, 2136735, 1376575965, 14640464277, 688290057,
    2136735, 231733185, 36276530435, 9069135935, 926946045, 2929043325,
    10498847775, 732473625, 166782399, 29252065857, 7313017341, 41694723,
    93778925, 60416389575, 642553709935, 30208285835, 93778925, 139039911,
    21765918261, 5441481561, 556167627, 344489165, 221934636135, 2360368185103,
    110967652523, 344489165, 113595607287, 17782755219237, 4445690435337, 454388951259,
    627791619325, 2250253039775, 156993513625, 7276422009, 1139083055659, 284770868359,
    29106105813, 1135492462325, 4070053320775, 283955608625, 2390752425, 2390754135,
    6625424270917, 106257668322681, 7129437777, 1856734945690583, 277770303, 462950505,
    14166285453, 462950505, 277770303, 226938337551
  ]
def negativeCoefficients : Array ℕ := #[
    1023492858468549239392740311040, 10885276957580333801153455194112, 1023495943276055511675210563584, 3177351731460450944360120320, 65403258183333014161732927488, 2559628313523420154496204931072,
    2559629252308202024695064690688, 65404196968114884360592687104, 78831607396675557544427520, 25393344524374757145512509440, 270068897638106145307735621632, 25393421059915918966442164224,
    78831607396675557544427520, 68395564113289426574361231360, 2676735491266321730192109731840, 2676736473002041333014446735360, 68396545849009029396698234880, 54031312597082270149587763200,
    193669557974259961979889254400, 54047014004469209877184512000, 192287014397019490483175424, 33725335780711016635073298432, 33725339824006733291285643264, 192282971101302834270830592,
    864957914491301256390246400, 278621419086889696457706700800, 2963255960195886872126543626240, 278622258851855221992907079680, 864957914491301256390246400, 41037338467973655944616738816,
    1606041294759793038115265839104, 1606041883801224799808668041216, 41037927509405417638018940928, 3177351731460450944360120320, 1023492858468549239392740311040, 10885276957580333801153455194112,
    1023495943276055511675210563584, 3177351731460450944360120320, 1047734547760452403335996112896, 41004241806835966004380380954624, 41004256845800020670115055927296, 1047749586724507069070671085568,
    723794458331747910545519411200, 2594365120363524074022266470400, 724004791768202123979784192000, 67113147286165249826091958272, 2626546700805078197751007674368, 2626547664133253058020425859072,
    67114110614340110095510142976, 1309133678133472503832720179200, 4692451998418006995471066726400, 1309514110149951897649283072000, 44101598127575489271614668800, 44101629671507855314947932160,
    3729782284709155167329583104, 239270997731641954161433509888, 65757457030877874908420898816, 2090497702384471931662779809792, 40991661525742051890963677184, 2134982371132398535987691520,
    65330460556651395201223360512, 68319435876236753151606128640, 40991661525742051890963677184, 1046568358329101762341166383104
  ]
def negativeScales : Array ℕ := #[
    37, 41, 36, 28, 32, 40,
    38, 34, 21, 30, 33, 29,
    21, 27, 35, 33, 29, 31,
    33, 29, 27, 34, 32, 25,
    26, 35, 39, 34, 26, 27,
    34, 32, 29, 28, 37, 41,
    36, 28, 36, 44, 42, 38,
    39, 41, 37, 32, 40, 38,
    34, 40, 41, 38, 31, 31,
    42, 46, 32, 50, 28, 28,
    33, 28, 28, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37691343882516541, 41102149056452314, 36691348230792891, 28359883366566665, 32723349164984993, 40013777176702421,
    38013777705833894, 34723369872981362, 21026976563942232, 30358437079833139, 33769242254168380, 29358441428109483,
    21026976563942232, 27787889417559181, 35078317428897131, 33078317958028605, 29787910125555707, 31447782387012520,
    33289511952907164, 29448201570829365, 27313391804384731, 34767819464375381, 32767819637338592, 25313361467941953,
    26482760405564535, 35814220922316231, 39225026095450035, 34814225270592649, 26482760405564535, 27050923822889312,
    34341351834730926, 32341352363862399, 29050944530885622, 28359883366566665, 37691343882516541, 41102149056452314,
    36691348230792891, 28359883366566665, 36725116091164260, 44015544102876608, 42015544632008082, 38725136799160631,
    39191494813619269, 41033224379513955, 37191913997436113, 32760582071342685, 40051010082901396, 38051010612032869,
    34760602779339121, 40046455267764540, 41888184837187639, 38046874451581384, 31154817593104060, 31154818624999965,
    42591149981736611, 46594560288754973, 32731141165261405, 50721689304492107, 28049317125139577, 28786282719792931,
    33721742467230802, 28786282719792931, 28049317125139577, 37723509393409898
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
noncomputable def negativeCeiling : ℝ := 74040549729 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1023492858468549239392740311040, coefficient := (-1023492858468549239392740311040) }, { argument := 10885276957580333801153455194112, coefficient := (-10885276957580333801153455194112) }, { argument := 1023495943276055511675210563584, coefficient := (-1023495943276055511675210563584) }, { argument := 3177351731460450944360120320, coefficient := (-3177351731460450944360120320) }, { argument := 65403258183333014161732927488, coefficient := (-65403258183333014161732927488) }, { argument := 2559628313523420154496204931072, coefficient := (-2559628313523420154496204931072) }, { argument := 2559629252308202024695064690688, coefficient := (-2559629252308202024695064690688) }, { argument := 65404196968114884360592687104, coefficient := (-65404196968114884360592687104) }, { argument := 78831607396675557544427520, coefficient := (-78831607396675557544427520) }, { argument := 25393344524374757145512509440, coefficient := (-25393344524374757145512509440) }, { argument := 270068897638106145307735621632, coefficient := (-270068897638106145307735621632) }, { argument := 25393421059915918966442164224, coefficient := (-25393421059915918966442164224) }, { argument := 78831607396675557544427520, coefficient := (-78831607396675557544427520) }, { argument := 68395564113289426574361231360, coefficient := (-68395564113289426574361231360) }, { argument := 2676735491266321730192109731840, coefficient := (-2676735491266321730192109731840) }, { argument := 2676736473002041333014446735360, coefficient := (-2676736473002041333014446735360) }, { argument := 68396545849009029396698234880, coefficient := (-68396545849009029396698234880) }, { argument := 54031312597082270149587763200, coefficient := (-54031312597082270149587763200) }, { argument := 193669557974259961979889254400, coefficient := (-193669557974259961979889254400) }, { argument := 54047014004469209877184512000, coefficient := (-54047014004469209877184512000) }, { argument := 192287014397019490483175424, coefficient := (-192287014397019490483175424) }, { argument := 33725335780711016635073298432, coefficient := (-33725335780711016635073298432) }, { argument := 33725339824006733291285643264, coefficient := (-33725339824006733291285643264) }, { argument := 192282971101302834270830592, coefficient := (-192282971101302834270830592) }, { argument := 864957914491301256390246400, coefficient := (-864957914491301256390246400) }, { argument := 278621419086889696457706700800, coefficient := (-278621419086889696457706700800) }, { argument := 2963255960195886872126543626240, coefficient := (-2963255960195886872126543626240) }, { argument := 278622258851855221992907079680, coefficient := (-278622258851855221992907079680) }, { argument := 864957914491301256390246400, coefficient := (-864957914491301256390246400) }, { argument := 41037338467973655944616738816, coefficient := (-41037338467973655944616738816) }, { argument := 1606041294759793038115265839104, coefficient := (-1606041294759793038115265839104) }, { argument := 1606041883801224799808668041216, coefficient := (-1606041883801224799808668041216) }, { argument := 41037927509405417638018940928, coefficient := (-41037927509405417638018940928) }, { argument := 3177351731460450944360120320, coefficient := (-3177351731460450944360120320) }, { argument := 1023492858468549239392740311040, coefficient := (-1023492858468549239392740311040) }, { argument := 10885276957580333801153455194112, coefficient := (-10885276957580333801153455194112) }, { argument := 1023495943276055511675210563584, coefficient := (-1023495943276055511675210563584) }, { argument := 3177351731460450944360120320, coefficient := (-3177351731460450944360120320) }, { argument := 1047734547760452403335996112896, coefficient := (-1047734547760452403335996112896) }, { argument := 41004241806835966004380380954624, coefficient := (-41004241806835966004380380954624) }, { argument := 41004256845800020670115055927296, coefficient := (-41004256845800020670115055927296) }, { argument := 1047749586724507069070671085568, coefficient := (-1047749586724507069070671085568) }, { argument := 723794458331747910545519411200, coefficient := (-723794458331747910545519411200) }, { argument := 2594365120363524074022266470400, coefficient := (-2594365120363524074022266470400) }, { argument := 724004791768202123979784192000, coefficient := (-724004791768202123979784192000) }, { argument := 67113147286165249826091958272, coefficient := (-67113147286165249826091958272) }, { argument := 2626546700805078197751007674368, coefficient := (-2626546700805078197751007674368) }, { argument := 2626547664133253058020425859072, coefficient := (-2626547664133253058020425859072) }, { argument := 67114110614340110095510142976, coefficient := (-67114110614340110095510142976) }, { argument := 1309133678133472503832720179200, coefficient := (-1309133678133472503832720179200) }, { argument := 4692451998418006995471066726400, coefficient := (-4692451998418006995471066726400) }, { argument := 1309514110149951897649283072000, coefficient := (-1309514110149951897649283072000) }, { argument := 44101598127575489271614668800, coefficient := (-44101598127575489271614668800) }, { argument := 44101629671507855314947932160, coefficient := (-44101629671507855314947932160) }, { argument := 3729782284709155167329583104, coefficient := (-3729782284709155167329583104) }, { argument := 239270997731641954161433509888, coefficient := (-239270997731641954161433509888) }, { argument := 65757457030877874908420898816, coefficient := (-65757457030877874908420898816) }, { argument := 2090497702384471931662779809792, coefficient := (-2090497702384471931662779809792) }, { argument := 40991661525742051890963677184, coefficient := (-40991661525742051890963677184) }, { argument := 2134982371132398535987691520, coefficient := (-2134982371132398535987691520) }, { argument := 65330460556651395201223360512, coefficient := (-65330460556651395201223360512) }, { argument := 68319435876236753151606128640, coefficient := (-68319435876236753151606128640) }, { argument := 40991661525742051890963677184, coefficient := (-40991661525742051890963677184) }, { argument := 1046568358329101762341166383104, coefficient := (-1046568358329101762341166383104) }] }

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
def constantNumerator : ℤ := (-2019464970324233704389821828431872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14536645857, 106257697590649, 14166285453, 462950505, 14536645857, 462950505,
    14166285453, 462950505, 6625424270917, 105737700408035, 656106815, 960500087808359,
    7404634055, 656106815, 1920999904795727, 656106815, 656106815, 27200313959,
    168713181, 7404634055, 27200313959, 105737937471203, 656106815, 168713181,
    656106815, 359435291256457, 7313017341, 189758933, 2643630114327329, 11779650687,
    718940998936525, 11779650687, 12275943281, 7313017341, 364921025, 7091035461,
    1110061831311, 277515559611, 28364548977, 627791619325, 2250253039775, 156993513625,
    15296604191, 15296609249, 18550607725, 66492702575, 4638999625, 15778966005,
    15778977291, 8322475, 1459683925, 364921025, 2080575, 8309525,
    5353350975, 56935138855, 2676683555, 8309525, 231733185, 36276530435,
    9069135935, 926946045, 2136735, 1376575965
  ]
def negativeCoefficients : Array ℕ := #[
    67038446453557314030013513728, 239271063637246843507234045952, 65330460556651395201223360512, 2134982371132398535987691520, 67038446453557314030013513728, 2134982371132398535987691520,
    65330460556651395201223360512, 68319435876236753151606128640, 3729782284709155167329583104, 238100134078319784426660167680, 24206069002643398291703726080, 8651415675086108560829477552128,
    273182778744118352149227765760, 24206069002643398291703726080, 8651414455416794409121026670592, 24206069002643398291703726080, 24206069002643398291703726080, 1003514460652444883464631615488,
    24897670974147495385752403968, 273182778744118352149227765760, 1003514460652444883464631615488, 238100667897117318461305913344, 24206069002643398291703726080, 24897670974147495385752403968,
    24206069002643398291703726080, 809376321883192722105445646336, 33725339824006733291285643264, 1750217236375598933280292864, 2976462899447495155786025271296, 54324050375196474582969090048,
    809455603727976537754540441600, 54324050375196474582969090048, 56612795991995334726489473024, 33725339824006733291285643264, 1682901188822691282000281600, 65403258183333014161732927488,
    2559628313523420154496204931072, 2559629252308202024695064690688, 65404196968114884360592687104, 723794458331747910545519411200, 2594365120363524074022266470400, 724004791768202123979784192000,
    70543135677052485041509105664, 70543159002960366247237124096, 42774789139356797201756979200, 153321733396289136567412326400, 42787219420204791152771072000, 36383818455249778649082101760,
    36383844478993980634832044032, 9595160399052868786585600, 1682900987061427975802060800, 1682901188822691282000281600, 9594958637789562588364800, 76641840524545680945971200,
    24687973843142125002581606400, 262566983814825419049187409920, 24688048252696032328485437440, 76641840524545680945971200, 2137361378540294580448788480, 83647984102072554068503429120,
    83648014781313791656701460480, 2137392057781532168646819840, 78831607396675557544427520, 25393344524374757145512509440
  ]
def negativeScales : Array ℕ := #[
    33, 46, 33, 28, 33, 28,
    33, 28, 42, 46, 29, 49,
    32, 29, 50, 29, 29, 34,
    27, 32, 34, 46, 29, 27,
    29, 48, 32, 27, 51, 33,
    49, 33, 33, 32, 28, 32,
    40, 38, 34, 39, 41, 37,
    33, 33, 34, 35, 32, 33,
    33, 22, 30, 28, 20, 22,
    32, 35, 31, 22, 27, 35,
    33, 29, 21, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33758975373583320, 46594560686135671, 33721742467230802, 28786282719792931, 33758975373583320, 28786282719792931,
    33721742467230802, 28786282719792931, 42591149981736611, 46587483184752596, 29289355465597985, 49770779074556021,
    32785781292199583, 29289355465597985, 50770778871166070, 29289355465597985, 29289355465597985, 34662904252749250,
    27329997450095332, 32785781292199583, 34662904252749250, 46587486419260933, 29289355465597985, 27329997450095332,
    29289355465597985, 48352725395648968, 32767819637338592, 27499592561954403, 51231441758417874, 33455577707090881,
    49352866706828447, 33455577707090881, 33515114834068634, 32767819637338592, 28443009033587804, 32723349164984993,
    40013777176702421, 38013777705833894, 34723369872981362, 39191494813619269, 41033224379513955, 37191913997436113,
    33832492363774622, 33832492840818442, 34110747399734907, 35952476976498227, 32111166583551751, 33877283620464980,
    33877284652360940, 22988581220676475, 30443008860624594, 28443009033587804, 20988550884224041, 22986334598453789,
    32317795095335792, 35728600269470391, 31317799443612136, 22986334598453789, 27787889417559181, 35078317428897131,
    33078317958028605, 29787910125555707, 21026976563942232, 30358437079833139
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
noncomputable def negativeCeiling : ℝ := 9906307071 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 67038446453557314030013513728, coefficient := (-67038446453557314030013513728) }, { argument := 239271063637246843507234045952, coefficient := (-239271063637246843507234045952) }, { argument := 65330460556651395201223360512, coefficient := (-65330460556651395201223360512) }, { argument := 2134982371132398535987691520, coefficient := (-2134982371132398535987691520) }, { argument := 67038446453557314030013513728, coefficient := (-67038446453557314030013513728) }, { argument := 2134982371132398535987691520, coefficient := (-2134982371132398535987691520) }, { argument := 65330460556651395201223360512, coefficient := (-65330460556651395201223360512) }, { argument := 68319435876236753151606128640, coefficient := (-68319435876236753151606128640) }, { argument := 3729782284709155167329583104, coefficient := (-3729782284709155167329583104) }, { argument := 238100134078319784426660167680, coefficient := (-238100134078319784426660167680) }, { argument := 24206069002643398291703726080, coefficient := (-24206069002643398291703726080) }, { argument := 8651415675086108560829477552128, coefficient := (-8651415675086108560829477552128) }, { argument := 273182778744118352149227765760, coefficient := (-273182778744118352149227765760) }, { argument := 24206069002643398291703726080, coefficient := (-24206069002643398291703726080) }, { argument := 8651414455416794409121026670592, coefficient := (-8651414455416794409121026670592) }, { argument := 24206069002643398291703726080, coefficient := (-24206069002643398291703726080) }, { argument := 24206069002643398291703726080, coefficient := (-24206069002643398291703726080) }, { argument := 1003514460652444883464631615488, coefficient := (-1003514460652444883464631615488) }, { argument := 24897670974147495385752403968, coefficient := (-24897670974147495385752403968) }, { argument := 273182778744118352149227765760, coefficient := (-273182778744118352149227765760) }, { argument := 1003514460652444883464631615488, coefficient := (-1003514460652444883464631615488) }, { argument := 238100667897117318461305913344, coefficient := (-238100667897117318461305913344) }, { argument := 24206069002643398291703726080, coefficient := (-24206069002643398291703726080) }, { argument := 24897670974147495385752403968, coefficient := (-24897670974147495385752403968) }, { argument := 24206069002643398291703726080, coefficient := (-24206069002643398291703726080) }, { argument := 809376321883192722105445646336, coefficient := (-809376321883192722105445646336) }, { argument := 33725339824006733291285643264, coefficient := (-33725339824006733291285643264) }, { argument := 1750217236375598933280292864, coefficient := (-1750217236375598933280292864) }, { argument := 2976462899447495155786025271296, coefficient := (-2976462899447495155786025271296) }, { argument := 54324050375196474582969090048, coefficient := (-54324050375196474582969090048) }, { argument := 809455603727976537754540441600, coefficient := (-809455603727976537754540441600) }, { argument := 54324050375196474582969090048, coefficient := (-54324050375196474582969090048) }, { argument := 56612795991995334726489473024, coefficient := (-56612795991995334726489473024) }, { argument := 33725339824006733291285643264, coefficient := (-33725339824006733291285643264) }, { argument := 1682901188822691282000281600, coefficient := (-1682901188822691282000281600) }, { argument := 65403258183333014161732927488, coefficient := (-65403258183333014161732927488) }, { argument := 2559628313523420154496204931072, coefficient := (-2559628313523420154496204931072) }, { argument := 2559629252308202024695064690688, coefficient := (-2559629252308202024695064690688) }, { argument := 65404196968114884360592687104, coefficient := (-65404196968114884360592687104) }, { argument := 723794458331747910545519411200, coefficient := (-723794458331747910545519411200) }, { argument := 2594365120363524074022266470400, coefficient := (-2594365120363524074022266470400) }, { argument := 724004791768202123979784192000, coefficient := (-724004791768202123979784192000) }, { argument := 70543135677052485041509105664, coefficient := (-70543135677052485041509105664) }, { argument := 70543159002960366247237124096, coefficient := (-70543159002960366247237124096) }, { argument := 42774789139356797201756979200, coefficient := (-42774789139356797201756979200) }, { argument := 153321733396289136567412326400, coefficient := (-153321733396289136567412326400) }, { argument := 42787219420204791152771072000, coefficient := (-42787219420204791152771072000) }, { argument := 36383818455249778649082101760, coefficient := (-36383818455249778649082101760) }, { argument := 36383844478993980634832044032, coefficient := (-36383844478993980634832044032) }, { argument := 9595160399052868786585600, coefficient := (-9595160399052868786585600) }, { argument := 1682900987061427975802060800, coefficient := (-1682900987061427975802060800) }, { argument := 1682901188822691282000281600, coefficient := (-1682901188822691282000281600) }, { argument := 9594958637789562588364800, coefficient := (-9594958637789562588364800) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 24687973843142125002581606400, coefficient := (-24687973843142125002581606400) }, { argument := 262566983814825419049187409920, coefficient := (-262566983814825419049187409920) }, { argument := 24688048252696032328485437440, coefficient := (-24688048252696032328485437440) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 2137361378540294580448788480, coefficient := (-2137361378540294580448788480) }, { argument := 83647984102072554068503429120, coefficient := (-83647984102072554068503429120) }, { argument := 83648014781313791656701460480, coefficient := (-83648014781313791656701460480) }, { argument := 2137392057781532168646819840, coefficient := (-2137392057781532168646819840) }, { argument := 78831607396675557544427520, coefficient := (-78831607396675557544427520) }, { argument := 25393344524374757145512509440, coefficient := (-25393344524374757145512509440) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
