import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 17, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

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
def constantNumerator : ℤ := (-711969601302829853457200980164608)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2324491, 2597, 14909429, 1127, 217, 4501,
    2261, 2324491, 2597, 217, 27989762375919, 405598531755793,
    5074340865, 47698804131, 563251836015, 39579858747, 202799219414355, 563251836015,
    5074340865, 39579858747, 39579858747, 39579858747, 39579858747, 39579858747,
    13994927651501, 47698804131, 185040345, 15493268007, 7746636807, 92517369,
    185806306143, 15307109353323, 885616641, 547272805222881, 29196153, 68124357,
    885616641, 885616641, 29196153, 10929093273, 437942295, 15307109353323,
    885616641, 68124357, 437942295, 68124357, 885616641, 885616641,
    822915476811, 10395525, 870408315, 435204315, 5197605, 11714355,
    865074465, 9016526475, 865074465, 11714355, 185146462679, 11714355,
    6537232738345, 184346955, 5548905, 52295600376607
  ]
def negativeCoefficients : Array ℕ := #[
    5488549194066072236214714368, 50233285656627071467391025152, 70407787788324691568790339584, 43598700758581986556603531264, 2098695222850996247289921536, 43531000912683567322819985408,
    43734100450378825024170622976, 5488549194066072236214714368, 50233285656627071467391025152, 2098695222850996247289921536, 63027341703188768591720742912, 913326698238704821755302641664,
    46802533639710474952947793920, 54992977026659808069713657856, 649385154250982839972150640640, 1460239049558966818531971170304, 913326488985516636041725870080, 649385154250982839972150640640,
    46802533639710474952947793920, 45632470298717713079124099072, 45632470298717713079124099072, 45632470298717713079124099072, 1460239049558966818531971170304, 45632470298717713079124099072,
    63027550956376954305297514496, 54992977026659808069713657856, 426673985940740107602493440, 35725043723815130732810993664, 35725056652676883393992982528, 426661057078987446420504576,
    3347188844434812407447027712, 275748367918979587189959032832, 65346974095781238047112167424, 2464697601671772908709243518976, 34468733588983510178696527872, 2513345157530047617196621824,
    65346974095781238047112167424, 65346974095781238047112167424, 34468733588983510178696527872, 806424746258926706889087516672, 64628875479344081585055989760, 275748367918979587189959032832,
    65346974095781238047112167424, 2513345157530047617196621824, 64628875479344081585055989760, 2513345157530047617196621824, 65346974095781238047112167424, 65346974095781238047112167424,
    3706081834723433641993568256, 23970448648356185820364800, 2007024928304220827686010880, 2007025654644768729999605760, 23969722307808283506769920, 216091708673579854520647680,
    31915614521112421859202170880, 332651112636303047212086067200, 31915614521112421859202170880, 216091708673579854520647680, 3335302161320439378278875136, 216091708673579854520647680,
    117764315697778996711763476480, 1700300549826325697412464640, 204718460848654599019560960, 117759223184601827741360193536
  ]
def negativeScales : Array ℕ := #[
    21, 11, 23, 10, 7, 12,
    11, 21, 11, 7, 44, 48,
    32, 35, 39, 35, 47, 39,
    32, 35, 35, 35, 35, 35,
    43, 35, 27, 33, 32, 26,
    37, 43, 29, 48, 24, 26,
    29, 29, 24, 33, 28, 43,
    29, 26, 28, 26, 29, 29,
    39, 23, 29, 28, 22, 23,
    29, 33, 29, 23, 37, 23,
    42, 27, 22, 45
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21148483409343020, 11342630298678409, 23829721671853330, 10138271800172222, 7761551232733342, 12136029849385552,
    11142745276751530, 21148483409343020, 11342630298678409, 7761551232733342, 44669964472516731, 48527045758298338,
    32240573288588705, 35473234045379088, 39034989154938811, 35204047412563591, 47527045427761004, 39034989154938811,
    32240573288588705, 35204047412563591, 35204047412563591, 35204047412563591, 35204047412563591, 35204047412563591,
    43669969262311570, 35473234045379088, 27463264620032912, 33850922435642992, 32850922957752975, 26463220903546899,
    37435008510426918, 43799267099284846, 29722107090262552, 48959253509323431, 24799274951300834, 26021667372000733,
    29722107090262552, 29722107090262552, 24799274951300834, 33347454662343730, 28706165546356433, 43799267099284846,
    29722107090262552, 26021667372000733, 28706165546356433, 26021667372000733, 29722107090262552, 29722107090262552,
    39581953300112628, 23309459283953801, 29697117097868714, 28697117619978681, 22309415567467788, 23481774184872917,
    29688249083420169, 33069924610922346, 29688249083420169, 23481774184872917, 37429876030082785, 23481774184872917,
    42571817199521604, 27457848345627353, 22403771672871506, 45571754811332781
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
noncomputable def negativeCeiling : ℝ := 5777090037 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 70407787788324691568790339584, coefficient := (-70407787788324691568790339584) }, { argument := 43598700758581986556603531264, coefficient := (-43598700758581986556603531264) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 43531000912683567322819985408, coefficient := (-43531000912683567322819985408) }, { argument := 43734100450378825024170622976, coefficient := (-43734100450378825024170622976) }, { argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 63027341703188768591720742912, coefficient := (-63027341703188768591720742912) }, { argument := 913326698238704821755302641664, coefficient := (-913326698238704821755302641664) }, { argument := 46802533639710474952947793920, coefficient := (-46802533639710474952947793920) }, { argument := 54992977026659808069713657856, coefficient := (-54992977026659808069713657856) }, { argument := 649385154250982839972150640640, coefficient := (-649385154250982839972150640640) }, { argument := 1460239049558966818531971170304, coefficient := (-1460239049558966818531971170304) }, { argument := 913326488985516636041725870080, coefficient := (-913326488985516636041725870080) }, { argument := 649385154250982839972150640640, coefficient := (-649385154250982839972150640640) }, { argument := 46802533639710474952947793920, coefficient := (-46802533639710474952947793920) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 1460239049558966818531971170304, coefficient := (-1460239049558966818531971170304) }, { argument := 45632470298717713079124099072, coefficient := (-45632470298717713079124099072) }, { argument := 63027550956376954305297514496, coefficient := (-63027550956376954305297514496) }, { argument := 54992977026659808069713657856, coefficient := (-54992977026659808069713657856) }, { argument := 426673985940740107602493440, coefficient := (-426673985940740107602493440) }, { argument := 35725043723815130732810993664, coefficient := (-35725043723815130732810993664) }, { argument := 35725056652676883393992982528, coefficient := (-35725056652676883393992982528) }, { argument := 426661057078987446420504576, coefficient := (-426661057078987446420504576) }, { argument := 3347188844434812407447027712, coefficient := (-3347188844434812407447027712) }, { argument := 275748367918979587189959032832, coefficient := (-275748367918979587189959032832) }, { argument := 65346974095781238047112167424, coefficient := (-65346974095781238047112167424) }, { argument := 2464697601671772908709243518976, coefficient := (-2464697601671772908709243518976) }, { argument := 34468733588983510178696527872, coefficient := (-34468733588983510178696527872) }, { argument := 2513345157530047617196621824, coefficient := (-2513345157530047617196621824) }, { argument := 65346974095781238047112167424, coefficient := (-65346974095781238047112167424) }, { argument := 65346974095781238047112167424, coefficient := (-65346974095781238047112167424) }, { argument := 34468733588983510178696527872, coefficient := (-34468733588983510178696527872) }, { argument := 806424746258926706889087516672, coefficient := (-806424746258926706889087516672) }, { argument := 64628875479344081585055989760, coefficient := (-64628875479344081585055989760) }, { argument := 275748367918979587189959032832, coefficient := (-275748367918979587189959032832) }, { argument := 65346974095781238047112167424, coefficient := (-65346974095781238047112167424) }, { argument := 2513345157530047617196621824, coefficient := (-2513345157530047617196621824) }, { argument := 64628875479344081585055989760, coefficient := (-64628875479344081585055989760) }, { argument := 2513345157530047617196621824, coefficient := (-2513345157530047617196621824) }, { argument := 65346974095781238047112167424, coefficient := (-65346974095781238047112167424) }, { argument := 65346974095781238047112167424, coefficient := (-65346974095781238047112167424) }, { argument := 3706081834723433641993568256, coefficient := (-3706081834723433641993568256) }, { argument := 23970448648356185820364800, coefficient := (-23970448648356185820364800) }, { argument := 2007024928304220827686010880, coefficient := (-2007024928304220827686010880) }, { argument := 2007025654644768729999605760, coefficient := (-2007025654644768729999605760) }, { argument := 23969722307808283506769920, coefficient := (-23969722307808283506769920) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 332651112636303047212086067200, coefficient := (-332651112636303047212086067200) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 3335302161320439378278875136, coefficient := (-3335302161320439378278875136) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 117764315697778996711763476480, coefficient := (-117764315697778996711763476480) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 117759223184601827741360193536, coefficient := (-117759223184601827741360193536) }] }

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
def constantNumerator : ℤ := (-10388433708823590898319909948751872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5548905, 5548905, 475356195, 5548905, 184346955, 475356195,
    1483433231585, 5548905, 5548905, 11714355, 2324491, 2597,
    14909429, 1127, 217, 4501, 2261, 2324491,
    2597, 217, 101659837794613, 1463012841666251, 9228235775, 86745416285,
    1024334171025, 71980239045, 731506256589505, 1024334171025, 9228235775, 71980239045,
    71980239045, 71980239045, 71980239045, 71980239045, 50830083140927, 86745416285,
    6561868742305, 512606116541589, 33274892287, 17969743276656159, 1096974471, 2559607099,
    33274892287, 33274892287, 1096974471, 410634110311, 16454617065, 512606116541589,
    33274892287, 2559607099, 16454617065, 2559607099, 33274892287, 33274892287,
    29241664813749, 562051385, 47060076231, 23530046631, 281017177, 184346955,
    13613540265, 141891653475, 13613540265, 184346955
  ]
def negativeCoefficients : Array ℕ := #[
    204718460848654599019560960, 204718460848654599019560960, 8768774073017371991337861120, 204718460848654599019560960, 1700300549826325697412464640, 8768774073017371991337861120,
    3340394674497608348682158080, 204718460848654599019560960, 204718460848654599019560960, 216091708673579854520647680, 5488549194066072236214714368, 50233285656627071467391025152,
    70407787788324691568790339584, 43598700758581986556603531264, 2098695222850996247289921536, 43531000912683567322819985408, 43734100450378825024170622976, 5488549194066072236214714368,
    50233285656627071467391025152, 2098695222850996247289921536, 228917603805182086336451969024, 3294412044283189233937178165248, 170230903593275721181980262400, 200021311722098972388826808320,
    2361953787356700631399976140800, 5311204192110202500877784186880, 3294411304595681152156020244480, 2361953787356700631399976140800, 170230903593275721181980262400, 165975131003443828152430755840,
    165975131003443828152430755840, 165975131003443828152430755840, 5311204192110202500877784186880, 165975131003443828152430755840, 228918343492690168117609889792, 200021311722098972388826808320,
    118208118490795612967136133120, 9234290861778149064565982232576, 2455253688394163674181867143168, 80928529124692153484680693284864, 1295078868603514905062962888704, 94432834169006295160841043968,
    2455253688394163674181867143168, 2455253688394163674181867143168, 1295078868603514905062962888704, 30299449363369734133035569250304, 2428272878631590446993055416320, 9234290861778149064565982232576,
    2455253688394163674181867143168, 94432834169006295160841043968, 2428272878631590446993055416320, 94432834169006295160841043968, 2455253688394163674181867143168, 2455253688394163674181867143168,
    131692750758892940718457749504, 648001128460562223343861760, 54256573895157436375111827456, 54256593530563581334322675712, 647981493054417264133013504, 1700300549826325697412464640,
    251125493205595108839511818240, 2617439017848805555695098265600, 251125493205595108839511818240, 1700300549826325697412464640
  ]
def negativeScales : Array ℕ := #[
    22, 22, 28, 22, 27, 28,
    40, 22, 22, 23, 21, 11,
    23, 10, 7, 12, 11, 21,
    11, 7, 46, 50, 33, 36,
    39, 36, 49, 39, 33, 36,
    36, 36, 36, 36, 45, 36,
    42, 48, 34, 53, 30, 31,
    34, 34, 30, 38, 33, 48,
    34, 31, 33, 31, 34, 34,
    44, 29, 35, 34, 28, 27,
    33, 37, 33, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22403771672871506, 22403771672871506, 28824433722398829, 22403771672871506, 27457848345627353, 28824433722398829,
    40432077132113689, 22403771672871506, 22403771672871506, 23481774184872917, 21148483409343020, 11342630298678409,
    23829721671853330, 10138271800172222, 7761551232733342, 12136029849385552, 11142745276751530, 21148483409343020,
    11342630298678409, 7761551232733342, 46530743162403718, 50377863856168183, 33103407718332029, 36336068475122304,
    39897823588882392, 36066881842306915, 49377863532242819, 39897823588882392, 33103407718332029, 36066881842306915,
    36066881842306915, 36066881842306915, 36066881842306915, 36066881842306915, 45530747824088787, 36336068475122304,
    42577243874427865, 48864844024038808, 34953714956017648, 53996419338602035, 30030882805442719, 31253275226779167,
    34953714956017648, 34953714956017648, 30030882805442719, 38579062517125298, 33937773409518158, 48864844024038808,
    34953714956017648, 31253275226779167, 33937773409518158, 31253275226779167, 34953714956017648, 34953714956017648,
    44733090684179364, 29066126792562555, 35453784606409891, 34453785128519857, 28066083076076542, 27457848345627353,
    33664323244150467, 37045998771676865, 33664323244150467, 27457848345627353
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
noncomputable def negativeCeiling : ℝ := 100059871383 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }, { argument := 3340394674497608348682158080, coefficient := (-3340394674497608348682158080) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 70407787788324691568790339584, coefficient := (-70407787788324691568790339584) }, { argument := 43598700758581986556603531264, coefficient := (-43598700758581986556603531264) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 43531000912683567322819985408, coefficient := (-43531000912683567322819985408) }, { argument := 43734100450378825024170622976, coefficient := (-43734100450378825024170622976) }, { argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 228917603805182086336451969024, coefficient := (-228917603805182086336451969024) }, { argument := 3294412044283189233937178165248, coefficient := (-3294412044283189233937178165248) }, { argument := 170230903593275721181980262400, coefficient := (-170230903593275721181980262400) }, { argument := 200021311722098972388826808320, coefficient := (-200021311722098972388826808320) }, { argument := 2361953787356700631399976140800, coefficient := (-2361953787356700631399976140800) }, { argument := 5311204192110202500877784186880, coefficient := (-5311204192110202500877784186880) }, { argument := 3294411304595681152156020244480, coefficient := (-3294411304595681152156020244480) }, { argument := 2361953787356700631399976140800, coefficient := (-2361953787356700631399976140800) }, { argument := 170230903593275721181980262400, coefficient := (-170230903593275721181980262400) }, { argument := 165975131003443828152430755840, coefficient := (-165975131003443828152430755840) }, { argument := 165975131003443828152430755840, coefficient := (-165975131003443828152430755840) }, { argument := 165975131003443828152430755840, coefficient := (-165975131003443828152430755840) }, { argument := 5311204192110202500877784186880, coefficient := (-5311204192110202500877784186880) }, { argument := 165975131003443828152430755840, coefficient := (-165975131003443828152430755840) }, { argument := 228918343492690168117609889792, coefficient := (-228918343492690168117609889792) }, { argument := 200021311722098972388826808320, coefficient := (-200021311722098972388826808320) }, { argument := 118208118490795612967136133120, coefficient := (-118208118490795612967136133120) }, { argument := 9234290861778149064565982232576, coefficient := (-9234290861778149064565982232576) }, { argument := 2455253688394163674181867143168, coefficient := (-2455253688394163674181867143168) }, { argument := 80928529124692153484680693284864, coefficient := (-80928529124692153484680693284864) }, { argument := 1295078868603514905062962888704, coefficient := (-1295078868603514905062962888704) }, { argument := 94432834169006295160841043968, coefficient := (-94432834169006295160841043968) }, { argument := 2455253688394163674181867143168, coefficient := (-2455253688394163674181867143168) }, { argument := 2455253688394163674181867143168, coefficient := (-2455253688394163674181867143168) }, { argument := 1295078868603514905062962888704, coefficient := (-1295078868603514905062962888704) }, { argument := 30299449363369734133035569250304, coefficient := (-30299449363369734133035569250304) }, { argument := 2428272878631590446993055416320, coefficient := (-2428272878631590446993055416320) }, { argument := 9234290861778149064565982232576, coefficient := (-9234290861778149064565982232576) }, { argument := 2455253688394163674181867143168, coefficient := (-2455253688394163674181867143168) }, { argument := 94432834169006295160841043968, coefficient := (-94432834169006295160841043968) }, { argument := 2428272878631590446993055416320, coefficient := (-2428272878631590446993055416320) }, { argument := 94432834169006295160841043968, coefficient := (-94432834169006295160841043968) }, { argument := 2455253688394163674181867143168, coefficient := (-2455253688394163674181867143168) }, { argument := 2455253688394163674181867143168, coefficient := (-2455253688394163674181867143168) }, { argument := 131692750758892940718457749504, coefficient := (-131692750758892940718457749504) }, { argument := 648001128460562223343861760, coefficient := (-648001128460562223343861760) }, { argument := 54256573895157436375111827456, coefficient := (-54256573895157436375111827456) }, { argument := 54256593530563581334322675712, coefficient := (-54256593530563581334322675712) }, { argument := 647981493054417264133013504, coefficient := (-647981493054417264133013504) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 2617439017848805555695098265600, coefficient := (-2617439017848805555695098265600) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
