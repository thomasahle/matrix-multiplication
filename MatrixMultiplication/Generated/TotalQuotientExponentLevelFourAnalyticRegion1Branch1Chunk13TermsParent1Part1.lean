import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-15456389254581280587854185517547520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    30105, 30537, 31725, 743013, 421335, 344385,
    4575285, 810675, 344385, 810675, 400005, 31716603,
    811593, 4575285, 31716603, 743013, 400005, 811593,
    421335, 13896894855487585, 50797792296892783, 868509377025635, 32913, 74655,
    15255, 810675, 17955, 15255, 17955, 70875,
    702459, 71901, 810675, 702459, 32913, 70875,
    71901, 74655, 3920101257, 228807667343, 62721628385, 445227455290309,
    445227528545339, 74165280261853, 216761084429685, 65019745245, 142372629034712947, 5101746975,
    4548035505, 129579435765, 33106297965, 5101746975, 2035315303515, 130295773725,
    13872732587237779, 129579435765, 4548035505, 130295773725, 4548035505, 129579435765,
    16599977355, 74165280261853, 35066698230466963, 31725
  ]
def negativeCoefficients : Array ℕ := #[
    284333685933581338316636160, 288413810574780711781269504, 299634153338078988809011200, 3508779687536423699163906048, 3979396564119763932225208320, 3252624362406125533837393920,
    43212345067152489403090206720, 3828304448500349633613004800, 3252624362406125533837393920, 3828304448500349633613004800, 3777940409960544867408936960, 149777422957682837993646194688,
    3832639580931623967919177728, 43212345067152489403090206720, 149777422957682837993646194688, 3508779687536423699163906048, 3777940409960544867408936960, 3832639580931623967919177728,
    3979396564119763932225208320, 15646512623195212666377380823040, 57193229614882547408155382382592, 15645674026961725622354538659840, 310854496101377265836752896, 352548269778633363428474880,
    288158802784705750939729920, 3828304448500349633613004800, 339160360799697919247646720, 288158802784705750939729920, 339160360799697919247646720, 334697724473386104520704000,
    13269075348760512428670713856, 339542872484810360509956096, 3828304448500349633613004800, 13269075348760512428670713856, 310854496101377265836752896, 334697724473386104520704000,
    339542872484810360509956096, 352548269778633363428474880, 144626209261812227885575962624, 527594560197348969769427009536, 144626228338051443110466027520, 125320387608784361274373832704,
    125320408228242224462780432384, 83502682137777393201181622272, 15619282225055263815429689180160, 149925325034038568524437258240, 160297329767122771932028944252928, 94110620776646881985534361600,
    5243527937429961112949882880, 149394918048290079305776496640, 152675851447081584666460815360, 94110620776646881985534361600, 2346558782077855223704599920640, 150220799486940278670596505600,
    15619308327623649599337420292096, 149394918048290079305776496640, 5243527937429961112949882880, 150220799486940278670596505600, 5243527937429961112949882880, 149394918048290079305776496640,
    153107766948529503836401827840, 83502682137777393201181622272, 19740796135480580753777236115456, 299634153338078988809011200
  ]
def negativeScales : Array ℕ := #[
    14, 14, 14, 19, 18, 18,
    22, 19, 18, 19, 18, 24,
    19, 22, 24, 19, 18, 19,
    18, 53, 55, 49, 15, 16,
    13, 19, 14, 13, 14, 16,
    19, 16, 19, 19, 15, 16,
    16, 16, 31, 37, 35, 48,
    48, 46, 47, 35, 56, 32,
    32, 36, 34, 32, 40, 36,
    53, 36, 32, 36, 32, 36,
    33, 46, 54, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14877715499884064, 14898270720387434, 14953332554642086, 19503027927289084, 18684608239020224, 18393662780653309,
    22125430182727480, 19628764127656122, 18393662780653309, 19628764127656122, 18609658508019485, 24918734930070916,
    19630396896334709, 22125430182727480, 24918734930070916, 19503027927289084, 18609658508019485, 19630396896334709,
    18684608239020224, 53625612079068953, 55495615316149499, 49625534753783792, 15006369912783681, 16187951267285539,
    13896994563604115, 19628764127656122, 14132098032552021, 13896994563604115, 14132098032552021, 16112989209604316,
    19422054497317946, 16133724215374083, 19628764127656122, 19422054497317946, 15006369912783681, 16112989209604316,
    16133724215374083, 16187951267285539, 31868243776353485, 37735344441548652, 35868243966645378, 48661535888763678,
    48661536126135967, 46075809195088222, 47623099098318396, 35920158858505865, 56982449447522018, 32248344203149160,
    32082596370900566, 36915045830390993, 34946386652406099, 32248344203149160, 40888389450971835, 36922999339714379,
    53623101509313598, 36915045830390993, 32082596370900566, 36922999339714379, 32082596370900566, 36915045830390993,
    33950462232888189, 46075809195088222, 54960951128102163, 14953332554642086
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
noncomputable def negativeCeiling : ℝ := 202181668793 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 43212345067152489403090206720, coefficient := (-43212345067152489403090206720) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 43212345067152489403090206720, coefficient := (-43212345067152489403090206720) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }, { argument := 3508779687536423699163906048, coefficient := (-3508779687536423699163906048) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 3832639580931623967919177728, coefficient := (-3832639580931623967919177728) }, { argument := 3979396564119763932225208320, coefficient := (-3979396564119763932225208320) }, { argument := 15646512623195212666377380823040, coefficient := (-15646512623195212666377380823040) }, { argument := 57193229614882547408155382382592, coefficient := (-57193229614882547408155382382592) }, { argument := 15645674026961725622354538659840, coefficient := (-15645674026961725622354538659840) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 339160360799697919247646720, coefficient := (-339160360799697919247646720) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 339160360799697919247646720, coefficient := (-339160360799697919247646720) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 144626209261812227885575962624, coefficient := (-144626209261812227885575962624) }, { argument := 527594560197348969769427009536, coefficient := (-527594560197348969769427009536) }, { argument := 144626228338051443110466027520, coefficient := (-144626228338051443110466027520) }, { argument := 125320387608784361274373832704, coefficient := (-125320387608784361274373832704) }, { argument := 125320408228242224462780432384, coefficient := (-125320408228242224462780432384) }, { argument := 83502682137777393201181622272, coefficient := (-83502682137777393201181622272) }, { argument := 15619282225055263815429689180160, coefficient := (-15619282225055263815429689180160) }, { argument := 149925325034038568524437258240, coefficient := (-149925325034038568524437258240) }, { argument := 160297329767122771932028944252928, coefficient := (-160297329767122771932028944252928) }, { argument := 94110620776646881985534361600, coefficient := (-94110620776646881985534361600) }, { argument := 5243527937429961112949882880, coefficient := (-5243527937429961112949882880) }, { argument := 149394918048290079305776496640, coefficient := (-149394918048290079305776496640) }, { argument := 152675851447081584666460815360, coefficient := (-152675851447081584666460815360) }, { argument := 94110620776646881985534361600, coefficient := (-94110620776646881985534361600) }, { argument := 2346558782077855223704599920640, coefficient := (-2346558782077855223704599920640) }, { argument := 150220799486940278670596505600, coefficient := (-150220799486940278670596505600) }, { argument := 15619308327623649599337420292096, coefficient := (-15619308327623649599337420292096) }, { argument := 149394918048290079305776496640, coefficient := (-149394918048290079305776496640) }, { argument := 5243527937429961112949882880, coefficient := (-5243527937429961112949882880) }, { argument := 150220799486940278670596505600, coefficient := (-150220799486940278670596505600) }, { argument := 5243527937429961112949882880, coefficient := (-5243527937429961112949882880) }, { argument := 149394918048290079305776496640, coefficient := (-149394918048290079305776496640) }, { argument := 153107766948529503836401827840, coefficient := (-153107766948529503836401827840) }, { argument := 83502682137777393201181622272, coefficient := (-83502682137777393201181622272) }, { argument := 19740796135480580753777236115456, coefficient := (-19740796135480580753777236115456) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-123034192956225151334591429385125888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    687103165668159449, 344385, 15255, 1374206480992478839, 15255, 30105,
    596511, 30537, 344385, 596511, 8766731285847057, 30105,
    30537, 31725, 570641099315321061, 2087076162685495919, 142651487665856299, 32913,
    74655, 15255, 810675, 17955, 15255, 17955,
    70875, 702459, 71901, 810675, 702459, 32913,
    70875, 71901, 74655, 1230528093, 4488905375, 307632065,
    53246812076647483, 53246810944166853, 68650503, 16026237327, 4393632945, 15560864199,
    15560871481, 3960663, 64989, 36855, 30105, 400005,
    70875, 30105, 70875, 34965, 2770659, 70929,
    400005, 2770659, 64989, 34965, 70929, 36855,
    1290249, 2927367, 596511, 31716603
  ]
def negativeCoefficients : Array ℕ := #[
    773609390217052768690078981554176, 3252624362406125533837393920, 288158802784705750939729920, 773609474465981036688447811616768, 288158802784705750939729920, 284333685933581338316636160,
    11267774212252219744268058624, 288413810574780711781269504, 3252624362406125533837393920, 11267774212252219744268058624, 19740923876099037579364465115136, 284333685933581338316636160,
    288413810574780711781269504, 299634153338078988809011200, 160621190139923133152298339926016, 587459714285265256818046731812864, 160611296673949333596562392088576, 310854496101377265836752896,
    352548269778633363428474880, 288158802784705750939729920, 3828304448500349633613004800, 339160360799697919247646720, 288158802784705750939729920, 339160360799697919247646720,
    334697724473386104520704000, 13269075348760512428670713856, 339542872484810360509956096, 3828304448500349633613004800, 13269075348760512428670713856, 310854496101377265836752896,
    334697724473386104520704000, 339542872484810360509956096, 352548269778633363428474880, 90796947228323463943686193152, 331222754494896809751609344000, 90796959550748505181666672640,
    14987645189191026921027401678848, 14987644870426067966508367085568, 5065513037489719177371451392, 18476993652231253466548273152, 5065513905639612146327224320, 35880909930587797358219624448,
    35880926721736590452338982912, 18703702201141937621012840448, 306901875355215372792889344, 348085633452321548701532160, 284333685933581338316636160, 3777940409960544867408936960,
    334697724473386104520704000, 284333685933581338316636160, 334697724473386104520704000, 330235088147074289793761280, 13084067197061128338133745664, 334952732263461065362243584,
    3777940409960544867408936960, 13084067197061128338133745664, 306901875355215372792889344, 330235088147074289793761280, 334952732263461065362243584, 348085633452321548701532160,
    12186057264312153734652100608, 13824099803858664700281618432, 11267774212252219744268058624, 149777422957682837993646194688
  ]
def negativeScales : Array ℕ := #[
    59, 18, 13, 60, 13, 14,
    19, 14, 18, 19, 52, 14,
    14, 14, 58, 60, 56, 15,
    16, 13, 19, 14, 13, 14,
    16, 19, 16, 19, 19, 15,
    16, 16, 16, 30, 32, 28,
    55, 55, 26, 33, 32, 33,
    33, 21, 15, 15, 14, 18,
    16, 14, 16, 15, 21, 16,
    18, 21, 15, 15, 16, 15,
    20, 21, 19, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    59253304343021823, 18393662780653309, 13896994563604115, 60253304500136648, 13896994563604115, 14877715499884064,
    19186189216714610, 14898270720387434, 18393662780653309, 19186189216714610, 52960960463601994, 14877715499884064,
    14898270720387434, 14953332554642086, 58985361289762717, 60856188958968636, 56985272424164034, 15006369912783681,
    16187951267285539, 13896994563604115, 19628764127656122, 14132098032552021, 13896994563604115, 14132098032552021,
    16112989209604316, 19422054497317946, 16133724215374083, 19628764127656122, 19422054497317946, 15006369912783681,
    16112989209604316, 16133724215374083, 16187951267285539, 30196630448937258, 32063716538910451, 28196630644731289,
    55563544670977004, 55563544640293022, 26032766955202224, 33899716699555487, 32032767202457621, 33857203135926194,
    33857203811062427, 21917310527473222, 15987907948136922, 15169572737970684, 14877715499884064, 18609658508019485,
    16112989209604316, 14877715499884064, 16112989209604316, 15093623884737385, 21401797730781646, 16114087987297101,
    18609658508019485, 21401797730781646, 15987907948136922, 15093623884737385, 16114087987297101, 15169572737970684,
    20299218081794152, 21481172195115125, 19186189216714610, 24918734930070916
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
noncomputable def negativeCeiling : ℝ := 1800335860981 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 773609390217052768690078981554176, coefficient := (-773609390217052768690078981554176) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 773609474465981036688447811616768, coefficient := (-773609474465981036688447811616768) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 3252624362406125533837393920, coefficient := (-3252624362406125533837393920) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 19740923876099037579364465115136, coefficient := (-19740923876099037579364465115136) }, { argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 288413810574780711781269504, coefficient := (-288413810574780711781269504) }, { argument := 299634153338078988809011200, coefficient := (-299634153338078988809011200) }, { argument := 160621190139923133152298339926016, coefficient := (-160621190139923133152298339926016) }, { argument := 587459714285265256818046731812864, coefficient := (-587459714285265256818046731812864) }, { argument := 160611296673949333596562392088576, coefficient := (-160611296673949333596562392088576) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 339160360799697919247646720, coefficient := (-339160360799697919247646720) }, { argument := 288158802784705750939729920, coefficient := (-288158802784705750939729920) }, { argument := 339160360799697919247646720, coefficient := (-339160360799697919247646720) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 3828304448500349633613004800, coefficient := (-3828304448500349633613004800) }, { argument := 13269075348760512428670713856, coefficient := (-13269075348760512428670713856) }, { argument := 310854496101377265836752896, coefficient := (-310854496101377265836752896) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 339542872484810360509956096, coefficient := (-339542872484810360509956096) }, { argument := 352548269778633363428474880, coefficient := (-352548269778633363428474880) }, { argument := 90796947228323463943686193152, coefficient := (-90796947228323463943686193152) }, { argument := 331222754494896809751609344000, coefficient := (-331222754494896809751609344000) }, { argument := 90796959550748505181666672640, coefficient := (-90796959550748505181666672640) }, { argument := 14987645189191026921027401678848, coefficient := (-14987645189191026921027401678848) }, { argument := 14987644870426067966508367085568, coefficient := (-14987644870426067966508367085568) }, { argument := 5065513037489719177371451392, coefficient := (-5065513037489719177371451392) }, { argument := 18476993652231253466548273152, coefficient := (-18476993652231253466548273152) }, { argument := 5065513905639612146327224320, coefficient := (-5065513905639612146327224320) }, { argument := 35880909930587797358219624448, coefficient := (-35880909930587797358219624448) }, { argument := 35880926721736590452338982912, coefficient := (-35880926721736590452338982912) }, { argument := 18703702201141937621012840448, coefficient := (-18703702201141937621012840448) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }, { argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 284333685933581338316636160, coefficient := (-284333685933581338316636160) }, { argument := 334697724473386104520704000, coefficient := (-334697724473386104520704000) }, { argument := 330235088147074289793761280, coefficient := (-330235088147074289793761280) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 3777940409960544867408936960, coefficient := (-3777940409960544867408936960) }, { argument := 13084067197061128338133745664, coefficient := (-13084067197061128338133745664) }, { argument := 306901875355215372792889344, coefficient := (-306901875355215372792889344) }, { argument := 330235088147074289793761280, coefficient := (-330235088147074289793761280) }, { argument := 334952732263461065362243584, coefficient := (-334952732263461065362243584) }, { argument := 348085633452321548701532160, coefficient := (-348085633452321548701532160) }, { argument := 12186057264312153734652100608, coefficient := (-12186057264312153734652100608) }, { argument := 13824099803858664700281618432, coefficient := (-13824099803858664700281618432) }, { argument := 11267774212252219744268058624, coefficient := (-11267774212252219744268058624) }, { argument := 149777422957682837993646194688, coefficient := (-149777422957682837993646194688) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
