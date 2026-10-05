import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2

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
def constantNumerator : ℤ := (-40084763460399204620888164007936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    686527551951, 4088043208401, 411432783, 43549271323125, 183192699, 57060021,
    51053703, 51053703, 183192699, 7222597395, 183192699, 16352258212107,
    51053703, 57060021, 183192699, 57060021, 411432783, 51053703,
    341942530311, 98429542875, 16480752178505, 8240381628055, 393730213405, 686527551951,
    2426891288577, 42943146595, 2426891288577, 57542246499859, 1475612341, 611721862373621,
    657024473, 204646967, 183105181, 183105181, 657024473, 25903997665,
    657024473, 1798204543607, 183105181, 204646967, 657024473, 204646967,
    1475612341, 183105181, 2417051142679, 16480752178505, 335165648250765, 335165894370015,
    16481159566815, 4088043208401, 57542246499859, 16369838096041, 411432783, 1475612341,
    102858367, 42943146595, 16369838096041, 102858367, 174406060824375, 45798251,
    14265029, 12763447, 12763447, 45798251
  ]
def negativeCoefficients : Array ℕ := #[
    193240326696631402135289856, 4602727467507307630741684224, 474349703220942372190814208, 49032120525770594325626880000, 422413604328138462826856448, 65785725264218285194346496,
    470887296628088778233217024, 470887296628088778233217024, 422413604328138462826856448, 8327087855812893468021227520, 422413604328138462826856448, 4602751499419451146415112192,
    470887296628088778233217024, 65785725264218285194346496, 422413604328138462826856448, 65785725264218285194346496, 474349703220942372190814208, 470887296628088778233217024,
    192496531511343016713388032, 110821813153524564885504000, 4638919335618788011047649280, 4638922453687397395894108160, 110825202648453991817543680, 193240326696631402135289856,
    683109168931505004726976512, 193398739003358584105861120, 683109168931505004726976512, 16196702493426638756987797504, 1701265200402151750884130816, 172184396965014085835084005376,
    1514995287949361413196087296, 235941889106867761071521792, 1688847206238632395038261248, 1688847206238632395038261248, 1514995287949361413196087296, 29865275963264050809316311040,
    1514995287949361413196087296, 16196786625048836050354438144, 1688847206238632395038261248, 235941889106867761071521792, 1514995287949361413196087296, 235941889106867761071521792,
    1701265200402151750884130816, 1688847206238632395038261248, 680339414094035997555687424, 4638919335618788011047649280, 188681486071191998559871303680, 188681624624012322148114759680,
    4639034005233857454554480640, 4602727467507307630741684224, 16196702493426638756987797504, 4607699796840349831996112896, 474349703220942372190814208, 1701265200402151750884130816,
    474350492972173027880992768, 193398739003358584105861120, 4607699796840349831996112896, 474350492972173027880992768, 49090941908738206901207040000, 422414307610256273003511808,
    65785834791761222844809216, 470888080614711910889160704, 470888080614711910889160704, 422414307610256273003511808
  ]
def negativeScales : Array ℕ := #[
    39, 41, 28, 45, 27, 25,
    25, 25, 27, 32, 27, 43,
    25, 25, 27, 25, 28, 25,
    38, 36, 43, 42, 38, 39,
    41, 35, 41, 45, 30, 49,
    29, 27, 27, 27, 29, 34,
    29, 40, 27, 27, 29, 27,
    30, 27, 41, 43, 48, 48,
    43, 41, 45, 43, 28, 30,
    26, 35, 43, 26, 47, 25,
    23, 23, 23, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39320526664010205, 41894547587468691, 28616081511617104, 45307713813041622, 27448786766210737, 25765976942408995,
    25605512269904727, 25605512269904727, 27448786766210737, 32749870607529456, 27448786766210737, 43894555120096396,
    25605512269904727, 25765976942408995, 27448786766210737, 25765976942408995, 28616081511617104, 25605512269904727,
    38314962917988226, 36518372343324594, 43905847326744887, 42905848296458018, 38518416467604893, 39320526664010205,
    41142246623757286, 35321708855270188, 41142246623757286, 45709686779885097, 30458666613884642, 49119869166006635,
    29291371868486937, 27608562044374790, 27448097372174434, 27448097372174434, 29291371868486937, 34592455709586038,
    29291371868486937, 40709694273753629, 27448097372174434, 27608562044374790, 29291371868486937, 27608562044374790,
    30458666613884642, 27448097372174434, 41136385138234579, 43905847326744887, 48251867620545414, 48251868679946618,
    43905882988338174, 41894547587468691, 45709686779885097, 43896105290685032, 28616081511617104, 30458666613884642,
    26616083913577573, 35321708855270188, 43896105290685032, 26616083913577573, 47309443504829981, 25448789168171206,
    23765979344369480, 23605514671865197, 23605514671865197, 25448789168171206
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
noncomputable def negativeCeiling : ℝ := 449415107 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 193240326696631402135289856, coefficient := (-193240326696631402135289856) }, { argument := 4602727467507307630741684224, coefficient := (-4602727467507307630741684224) }, { argument := 474349703220942372190814208, coefficient := (-474349703220942372190814208) }, { argument := 49032120525770594325626880000, coefficient := (-49032120525770594325626880000) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 65785725264218285194346496, coefficient := (-65785725264218285194346496) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 8327087855812893468021227520, coefficient := (-8327087855812893468021227520) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 4602751499419451146415112192, coefficient := (-4602751499419451146415112192) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 65785725264218285194346496, coefficient := (-65785725264218285194346496) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 65785725264218285194346496, coefficient := (-65785725264218285194346496) }, { argument := 474349703220942372190814208, coefficient := (-474349703220942372190814208) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 192496531511343016713388032, coefficient := (-192496531511343016713388032) }, { argument := 110821813153524564885504000, coefficient := (-110821813153524564885504000) }, { argument := 4638919335618788011047649280, coefficient := (-4638919335618788011047649280) }, { argument := 4638922453687397395894108160, coefficient := (-4638922453687397395894108160) }, { argument := 110825202648453991817543680, coefficient := (-110825202648453991817543680) }, { argument := 193240326696631402135289856, coefficient := (-193240326696631402135289856) }, { argument := 683109168931505004726976512, coefficient := (-683109168931505004726976512) }, { argument := 193398739003358584105861120, coefficient := (-193398739003358584105861120) }, { argument := 683109168931505004726976512, coefficient := (-683109168931505004726976512) }, { argument := 16196702493426638756987797504, coefficient := (-16196702493426638756987797504) }, { argument := 1701265200402151750884130816, coefficient := (-1701265200402151750884130816) }, { argument := 172184396965014085835084005376, coefficient := (-172184396965014085835084005376) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 235941889106867761071521792, coefficient := (-235941889106867761071521792) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 29865275963264050809316311040, coefficient := (-29865275963264050809316311040) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 16196786625048836050354438144, coefficient := (-16196786625048836050354438144) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 235941889106867761071521792, coefficient := (-235941889106867761071521792) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 235941889106867761071521792, coefficient := (-235941889106867761071521792) }, { argument := 1701265200402151750884130816, coefficient := (-1701265200402151750884130816) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 680339414094035997555687424, coefficient := (-680339414094035997555687424) }, { argument := 4638919335618788011047649280, coefficient := (-4638919335618788011047649280) }, { argument := 188681486071191998559871303680, coefficient := (-188681486071191998559871303680) }, { argument := 188681624624012322148114759680, coefficient := (-188681624624012322148114759680) }, { argument := 4639034005233857454554480640, coefficient := (-4639034005233857454554480640) }, { argument := 4602727467507307630741684224, coefficient := (-4602727467507307630741684224) }, { argument := 16196702493426638756987797504, coefficient := (-16196702493426638756987797504) }, { argument := 4607699796840349831996112896, coefficient := (-4607699796840349831996112896) }, { argument := 474349703220942372190814208, coefficient := (-474349703220942372190814208) }, { argument := 1701265200402151750884130816, coefficient := (-1701265200402151750884130816) }, { argument := 474350492972173027880992768, coefficient := (-474350492972173027880992768) }, { argument := 193398739003358584105861120, coefficient := (-193398739003358584105861120) }, { argument := 4607699796840349831996112896, coefficient := (-4607699796840349831996112896) }, { argument := 474350492972173027880992768, coefficient := (-474350492972173027880992768) }, { argument := 49090941908738206901207040000, coefficient := (-49090941908738206901207040000) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }, { argument := 65785834791761222844809216, coefficient := (-65785834791761222844809216) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }] }

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
def constantNumerator : ℤ := (-39543597995828491038414103117824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1805652355, 45798251, 16369923584021, 12763447, 14265029, 45798251,
    14265029, 102858367, 12763447, 684456711131, 8240381628055, 335165894370015,
    41895767561175, 4120292661225, 43549271323125, 611721862373621, 174406060824375, 183192699,
    657024473, 45798251, 57060021, 204646967, 14265029, 51053703,
    183105181, 12763447, 51053703, 183105181, 12763447, 183192699,
    657024473, 45798251, 7222597395, 25903997665, 1805652355, 183192699,
    657024473, 45798251, 393730213405, 16481159566815, 4120292661225, 12304445475,
    16352258212107, 1798204543607, 16369923584021, 51053703, 183105181, 12763447,
    57060021, 204646967, 14265029, 183192699, 657024473, 45798251,
    57060021, 204646967, 14265029, 411432783, 1475612341, 102858367,
    51053703, 183105181, 12763447, 341942530311
  ]
def negativeCoefficients : Array ℕ := #[
    8327101719693986365356113920, 422414307610256273003511808, 4607723859567529373022027776, 470888080614711910889160704, 65785834791761222844809216, 422414307610256273003511808,
    65785834791761222844809216, 474350492972173027880992768, 470888080614711910889160704, 192657436825050426361511936, 4638922453687397395894108160, 188681624624012322148114759680,
    188681763176908643980070092800, 4639037123437574828222054400, 49032120525770594325626880000, 172184396965014085835084005376, 49090941908738206901207040000, 422413604328138462826856448,
    1514995287949361413196087296, 422414307610256273003511808, 65785725264218285194346496, 235941889106867761071521792, 65785834791761222844809216, 470887296628088778233217024,
    1688847206238632395038261248, 470888080614711910889160704, 470887296628088778233217024, 1688847206238632395038261248, 470888080614711910889160704, 422413604328138462826856448,
    1514995287949361413196087296, 422414307610256273003511808, 8327087855812893468021227520, 29865275963264050809316311040, 8327101719693986365356113920, 422413604328138462826856448,
    1514995287949361413196087296, 422414307610256273003511808, 110825202648453991817543680, 4639034005233857454554480640, 4639037123437574828222054400, 110828592112421171311411200,
    4602751499419451146415112192, 16196786625048836050354438144, 4607723859567529373022027776, 470887296628088778233217024, 1688847206238632395038261248, 470888080614711910889160704,
    65785725264218285194346496, 235941889106867761071521792, 65785834791761222844809216, 422413604328138462826856448, 1514995287949361413196087296, 422414307610256273003511808,
    65785725264218285194346496, 235941889106867761071521792, 65785834791761222844809216, 474349703220942372190814208, 1701265200402151750884130816, 474350492972173027880992768,
    470887296628088778233217024, 1688847206238632395038261248, 470888080614711910889160704, 192496531511343016713388032
  ]
def negativeScales : Array ℕ := #[
    30, 25, 43, 23, 23, 25,
    23, 26, 23, 39, 42, 48,
    45, 41, 45, 49, 47, 27,
    29, 25, 25, 27, 23, 25,
    27, 23, 25, 27, 23, 27,
    29, 25, 32, 34, 30, 27,
    29, 25, 38, 43, 41, 33,
    43, 40, 43, 25, 27, 23,
    25, 27, 23, 27, 29, 25,
    25, 27, 23, 28, 30, 26,
    25, 27, 23, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30749873009489936, 25448789168171206, 43896112824832352, 23605514671865197, 23765979344369480, 25448789168171206,
    23765979344369480, 26616083913577573, 23605514671865197, 39316168344029381, 42905848296458018, 48251868679946618,
    45251869739347624, 41905883958069354, 45307713813041622, 49119869166006635, 47309443504829981, 27448786766210737,
    29291371868486937, 25448789168171206, 25765976942408995, 27608562044374790, 23765979344369480, 25605512269904727,
    27448097372174434, 23605514671865197, 25605512269904727, 27448097372174434, 23605514671865197, 27448786766210737,
    29291371868486937, 25448789168171206, 32749870607529456, 34592455709586038, 30749873009489936, 27448786766210737,
    29291371868486937, 25448789168171206, 38518416467604893, 43905882988338174, 41905883958069354, 33518460590132661,
    43894555120096396, 40709694273753629, 43896112824832352, 25605512269904727, 27448097372174434, 23605514671865197,
    25765976942408995, 27608562044374790, 23765979344369480, 27448786766210737, 29291371868486937, 25448789168171206,
    25765976942408995, 27608562044374790, 23765979344369480, 28616081511617104, 30458666613884642, 26616083913577573,
    25605512269904727, 27448097372174434, 23605514671865197, 38314962917988226
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
noncomputable def negativeCeiling : ℝ := 212178823 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8327101719693986365356113920, coefficient := (-8327101719693986365356113920) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }, { argument := 4607723859567529373022027776, coefficient := (-4607723859567529373022027776) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 65785834791761222844809216, coefficient := (-65785834791761222844809216) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }, { argument := 65785834791761222844809216, coefficient := (-65785834791761222844809216) }, { argument := 474350492972173027880992768, coefficient := (-474350492972173027880992768) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 192657436825050426361511936, coefficient := (-192657436825050426361511936) }, { argument := 4638922453687397395894108160, coefficient := (-4638922453687397395894108160) }, { argument := 188681624624012322148114759680, coefficient := (-188681624624012322148114759680) }, { argument := 188681763176908643980070092800, coefficient := (-188681763176908643980070092800) }, { argument := 4639037123437574828222054400, coefficient := (-4639037123437574828222054400) }, { argument := 49032120525770594325626880000, coefficient := (-49032120525770594325626880000) }, { argument := 172184396965014085835084005376, coefficient := (-172184396965014085835084005376) }, { argument := 49090941908738206901207040000, coefficient := (-49090941908738206901207040000) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }, { argument := 65785725264218285194346496, coefficient := (-65785725264218285194346496) }, { argument := 235941889106867761071521792, coefficient := (-235941889106867761071521792) }, { argument := 65785834791761222844809216, coefficient := (-65785834791761222844809216) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }, { argument := 8327087855812893468021227520, coefficient := (-8327087855812893468021227520) }, { argument := 29865275963264050809316311040, coefficient := (-29865275963264050809316311040) }, { argument := 8327101719693986365356113920, coefficient := (-8327101719693986365356113920) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }, { argument := 110825202648453991817543680, coefficient := (-110825202648453991817543680) }, { argument := 4639034005233857454554480640, coefficient := (-4639034005233857454554480640) }, { argument := 4639037123437574828222054400, coefficient := (-4639037123437574828222054400) }, { argument := 110828592112421171311411200, coefficient := (-110828592112421171311411200) }, { argument := 4602751499419451146415112192, coefficient := (-4602751499419451146415112192) }, { argument := 16196786625048836050354438144, coefficient := (-16196786625048836050354438144) }, { argument := 4607723859567529373022027776, coefficient := (-4607723859567529373022027776) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 65785725264218285194346496, coefficient := (-65785725264218285194346496) }, { argument := 235941889106867761071521792, coefficient := (-235941889106867761071521792) }, { argument := 65785834791761222844809216, coefficient := (-65785834791761222844809216) }, { argument := 422413604328138462826856448, coefficient := (-422413604328138462826856448) }, { argument := 1514995287949361413196087296, coefficient := (-1514995287949361413196087296) }, { argument := 422414307610256273003511808, coefficient := (-422414307610256273003511808) }, { argument := 65785725264218285194346496, coefficient := (-65785725264218285194346496) }, { argument := 235941889106867761071521792, coefficient := (-235941889106867761071521792) }, { argument := 65785834791761222844809216, coefficient := (-65785834791761222844809216) }, { argument := 474349703220942372190814208, coefficient := (-474349703220942372190814208) }, { argument := 1701265200402151750884130816, coefficient := (-1701265200402151750884130816) }, { argument := 474350492972173027880992768, coefficient := (-474350492972173027880992768) }, { argument := 470887296628088778233217024, coefficient := (-470887296628088778233217024) }, { argument := 1688847206238632395038261248, coefficient := (-1688847206238632395038261248) }, { argument := 470888080614711910889160704, coefficient := (-470888080614711910889160704) }, { argument := 192496531511343016713388032, coefficient := (-192496531511343016713388032) }] }

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

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 82212894897588325503517969088512
def positiveArguments : Array ℕ := #[
    5, 7588323, 26759077, 949455, 2011595, 40937215,
    40937245, 2011645, 7079, 5380169, 137, 57239831,
    61, 19, 17, 17, 61, 2405,
    61, 5380197, 17, 19, 61, 19,
    137, 17, 225627
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 143339368785555339107717087232, 505464673349312068943890874368, 143477583007775967883831541760, 18998977610216327927289610240, 773282128072113932347176386560,
    773282694756091876704602030080, 18999449846864614891810979840, 2139496469262989981936254976, 50814259515548592439451189248, 5299930793190534301911875584, 540614918799045774123835850752,
    4719646399775512298052911104, 735026898325694538221355008, 5261245166962866168321277952, 5261245166962866168321277952, 4719646399775512298052911104, 93038931077541861285387304960,
    4719646399775512298052911104, 50814523968071633139583156224, 5261245166962866168321277952, 735026898325694538221355008, 4719646399775512298052911104, 735026898325694538221355008,
    5299930793190534301911875584, 5261245166962866168321277952, 2130986764860858881261174784
  ]
def positiveScales : Array ℕ := #[
    2, 22, 24, 19, 20, 25,
    25, 20, 12, 22, 7, 25,
    5, 4, 4, 4, 5, 11,
    5, 22, 4, 4, 5, 4,
    7, 4, 17
  ]
def negativeArguments : Array ℕ := #[
    2417051142679, 684456711131, 5, 5, 5
  ]
def negativeCoefficients : Array ℕ := #[
    680339414094035997555687424, 192657436825050426361511936, 792281625142643375935439503360, 1584563250285286751870879006720, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    41, 39, 2, 2, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 22855349658152649, 24673525018212144, 19856740098896912, 20939908441367631, 25286909621913434,
    25286910679162575, 20939944300402330, 12789329860060273, 22359220060253386, 7098032082960526, 25770516076718755,
    5930737337099561, 4247927513443585, 4087462841250339, 4087462841250339, 5930737337099561, 11231821178657404,
    5930737337099561, 22359227568448023, 4087462841250339, 4247927513443585, 5930737337099561, 4247927513443585,
    7098032082960526, 4087462841250339, 17783580194783893
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41136385138234579, 39316168344029381, 2321928094887363, 2321928094887363, 2321928094887363
  ]

abbrev PositiveTerm := Fin 27
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 960275259 / 1000000000000
noncomputable def negativeCeiling : ℝ := 89002581 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 680339414094035997555687424, coefficient := (-680339414094035997555687424) }, { argument := 192657436825050426361511936, coefficient := (-192657436825050426361511936) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 143339368785555339107717087232, coefficient := 143339368785555339107717087232 }, { argument := 505464673349312068943890874368, coefficient := 505464673349312068943890874368 }, { argument := 143477583007775967883831541760, coefficient := 143477583007775967883831541760 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 18998977610216327927289610240, coefficient := 18998977610216327927289610240 }, { argument := 773282128072113932347176386560, coefficient := 773282128072113932347176386560 }, { argument := 773282694756091876704602030080, coefficient := 773282694756091876704602030080 }, { argument := 18999449846864614891810979840, coefficient := 18999449846864614891810979840 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 2139496469262989981936254976, coefficient := 2139496469262989981936254976 }, { argument := 50814259515548592439451189248, coefficient := 50814259515548592439451189248 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 540614918799045774123835850752, coefficient := 540614918799045774123835850752 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 93038931077541861285387304960, coefficient := 93038931077541861285387304960 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 50814523968071633139583156224, coefficient := 50814523968071633139583156224 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 2130986764860858881261174784, coefficient := 2130986764860858881261174784 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2
