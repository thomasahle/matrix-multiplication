import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 6, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 43449, 2053709, 2053697, 43449, 51985,
    164479, 3510773, 1317071, 12309
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1641456810513625719119020032, 77586932377341889617395187712, 77586479030159534131454672896, 1641456810513625719119020032, 490984443223957012867973120,
    12427681867774662001656070144, 132633253953309703486585176064, 12439383891919212982495608832, 465020872301139703483072512
  ]
def positiveScales : Array ℕ := #[
    0, 15, 20, 20, 15, 15,
    17, 21, 20, 13
  ]
def negativeArguments : Array ℕ := #[
    2258696265, 7146448071, 152539576077, 57225417879, 534813741, 2258696265,
    106762062365, 106761438545, 2258696265, 106762062365, 337792002611, 7210106107057,
    2704880566339, 25279104081, 7146448071, 337792002611, 337790028863, 7146448071,
    106761438545, 337790028863, 7210063977781, 2704864761487, 25278956373, 152539576077,
    7210106107057, 7210063977781, 152539576077, 2258696265, 7146448071, 152539576077,
    57225417879, 534813741, 57225417879, 2704880566339, 2704864761487, 57225417879,
    534813741, 25279104081, 25278956373, 534813741, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2543065914349282771599360, 64369481739156399883026432, 686977177979630626057224192, 64430092658996329888874496, 2408586964680220958785536, 2543065914349282771599360,
    120203396071079913728245760, 120202693712200027162542080, 2543065914349282771599360, 120203396071079913728245760, 3042559874175266423792730112, 32471431177043642739979190272,
    3045424777661504146464833536, 113846963719451584732594176, 64369481739156399883026432, 3042559874175266423792730112, 3042542096233751777269252096, 64369481739156399883026432,
    120202693712200027162542080, 3042542096233751777269252096, 32471241443651947751198949376, 3045406982980109685005221888, 113846298501757825091371008, 686977177979630626057224192,
    32471431177043642739979190272, 32471241443651947751198949376, 686977177979630626057224192, 2543065914349282771599360, 64369481739156399883026432, 686977177979630626057224192,
    64430092658996329888874496, 2408586964680220958785536, 64430092658996329888874496, 3045424777661504146464833536, 3045406982980109685005221888, 64430092658996329888874496,
    2408586964680220958785536, 113846963719451584732594176, 113846298501757825091371008, 2408586964680220958785536, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    31, 32, 37, 35, 28, 31,
    36, 36, 31, 36, 38, 42,
    41, 34, 32, 38, 38, 32,
    36, 38, 42, 41, 34, 37,
    42, 42, 37, 31, 32, 37,
    35, 28, 35, 41, 41, 35,
    28, 34, 34, 28, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15407035352638768, 20969800342101301, 20969791912284412, 15407035352638768, 15665807780735268,
    17327543872805543, 21743357286589869, 20328901689092439, 13587425939613443
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31072843133376009, 32734579225604254, 37150392639240697, 35735937041896071, 28994461313921690, 31072843133376009,
    36635608123748314, 36635599693931297, 31072843133376009, 36635608123748314, 38297344215801911, 42713157629696640,
    41298702032088807, 34557226282611711, 32734579225604254, 38297344215801911, 38297335785984898, 32734579225604254,
    36635599693931297, 38297335785984898, 42713149199879607, 41298693602271793, 34557217852794697, 37150392639240697,
    42713157629696640, 42713149199879607, 37150392639240697, 31072843133376009, 32734579225604254, 37150392639240697,
    35735937041896071, 28994461313921690, 35735937041896071, 41298702032088807, 41298693602271793, 35735937041896071,
    28994461313921690, 34557226282611711, 34557217852794697, 28994461313921690, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 20073779 / 250000000000
noncomputable def negativeCeiling : ℝ := 80295117 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2543065914349282771599360, coefficient := (-2543065914349282771599360) }, { argument := 64369481739156399883026432, coefficient := (-64369481739156399883026432) }, { argument := 686977177979630626057224192, coefficient := (-686977177979630626057224192) }, { argument := 64430092658996329888874496, coefficient := (-64430092658996329888874496) }, { argument := 2408586964680220958785536, coefficient := (-2408586964680220958785536) }, { argument := 2543065914349282771599360, coefficient := (-2543065914349282771599360) }, { argument := 120203396071079913728245760, coefficient := (-120203396071079913728245760) }, { argument := 120202693712200027162542080, coefficient := (-120202693712200027162542080) }, { argument := 2543065914349282771599360, coefficient := (-2543065914349282771599360) }, { argument := 120203396071079913728245760, coefficient := (-120203396071079913728245760) }, { argument := 3042559874175266423792730112, coefficient := (-3042559874175266423792730112) }, { argument := 32471431177043642739979190272, coefficient := (-32471431177043642739979190272) }, { argument := 3045424777661504146464833536, coefficient := (-3045424777661504146464833536) }, { argument := 113846963719451584732594176, coefficient := (-113846963719451584732594176) }, { argument := 64369481739156399883026432, coefficient := (-64369481739156399883026432) }, { argument := 3042559874175266423792730112, coefficient := (-3042559874175266423792730112) }, { argument := 3042542096233751777269252096, coefficient := (-3042542096233751777269252096) }, { argument := 64369481739156399883026432, coefficient := (-64369481739156399883026432) }, { argument := 120202693712200027162542080, coefficient := (-120202693712200027162542080) }, { argument := 3042542096233751777269252096, coefficient := (-3042542096233751777269252096) }, { argument := 32471241443651947751198949376, coefficient := (-32471241443651947751198949376) }, { argument := 3045406982980109685005221888, coefficient := (-3045406982980109685005221888) }, { argument := 113846298501757825091371008, coefficient := (-113846298501757825091371008) }, { argument := 686977177979630626057224192, coefficient := (-686977177979630626057224192) }, { argument := 32471431177043642739979190272, coefficient := (-32471431177043642739979190272) }, { argument := 32471241443651947751198949376, coefficient := (-32471241443651947751198949376) }, { argument := 686977177979630626057224192, coefficient := (-686977177979630626057224192) }, { argument := 2543065914349282771599360, coefficient := (-2543065914349282771599360) }, { argument := 64369481739156399883026432, coefficient := (-64369481739156399883026432) }, { argument := 686977177979630626057224192, coefficient := (-686977177979630626057224192) }, { argument := 64430092658996329888874496, coefficient := (-64430092658996329888874496) }, { argument := 2408586964680220958785536, coefficient := (-2408586964680220958785536) }, { argument := 64430092658996329888874496, coefficient := (-64430092658996329888874496) }, { argument := 3045424777661504146464833536, coefficient := (-3045424777661504146464833536) }, { argument := 3045406982980109685005221888, coefficient := (-3045406982980109685005221888) }, { argument := 64430092658996329888874496, coefficient := (-64430092658996329888874496) }, { argument := 2408586964680220958785536, coefficient := (-2408586964680220958785536) }, { argument := 113846963719451584732594176, coefficient := (-113846963719451584732594176) }, { argument := 113846298501757825091371008, coefficient := (-113846298501757825091371008) }, { argument := 2408586964680220958785536, coefficient := (-2408586964680220958785536) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 1641456810513625719119020032, coefficient := 1641456810513625719119020032 }, { argument := 77586932377341889617395187712, coefficient := 77586932377341889617395187712 }, { argument := 77586479030159534131454672896, coefficient := 77586479030159534131454672896 }, { argument := 1641456810513625719119020032, coefficient := 1641456810513625719119020032 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 490984443223957012867973120, coefficient := 490984443223957012867973120 }, { argument := 12427681867774662001656070144, coefficient := 12427681867774662001656070144 }, { argument := 132633253953309703486585176064, coefficient := 132633253953309703486585176064 }, { argument := 12439383891919212982495608832, coefficient := 12439383891919212982495608832 }, { argument := 465020872301139703483072512, coefficient := 465020872301139703483072512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6
