import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2

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
def constantNumerator : ℤ := 17428795590365449352252389064704
def positiveArguments : Array ℕ := #[
    5, 1, 1025, 509, 1025, 257
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 633825300114114700748351602688, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 39768823762042841331134365696
  ]
def positiveScales : Array ℕ := #[
    2, 0, 10, 8, 10, 8
  ]
def negativeArguments : Array ℕ := #[
    895707, 47, 12309137, 1163, 37, 12309143,
    19, 19, 643, 35, 1163, 643,
    895701, 37, 35, 47, 396669875, 10849929425,
    3173357975, 396669875, 196980455, 396669875, 99457715, 196980455,
    5387916173, 1575843131, 895707, 47, 396669875, 10849929425,
    3173357975, 10849929425, 5387916173, 10849929425, 2720421329, 12309137,
    1163, 37, 3173357975, 1575843131, 3173357975, 795661463,
    12309143, 19, 99457715, 2720421329, 795661463, 19,
    643, 35, 1163, 643, 895701, 37,
    35, 47, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4229856715271721305424003072, 909112216350201139379044352, 116256512003701232153556680704, 22495691651389019682932523008, 715684085211860471426056192, 116256568672099026589299245056,
    735026898325694538221355008, 735026898325694538221355008, 12437428832195304949377138688, 676998458984192337835458560, 22495691651389019682932523008, 12437428832195304949377138688,
    4229828381072824087552720896, 715684085211860471426056192, 676998458984192337835458560, 909112216350201139379044352, 3658633832937679312912384000, 12509116957549102061374668800,
    3658632651193137090894233600, 3658633832937679312912384000, 3633648040907861015165665280, 3658633832937679312912384000, 3669342029521887154803834880, 3633648040907861015165665280,
    12423688841741449657053085696, 3633646867233769325395443712, 4229856715271721305424003072, 909112216350201139379044352, 3658633832937679312912384000, 12509116957549102061374668800,
    3658632651193137090894233600, 12509116957549102061374668800, 12423688841741449657053085696, 12509116957549102061374668800, 12545729007180953091798204416, 116256512003701232153556680704,
    22495691651389019682932523008, 715684085211860471426056192, 3658632651193137090894233600, 3633646867233769325395443712, 3658632651193137090894233600, 3669340844318580418965143552,
    116256568672099026589299245056, 735026898325694538221355008, 3669342029521887154803834880, 12545729007180953091798204416, 3669340844318580418965143552, 735026898325694538221355008,
    12437428832195304949377138688, 676998458984192337835458560, 22495691651389019682932523008, 12437428832195304949377138688, 4229828381072824087552720896, 715684085211860471426056192,
    676998458984192337835458560, 909112216350201139379044352, 633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    19, 5, 23, 10, 5, 23,
    4, 4, 9, 5, 10, 9,
    19, 5, 5, 5, 28, 33,
    31, 28, 27, 28, 26, 27,
    32, 30, 19, 5, 28, 33,
    31, 33, 32, 33, 31, 23,
    10, 5, 31, 30, 31, 29,
    23, 4, 26, 31, 29, 4,
    9, 5, 10, 9, 19, 5,
    5, 5, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 10001408194392808, 8991521844801183, 10001408194392808, 8005624549193878
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    19772667355772277, 5554588851679165, 23553226281480972, 10183635381473219, 5209453365628950, 23553226984712087,
    4247927513443586, 4247927513443586, 9328674927327948, 5129283016944967, 10183635381473219, 9328674927327948,
    19772657691675307, 5209453365628950, 5129283016944967, 5554588851679165, 28563363595610066, 33336966607346729,
    31563363129617200, 28563363595610066, 27553477247292447, 28563363595610066, 26567579950411398, 27553477247292447,
    32327080259029616, 30553476781299580, 19772667355772277, 5554588851679165, 28563363595610066, 33336966607346729,
    31563363129617200, 33336966607346729, 32327080259029616, 33336966607346729, 31341182962147799, 23553226281480972,
    10183635381473219, 5209453365628950, 31563363129617200, 30553476781299580, 31563363129617200, 29567579484418532,
    23553226984712087, 4247927513443586, 26567579950411398, 31341182962147799, 29567579484418532, 4247927513443586,
    9328674927327948, 5129283016944967, 10183635381473219, 9328674927327948, 19772657691675307, 5209453365628950,
    5129283016944967, 5554588851679165, 0, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 39785693 / 1000000000000
noncomputable def negativeCeiling : ℝ := 213070663 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4229856715271721305424003072, coefficient := (-4229856715271721305424003072) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 116256512003701232153556680704, coefficient := (-116256512003701232153556680704) }, { argument := 22495691651389019682932523008, coefficient := (-22495691651389019682932523008) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 116256568672099026589299245056, coefficient := (-116256568672099026589299245056) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 12437428832195304949377138688, coefficient := (-12437428832195304949377138688) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 22495691651389019682932523008, coefficient := (-22495691651389019682932523008) }, { argument := 12437428832195304949377138688, coefficient := (-12437428832195304949377138688) }, { argument := 4229828381072824087552720896, coefficient := (-4229828381072824087552720896) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 3658633832937679312912384000, coefficient := (-3658633832937679312912384000) }, { argument := 12509116957549102061374668800, coefficient := (-12509116957549102061374668800) }, { argument := 3658632651193137090894233600, coefficient := (-3658632651193137090894233600) }, { argument := 3658633832937679312912384000, coefficient := (-3658633832937679312912384000) }, { argument := 3633648040907861015165665280, coefficient := (-3633648040907861015165665280) }, { argument := 3658633832937679312912384000, coefficient := (-3658633832937679312912384000) }, { argument := 3669342029521887154803834880, coefficient := (-3669342029521887154803834880) }, { argument := 3633648040907861015165665280, coefficient := (-3633648040907861015165665280) }, { argument := 12423688841741449657053085696, coefficient := (-12423688841741449657053085696) }, { argument := 3633646867233769325395443712, coefficient := (-3633646867233769325395443712) }, { argument := 4229856715271721305424003072, coefficient := (-4229856715271721305424003072) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 3658633832937679312912384000, coefficient := (-3658633832937679312912384000) }, { argument := 12509116957549102061374668800, coefficient := (-12509116957549102061374668800) }, { argument := 3658632651193137090894233600, coefficient := (-3658632651193137090894233600) }, { argument := 12509116957549102061374668800, coefficient := (-12509116957549102061374668800) }, { argument := 12423688841741449657053085696, coefficient := (-12423688841741449657053085696) }, { argument := 12509116957549102061374668800, coefficient := (-12509116957549102061374668800) }, { argument := 12545729007180953091798204416, coefficient := (-12545729007180953091798204416) }, { argument := 116256512003701232153556680704, coefficient := (-116256512003701232153556680704) }, { argument := 22495691651389019682932523008, coefficient := (-22495691651389019682932523008) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 3658632651193137090894233600, coefficient := (-3658632651193137090894233600) }, { argument := 3633646867233769325395443712, coefficient := (-3633646867233769325395443712) }, { argument := 3658632651193137090894233600, coefficient := (-3658632651193137090894233600) }, { argument := 3669340844318580418965143552, coefficient := (-3669340844318580418965143552) }, { argument := 116256568672099026589299245056, coefficient := (-116256568672099026589299245056) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 3669342029521887154803834880, coefficient := (-3669342029521887154803834880) }, { argument := 12545729007180953091798204416, coefficient := (-12545729007180953091798204416) }, { argument := 3669340844318580418965143552, coefficient := (-3669340844318580418965143552) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 12437428832195304949377138688, coefficient := (-12437428832195304949377138688) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 22495691651389019682932523008, coefficient := (-22495691651389019682932523008) }, { argument := 12437428832195304949377138688, coefficient := (-12437428832195304949377138688) }, { argument := 4229828381072824087552720896, coefficient := (-4229828381072824087552720896) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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
def constantNumerator : ℤ := (-17904164565451035377813652766720)
def positiveArguments : Array ℕ := #[
    386995, 10585297, 3095959, 895707, 47, 12309137,
    1163, 37, 12309143, 19, 19, 643,
    35, 1163, 643, 895701, 37, 35,
    47
  ]
def positiveCoefficients : Array ℕ := #[
    29240515472610213591588536320, 99975303528041213743201255424, 29240506027877247852298108928, 8459713430543442610848006144, 1818224432700402278758088704, 232513024007402464307113361408,
    44991383302778039365865046016, 1431368170423720942852112384, 232513137344198053178598490112, 1470053796651389076442710016, 1470053796651389076442710016, 24874857664390609898754277376,
    1353996917968384675670917120, 44991383302778039365865046016, 24874857664390609898754277376, 8459656762145648175105441792, 1431368170423720942852112384, 1353996917968384675670917120,
    1818224432700402278758088704
  ]
def positiveScales : Array ℕ := #[
    18, 23, 21, 19, 5, 23,
    10, 5, 23, 4, 4, 9,
    5, 10, 9, 19, 5, 5,
    5
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    18561955401215154, 23335558412953919, 21561954935222288, 19772667355383412, 5554588851677541, 23553226281479414,
    10183635381473218, 5209453365628949, 23553226984710529, 4247927513443585, 4247927513443585, 9328674927327946,
    5129283016944966, 10183635381473218, 9328674927327946, 19772657691286521, 5209453365628949, 5129283016944966,
    5554588851677541
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 19
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 195428601 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29240515472610213591588536320, coefficient := 29240515472610213591588536320 }, { argument := 99975303528041213743201255424, coefficient := 99975303528041213743201255424 }, { argument := 29240506027877247852298108928, coefficient := 29240506027877247852298108928 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 8459713430543442610848006144, coefficient := 8459713430543442610848006144 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 232513024007402464307113361408, coefficient := 232513024007402464307113361408 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 232513137344198053178598490112, coefficient := 232513137344198053178598490112 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 8459656762145648175105441792, coefficient := 8459656762145648175105441792 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2
