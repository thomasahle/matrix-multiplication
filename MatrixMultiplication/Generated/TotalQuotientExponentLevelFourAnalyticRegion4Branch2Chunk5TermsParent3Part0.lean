import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5

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
def constantNumerator : ℤ := 9550160194964430761097745661952
def positiveArguments : Array ℕ := #[
    9, 33554423, 33554441, 60539495, 104701, 60577177,
    868029, 32686387, 65372825, 1736071
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 633825130108921317441123909632, 633825470119308084055579295744, 571779364155708944132645847040, 2025211875831540627534581334016, 572135260583323932074530832384,
    16396604223035421060797300736, 617428393659624376030260625408, 617428875341005628734072422400, 16396727004563975671572856832
  ]
def positiveScales : Array ℕ := #[
    3, 24, 25, 25, 16, 25,
    19, 24, 25, 20
  ]
def negativeArguments : Array ℕ := #[
    3640776075383, 274193214844723, 274193428754035, 1820401669211, 91620742835859, 81135995944191,
    91677365460337, 3640776075383, 3640778938249, 3640778938249, 274193360113869, 274193574023565,
    1820403100581, 81135995944191, 287364664957101, 20296677489301, 274193214844723, 274193360113869,
    91677365460337, 20296677489301, 91733986310463, 274193428754035, 274193574023565, 1820401669211,
    1820403100581, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4099149444108573913741524992, 154357057525276606880678936576, 154357177945513833665574993920, 4099180139561644260566499328, 51577892911872829170288427008, 182702020550296331185047994368,
    51609768615685311710986502144, 4099149444108573913741524992, 4099152667409136616657125376, 4099152667409136616657125376, 154357139304535581134451376128, 154357259724988980701461217280,
    4099183362720343575219929088, 182702020550296331185047994368, 647087699010123746754636546048, 182816218355350235827606126592, 154357057525276606880678936576, 154357139304535581134451376128,
    51609768615685311710986502144, 182816218355350235827606126592, 51641643320626418498672787456, 154357177945513833665574993920, 154357259724988980701461217280, 4099180139561644260566499328,
    4099183362720343575219929088, 1267650600228229401496703205376, 3169126500570573503741758013440, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    41, 47, 47, 40, 46, 46,
    46, 41, 41, 41, 47, 47,
    40, 46, 48, 44, 47, 47,
    46, 44, 46, 47, 47, 40,
    40, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 24999999611579411, 25000000386960912, 25851373304842837, 16675915695959466, 25852271011744329,
    19727383716933712, 24962186580593299, 25962187706098810, 20727394520124220
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41727383149858256, 47962186211995447, 47962187337500500, 40727393953078012, 46380739493414834, 46205407340935764,
    46381630819385344, 41727383149858256, 41727384284297970, 41727384284297970, 47962186976343557, 47962188101850035,
    40727395087459302, 46205407340935764, 48029876003909344, 44206308815033940, 47962186211995447, 47962186976343557,
    46381630819385344, 44206308815033940, 46382521567111633, 47962187337500500, 47962188101850035, 40727393953078012,
    40727395087459302, 0, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 1639238417 / 1000000000000
noncomputable def negativeCeiling : ℝ := 340981921 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4099149444108573913741524992, coefficient := (-4099149444108573913741524992) }, { argument := 154357057525276606880678936576, coefficient := (-154357057525276606880678936576) }, { argument := 154357177945513833665574993920, coefficient := (-154357177945513833665574993920) }, { argument := 4099180139561644260566499328, coefficient := (-4099180139561644260566499328) }, { argument := 51577892911872829170288427008, coefficient := (-51577892911872829170288427008) }, { argument := 182702020550296331185047994368, coefficient := (-182702020550296331185047994368) }, { argument := 51609768615685311710986502144, coefficient := (-51609768615685311710986502144) }, { argument := 4099149444108573913741524992, coefficient := (-4099149444108573913741524992) }, { argument := 4099152667409136616657125376, coefficient := (-4099152667409136616657125376) }, { argument := 4099152667409136616657125376, coefficient := (-4099152667409136616657125376) }, { argument := 154357139304535581134451376128, coefficient := (-154357139304535581134451376128) }, { argument := 154357259724988980701461217280, coefficient := (-154357259724988980701461217280) }, { argument := 4099183362720343575219929088, coefficient := (-4099183362720343575219929088) }, { argument := 182702020550296331185047994368, coefficient := (-182702020550296331185047994368) }, { argument := 647087699010123746754636546048, coefficient := (-647087699010123746754636546048) }, { argument := 182816218355350235827606126592, coefficient := (-182816218355350235827606126592) }, { argument := 154357057525276606880678936576, coefficient := (-154357057525276606880678936576) }, { argument := 154357139304535581134451376128, coefficient := (-154357139304535581134451376128) }, { argument := 51609768615685311710986502144, coefficient := (-51609768615685311710986502144) }, { argument := 182816218355350235827606126592, coefficient := (-182816218355350235827606126592) }, { argument := 51641643320626418498672787456, coefficient := (-51641643320626418498672787456) }, { argument := 154357177945513833665574993920, coefficient := (-154357177945513833665574993920) }, { argument := 154357259724988980701461217280, coefficient := (-154357259724988980701461217280) }, { argument := 4099180139561644260566499328, coefficient := (-4099180139561644260566499328) }, { argument := 4099183362720343575219929088, coefficient := (-4099183362720343575219929088) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 633825130108921317441123909632, coefficient := 633825130108921317441123909632 }, { argument := 633825470119308084055579295744, coefficient := 633825470119308084055579295744 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 571779364155708944132645847040, coefficient := 571779364155708944132645847040 }, { argument := 2025211875831540627534581334016, coefficient := 2025211875831540627534581334016 }, { argument := 572135260583323932074530832384, coefficient := 572135260583323932074530832384 }, { argument := 3169126500570573503741758013440, coefficient := (-3169126500570573503741758013440) }, { argument := 16396604223035421060797300736, coefficient := 16396604223035421060797300736 }, { argument := 617428393659624376030260625408, coefficient := 617428393659624376030260625408 }, { argument := 617428875341005628734072422400, coefficient := 617428875341005628734072422400 }, { argument := 16396727004563975671572856832, coefficient := 16396727004563975671572856832 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5
