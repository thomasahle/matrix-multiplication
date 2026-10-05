import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    1, 44063, 599905, 3572369, 1199817, 22025
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 416163268669370354102173696, 11331885059623658047689195520, 134960285040340412819247726592, 11331951172754418222722187264, 416040487140815743326617600
  ]
def positiveScales : Array ℕ := #[
    0, 15, 19, 21, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    1941547969, 26433614015, 157409295247, 52867536471, 970487575, 26433614015,
    359886009025, 2143082024945, 719776217385, 13212907625, 157409295247, 2143082024945,
    12761820272161, 4286189056473, 78681427225, 52867536471, 719776217385, 4286189056473,
    1439560833489, 26425969425, 970487575, 13212907625, 78681427225, 26425969425,
    485100625, 1
  ]
def negativeCoefficients : Array ℕ := #[
    546497169356896457457664, 14880801778501190082887680, 177227110854760396780208128, 14880888596924481694334976, 546335935142212036198400, 14880801778501190082887680,
    405195624035211240118681600, 4825791704483355006714511360, 405197988050653890603909120, 14876411464107696324608000, 177227110854760396780208128, 4825791704483355006714511360,
    57474129022273521447501561856, 4825819859392825159059505152, 177174823165744399568076800, 14880888596924481694334976, 405197988050653890603909120, 4825819859392825159059505152,
    405200352079888814947958784, 14876498256916765055385600, 546335935142212036198400, 14876411464107696324608000, 177174823165744399568076800, 14876498256916765055385600,
    546174748496798679040000, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    30, 34, 37, 35, 29, 34,
    38, 40, 39, 33, 37, 40,
    43, 41, 36, 35, 39, 41,
    40, 34, 29, 33, 36, 34,
    28, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15427280102862913, 19194374530357469, 21768449677471103, 20194382947386688, 14426854398695136
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30854560207615003, 34621654633230568, 37195729780354778, 35621663050259789, 29854134503432022, 34621654633230568,
    38388749060714944, 40962824220772882, 39388757477744163, 33621228929062677, 37195729780354778, 40962824220772882,
    43536899354984615, 41962832637803910, 36195304076187001, 35621663050259789, 39388757477744163, 41962832637803910,
    40388765894773381, 34621237346091897, 29854134503432022, 33621228929062677, 36195304076187001, 34621237346091897,
    28853708799249156, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 5110709 / 125000000000
noncomputable def negativeCeiling : ℝ := 40885673 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 546497169356896457457664, coefficient := (-546497169356896457457664) }, { argument := 14880801778501190082887680, coefficient := (-14880801778501190082887680) }, { argument := 177227110854760396780208128, coefficient := (-177227110854760396780208128) }, { argument := 14880888596924481694334976, coefficient := (-14880888596924481694334976) }, { argument := 546335935142212036198400, coefficient := (-546335935142212036198400) }, { argument := 14880801778501190082887680, coefficient := (-14880801778501190082887680) }, { argument := 405195624035211240118681600, coefficient := (-405195624035211240118681600) }, { argument := 4825791704483355006714511360, coefficient := (-4825791704483355006714511360) }, { argument := 405197988050653890603909120, coefficient := (-405197988050653890603909120) }, { argument := 14876411464107696324608000, coefficient := (-14876411464107696324608000) }, { argument := 177227110854760396780208128, coefficient := (-177227110854760396780208128) }, { argument := 4825791704483355006714511360, coefficient := (-4825791704483355006714511360) }, { argument := 57474129022273521447501561856, coefficient := (-57474129022273521447501561856) }, { argument := 4825819859392825159059505152, coefficient := (-4825819859392825159059505152) }, { argument := 177174823165744399568076800, coefficient := (-177174823165744399568076800) }, { argument := 14880888596924481694334976, coefficient := (-14880888596924481694334976) }, { argument := 405197988050653890603909120, coefficient := (-405197988050653890603909120) }, { argument := 4825819859392825159059505152, coefficient := (-4825819859392825159059505152) }, { argument := 405200352079888814947958784, coefficient := (-405200352079888814947958784) }, { argument := 14876498256916765055385600, coefficient := (-14876498256916765055385600) }, { argument := 546335935142212036198400, coefficient := (-546335935142212036198400) }, { argument := 14876411464107696324608000, coefficient := (-14876411464107696324608000) }, { argument := 177174823165744399568076800, coefficient := (-177174823165744399568076800) }, { argument := 14876498256916765055385600, coefficient := (-14876498256916765055385600) }, { argument := 546174748496798679040000, coefficient := (-546174748496798679040000) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 416163268669370354102173696, coefficient := 416163268669370354102173696 }, { argument := 11331885059623658047689195520, coefficient := 11331885059623658047689195520 }, { argument := 134960285040340412819247726592, coefficient := 134960285040340412819247726592 }, { argument := 11331951172754418222722187264, coefficient := 11331951172754418222722187264 }, { argument := 416040487140815743326617600, coefficient := 416040487140815743326617600 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5
