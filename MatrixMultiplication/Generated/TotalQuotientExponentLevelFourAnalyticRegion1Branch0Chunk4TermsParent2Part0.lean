import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4

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
    21, 257, 993, 1919, 9939, 26193,
    26199, 26267, 26299, 28405, 28503, 62961,
    125475
  ]
def positiveCoefficients : Array ℕ := #[
    380215951905954556111417417662464, 203854062149202140628188584214528, 1109194275199700726309615304704, 1267650600228229401496703205376, 1574897414458546502684466644779008, 45001596308102143753132963790848,
    35018847831304837216346426048512, 35177304156333365891533513949184, 45476965283187729778694227492864, 347177808137506327334909590372352, 348524686900248821073999837528064, 358745119864588920623567007121408,
    357398241101846426884476759965696
  ]
def positiveScales : Array ℕ := #[
    4, 8, 9, 10, 13, 14,
    14, 14, 14, 14, 14, 15,
    16
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 55, 107, 113, 165,
    325, 443, 461, 887, 2285, 2295,
    2567, 2573, 4799, 20695697483261
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 1109194275199700726309615304704, 8715097876569077135289834536960, 8477413389026284122509202685952, 35811129456447480592281865551872, 26145293629707231405869503610880,
    25749152817135909717901783859200, 140392303975276406215759879995392, 36524182919075859630623761104896, 140550760300304934890946967896064, 181036351345094011401247926517760, 181828632970236654777183366021120,
    203378693174116554602627320512512, 203854062149202140628188584214528, 380215951905954556111417417662464, 787448707229273251342233322389504
  ]
def negativeScales : Array ℕ := #[
    1, 2, 5, 6, 6, 7,
    8, 8, 8, 9, 11, 11,
    11, 11, 12, 44
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4392317422778759, 8005624549193878, 9955649906820795, 10906138995894173, 13278884988802170, 14676893686935099,
    14677224125562471, 14680963816703623, 14682720322696396, 14793857282493750, 14798826153431421, 15942170834119450,
    16937040420017906
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 5781359713964302, 6741466986587556, 6820178963384638, 7366322214245818,
    8344295907915818, 8791162889093957, 8848622942116486, 9792790294858386, 11157978449945433, 11164278438301171,
    11325867580575419, 11329235741733801, 12228518097716194, 44234396104412937
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 292889906033 / 500000000000
noncomputable def negativeCeiling : ℝ := 624029755493 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-950737950171172051122527404032) }, { argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 21, coefficient := 380215951905954556111417417662464 }, { argument := 55, coefficient := (-8715097876569077135289834536960) }, { argument := 107, coefficient := (-8477413389026284122509202685952) }, { argument := 113, coefficient := (-35811129456447480592281865551872) }, { argument := 165, coefficient := (-26145293629707231405869503610880) }, { argument := 257, coefficient := 203854062149202140628188584214528 }, { argument := 325, coefficient := (-25749152817135909717901783859200) }, { argument := 443, coefficient := (-140392303975276406215759879995392) }, { argument := 461, coefficient := (-36524182919075859630623761104896) }, { argument := 887, coefficient := (-140550760300304934890946967896064) }, { argument := 993, coefficient := 1109194275199700726309615304704 }, { argument := 1919, coefficient := 1267650600228229401496703205376 }, { argument := 2285, coefficient := (-181036351345094011401247926517760) }, { argument := 2295, coefficient := (-181828632970236654777183366021120) }, { argument := 2567, coefficient := (-203378693174116554602627320512512) }, { argument := 2573, coefficient := (-203854062149202140628188584214528) }, { argument := 4799, coefficient := (-380215951905954556111417417662464) }, { argument := 9939, coefficient := 1574897414458546502684466644779008 }, { argument := 26193, coefficient := 45001596308102143753132963790848 }, { argument := 26199, coefficient := 35018847831304837216346426048512 }, { argument := 26267, coefficient := 35177304156333365891533513949184 }, { argument := 26299, coefficient := 45476965283187729778694227492864 }, { argument := 28405, coefficient := 347177808137506327334909590372352 }, { argument := 28503, coefficient := 348524686900248821073999837528064 }, { argument := 62961, coefficient := 358745119864588920623567007121408 }, { argument := 125475, coefficient := 357398241101846426884476759965696 }, { argument := 20695697483261, coefficient := (-787448707229273251342233322389504) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk4
