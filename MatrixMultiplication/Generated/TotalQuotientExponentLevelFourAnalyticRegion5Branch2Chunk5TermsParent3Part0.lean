import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5

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
def constantNumerator : ℤ := 304782363940907887149497450496
def positiveArguments : Array ℕ := #[
    3, 12579369, 12586455, 2257695, 16137077, 4513357
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 237617562164997784168663351296, 237751412920588241392600350720, 85293305572339069205883125760, 304820766225146583104375226368, 85254903288100373251005349888
  ]
def positiveScales : Array ℕ := #[
    1, 23, 23, 21, 23, 22
  ]
def negativeArguments : Array ℕ := #[
    2366700081675, 67664713880651, 18925080894301, 2366700081675, 2368029502965, 2368029502965,
    67702899338165, 18935701742755, 67664713880651, 67702899338165, 18925080894301, 18935701742755,
    3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    21317339211858504897370521600, 76183695054757767987775668224, 21307746815882619199185485824, 21317339211858504897370521600, 21329313574311029705571041280, 21329313574311029705571041280,
    76226688057815523564411944960, 21319704828167567426317189120, 76183695054757767987775668224, 76226688057815523564411944960, 21307746815882619199185485824, 21319704828167567426317189120,
    475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    41, 45, 44, 41, 41, 41,
    45, 44, 45, 45, 44, 44,
    1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 23584556220498268, 23585368666562409, 21106419169824726, 23943875942401615, 22105769467475619
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41106014031837397, 45943468929241723, 44105364700486875, 41106014031837397, 41106824194073044, 41106824194073044,
    45944282860715360, 44106174120933538, 45943468929241723, 45944282860715360, 44105364700486875, 44106174120933538,
    1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 14
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
noncomputable def positiveFloor : ℝ := 138115981 / 500000000000
noncomputable def negativeCeiling : ℝ := 274178601 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21317339211858504897370521600, coefficient := (-21317339211858504897370521600) }, { argument := 76183695054757767987775668224, coefficient := (-76183695054757767987775668224) }, { argument := 21307746815882619199185485824, coefficient := (-21307746815882619199185485824) }, { argument := 21317339211858504897370521600, coefficient := (-21317339211858504897370521600) }, { argument := 21329313574311029705571041280, coefficient := (-21329313574311029705571041280) }, { argument := 21329313574311029705571041280, coefficient := (-21329313574311029705571041280) }, { argument := 76226688057815523564411944960, coefficient := (-76226688057815523564411944960) }, { argument := 21319704828167567426317189120, coefficient := (-21319704828167567426317189120) }, { argument := 76183695054757767987775668224, coefficient := (-76183695054757767987775668224) }, { argument := 76226688057815523564411944960, coefficient := (-76226688057815523564411944960) }, { argument := 21307746815882619199185485824, coefficient := (-21307746815882619199185485824) }, { argument := 21319704828167567426317189120, coefficient := (-21319704828167567426317189120) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 237617562164997784168663351296, coefficient := 237617562164997784168663351296 }, { argument := 237751412920588241392600350720, coefficient := 237751412920588241392600350720 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 85293305572339069205883125760, coefficient := 85293305572339069205883125760 }, { argument := 304820766225146583104375226368, coefficient := 304820766225146583104375226368 }, { argument := 85254903288100373251005349888, coefficient := 85254903288100373251005349888 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5
