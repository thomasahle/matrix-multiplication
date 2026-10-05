import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1

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
def constantNumerator : ℤ := 350824249932719982589142630400
def positiveArguments : Array ℕ := #[
    1, 8388571, 8388645, 197773, 20905589, 6320107,
    58071, 2039083, 8155897, 232703
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 79227813059144605239798136832, 79228511969384069947289763840, 59773221530661013942291136512, 197447705596496686826691493888, 59691722929899649605193170944,
    2193860352213785337636323328, 77034377719914278170231046144, 77030269261074181578895130624, 2197817695326430100325400576
  ]
def positiveScales : Array ℕ := #[
    0, 22, 23, 17, 24, 22,
    15, 20, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    487132706541, 17104992520393, 68416321053187, 1952045637413, 2502770796535, 33080677163851,
    9997525089497, 487132706541, 487137003795, 487137003795, 17105143412535, 68416924589565,
    1952062857435, 33080677163851, 54626360173287, 33035393619687, 17104992520393, 17105143412535,
    9997525089497, 33035393619687, 155999709873, 68416321053187, 68416924589565, 1952045637413,
    1952062857435, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    548462668914507194862403584, 19258509485254259000561631232, 19257482375074574602885660672, 549452000328961821589372928, 5635738813334392730739015680, 18622765668535380006259392512,
    5628106283460734234147160064, 548462668914507194862403584, 548467507192385473955758080, 548467507192385473955758080, 19258679374702880084553891840, 19257652255462516186561904640,
    549456847334253228573327360, 18622765668535380006259392512, 61503813830255459125677785088, 18597273299457504281408569344, 19258509485254259000561631232, 19258679374702880084553891840,
    5628106283460734234147160064, 18597273299457504281408569344, 5620481882031586287040856064, 19257482375074574602885660672, 19257652255462516186561904640, 549452000328961821589372928,
    549456847334253228573327360, 158456325028528675187087900672, 316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    38, 43, 45, 40, 41, 44,
    43, 38, 38, 38, 43, 45,
    40, 44, 45, 44, 43, 43,
    43, 44, 37, 45, 45, 40,
    40, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 22999993635168450, 23000006363344048, 17593485957030499, 24317385355065887, 22591517552894412,
    15825530257377616, 20959489069403038, 22959412124390183, 17828130284410333
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38825523895149759, 43959482719008831, 45959405773979311, 40828123922242518, 41186663313876255, 44911054005736676,
    43184708135233639, 38825523895149759, 38825536621866193, 38825536621866193, 43959495445727593, 45959418500698070,
    40828136648958966, 44911054005736676, 45634662531107468, 44909077773329436, 43959482719008831, 43959495445727593,
    43184708135233639, 44909077773329436, 37182752389738424, 45959405773979311, 45959418500698070, 40828123922242518,
    40828136648958966, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 172167619 / 1000000000000
noncomputable def negativeCeiling : ℝ := 170668467 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 548462668914507194862403584, coefficient := (-548462668914507194862403584) }, { argument := 19258509485254259000561631232, coefficient := (-19258509485254259000561631232) }, { argument := 19257482375074574602885660672, coefficient := (-19257482375074574602885660672) }, { argument := 549452000328961821589372928, coefficient := (-549452000328961821589372928) }, { argument := 5635738813334392730739015680, coefficient := (-5635738813334392730739015680) }, { argument := 18622765668535380006259392512, coefficient := (-18622765668535380006259392512) }, { argument := 5628106283460734234147160064, coefficient := (-5628106283460734234147160064) }, { argument := 548462668914507194862403584, coefficient := (-548462668914507194862403584) }, { argument := 548467507192385473955758080, coefficient := (-548467507192385473955758080) }, { argument := 548467507192385473955758080, coefficient := (-548467507192385473955758080) }, { argument := 19258679374702880084553891840, coefficient := (-19258679374702880084553891840) }, { argument := 19257652255462516186561904640, coefficient := (-19257652255462516186561904640) }, { argument := 549456847334253228573327360, coefficient := (-549456847334253228573327360) }, { argument := 18622765668535380006259392512, coefficient := (-18622765668535380006259392512) }, { argument := 61503813830255459125677785088, coefficient := (-61503813830255459125677785088) }, { argument := 18597273299457504281408569344, coefficient := (-18597273299457504281408569344) }, { argument := 19258509485254259000561631232, coefficient := (-19258509485254259000561631232) }, { argument := 19258679374702880084553891840, coefficient := (-19258679374702880084553891840) }, { argument := 5628106283460734234147160064, coefficient := (-5628106283460734234147160064) }, { argument := 18597273299457504281408569344, coefficient := (-18597273299457504281408569344) }, { argument := 5620481882031586287040856064, coefficient := (-5620481882031586287040856064) }, { argument := 19257482375074574602885660672, coefficient := (-19257482375074574602885660672) }, { argument := 19257652255462516186561904640, coefficient := (-19257652255462516186561904640) }, { argument := 549452000328961821589372928, coefficient := (-549452000328961821589372928) }, { argument := 549456847334253228573327360, coefficient := (-549456847334253228573327360) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 79227813059144605239798136832, coefficient := 79227813059144605239798136832 }, { argument := 79228511969384069947289763840, coefficient := 79228511969384069947289763840 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 59773221530661013942291136512, coefficient := 59773221530661013942291136512 }, { argument := 197447705596496686826691493888, coefficient := 197447705596496686826691493888 }, { argument := 59691722929899649605193170944, coefficient := 59691722929899649605193170944 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 2193860352213785337636323328, coefficient := 2193860352213785337636323328 }, { argument := 77034377719914278170231046144, coefficient := 77034377719914278170231046144 }, { argument := 77030269261074181578895130624, coefficient := 77030269261074181578895130624 }, { argument := 2197817695326430100325400576, coefficient := 2197817695326430100325400576 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1
