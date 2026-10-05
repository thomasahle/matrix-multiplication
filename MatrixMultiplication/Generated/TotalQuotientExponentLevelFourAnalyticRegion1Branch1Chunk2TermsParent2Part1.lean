import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 40529748149091171129300120240128
def positiveArguments : Array ℕ := #[
    5, 47, 35, 37, 3, 643,
    1163, 35, 643, 19, 19, 37,
    37, 1163, 37, 47, 3, 257,
    1025, 509, 1025, 3, 1, 1,
    1, 1, 12477, 511185, 10525695, 511185,
    12477, 42083, 8346525, 8346525, 42083
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 1818224432700402278758088704, 1353996917968384675670917120, 1431368170423720942852112384, 1856910058928070412348686336, 24874857664390609898754277376,
    44991383302778039365865046016, 1353996917968384675670917120, 24874857664390609898754277376, 1470053796651389076442710016, 1470053796651389076442710016, 1431368170423720942852112384,
    1431368170423720942852112384, 44991383302778039365865046016, 1431368170423720942852112384, 1818224432700402278758088704, 1856910058928070412348686336, 39768823762042841331134365696,
    39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 475368975085586025561263702016, 39614081257132168796771975168, 39614081257132168796771975168,
    39614081257132168796771975168, 39614081257132168796771975168, 235683866427058253325139968, 38624046568731513417011036160, 397649514215268882220591349760, 38624046568731513417011036160,
    235683866427058253325139968, 397462697397206559055937536, 78830699816867131034488012800, 78830699816867131034488012800, 397462697397206559055937536
  ]
def positiveScales : Array ℕ := #[
    2, 5, 5, 5, 1, 9,
    10, 5, 9, 4, 4, 5,
    5, 10, 5, 5, 1, 8,
    10, 8, 10, 1, 0, 0,
    0, 0, 13, 18, 23, 18,
    13, 15, 22, 22, 15
  ]
def negativeArguments : Array ℕ := #[
    37, 1163, 37, 240267363, 3, 12477,
    511185, 10525695, 511185, 12477, 1, 1,
    3, 1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    178921021302965117856514048, 5623922912847254920733130752, 178921021302965117856514048, 277009409657879474668044288, 232113757366008801543585792, 117841933213529126662569984,
    19312023284365756708505518080, 198824757107634441110295674880, 19312023284365756708505518080, 117841933213529126662569984, 158456325028528675187087900672, 158456325028528675187087900672,
    475368975085586025561263702016, 158456325028528675187087900672, 475368975085586025561263702016, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    5, 10, 5, 27, 1, 13,
    18, 23, 18, 13, 0, 0,
    1, 0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 5554588851677541, 5129283016944966, 5209453365628949, 1584962500720924, 9328674927327946,
    10183635381473218, 5129283016944966, 9328674927327946, 4247927513443585, 4247927513443585, 5209453365628949,
    5209453365628949, 10183635381473218, 5209453365628949, 5554588851677541, 1584962500720924, 8005624549193878,
    10001408194392808, 8991521844801183, 10001408194392808, 1584962500720924, 0, 0,
    0, 0, 13606983470367085, 18963485976693339, 23327412160206294, 18963485976693339,
    13606983470367085, 15360949934247378, 22992744237616252, 22992744237616252, 15360949934247378
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5209453365628950, 10183635381473219, 5209453365628950, 27840065452127928, 1584962500724866, 13606983470374365,
    18963485990566218, 23327412160206296, 18963485990566218, 13606983470374365, 0, 0,
    1584962500724866, 0, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 35
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
noncomputable def positiveFloor : ℝ := 119805903 / 500000000000
noncomputable def negativeCeiling : ℝ := 20907837 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 5623922912847254920733130752, coefficient := (-5623922912847254920733130752) }, { argument := 178921021302965117856514048, coefficient := (-178921021302965117856514048) }, { argument := 277009409657879474668044288, coefficient := (-277009409657879474668044288) }, { argument := 232113757366008801543585792, coefficient := (-232113757366008801543585792) }, { argument := 117841933213529126662569984, coefficient := (-117841933213529126662569984) }, { argument := 19312023284365756708505518080, coefficient := (-19312023284365756708505518080) }, { argument := 198824757107634441110295674880, coefficient := (-198824757107634441110295674880) }, { argument := 19312023284365756708505518080, coefficient := (-19312023284365756708505518080) }, { argument := 117841933213529126662569984, coefficient := (-117841933213529126662569984) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 24874857664390609898754277376, coefficient := 24874857664390609898754277376 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 44991383302778039365865046016, coefficient := 44991383302778039365865046016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 235683866427058253325139968, coefficient := 235683866427058253325139968 }, { argument := 38624046568731513417011036160, coefficient := 38624046568731513417011036160 }, { argument := 397649514215268882220591349760, coefficient := 397649514215268882220591349760 }, { argument := 38624046568731513417011036160, coefficient := 38624046568731513417011036160 }, { argument := 235683866427058253325139968, coefficient := 235683866427058253325139968 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 397462697397206559055937536, coefficient := 397462697397206559055937536 }, { argument := 78830699816867131034488012800, coefficient := 78830699816867131034488012800 }, { argument := 78830699816867131034488012800, coefficient := 78830699816867131034488012800 }, { argument := 397462697397206559055937536, coefficient := 397462697397206559055937536 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
