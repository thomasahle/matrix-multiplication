import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 18, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    129, 269, 891, 1715, 2151, 4797,
    6091, 14143, 19025, 24343, 45911, 111337
  ]
def positiveCoefficients : Array ℕ := #[
    68373904249810123343228429139968, 554597137599850363154807652352, 79228162514264337593543950336, 271752597423926677945855749652480, 554597137599850363154807652352, 24877643029479002004372800405504,
    4753689750855860255612637020160, 63778670823982791762802880020480, 24164589566850622966030904852480, 4674461588341595918019093069824, 85724871840434013276214554263552, 62590248386268826698899720765440
  ]
def positiveScales : Array ℕ := #[
    7, 8, 9, 10, 11, 12,
    12, 13, 14, 14, 15, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 13, 27, 131, 157,
    251, 305, 539, 541, 543, 502429911281
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 1663791412799551089464422957056, 4119864450741745554864285417472, 4278320775770274230051373318144, 20757778578737256449508514988032, 24877643029479002004372800405504,
    19886268791080348735979531534336, 24164589566850622966030904852480, 42703979595188477962920189231104, 85724871840434013276214554263552, 43020892245245535313294365032448, 135876298711963338972927874826240
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 7, 7,
    7, 8, 9, 9, 9, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 8071462362556624, 9799281621482476, 10743992861047947, 11070791809423060, 12227916724201487,
    12572463389083514, 13787800555256517, 14215608833278269, 14571219354438152, 15486552235675711, 16764573589522006
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 3700439718214233, 4754887502413606, 7033423001537451, 7294620748891628,
    7971543568880765, 8252665432450249, 9074141462752506, 9079484783826816, 9084808387804362, 38870131401390083
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 12
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
noncomputable def positiveFloor : ℝ := 44791888279 / 500000000000
noncomputable def negativeCeiling : ℝ := 91055994269 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 7, coefficient := (-1663791412799551089464422957056) }, { argument := 13, coefficient := (-4119864450741745554864285417472) }, { argument := 27, coefficient := (-4278320775770274230051373318144) }, { argument := 129, coefficient := 68373904249810123343228429139968 }, { argument := 131, coefficient := (-20757778578737256449508514988032) }, { argument := 157, coefficient := (-24877643029479002004372800405504) }, { argument := 251, coefficient := (-19886268791080348735979531534336) }, { argument := 269, coefficient := 554597137599850363154807652352 }, { argument := 305, coefficient := (-24164589566850622966030904852480) }, { argument := 539, coefficient := (-42703979595188477962920189231104) }, { argument := 541, coefficient := (-85724871840434013276214554263552) }, { argument := 543, coefficient := (-43020892245245535313294365032448) }, { argument := 891, coefficient := 79228162514264337593543950336 }, { argument := 1715, coefficient := 271752597423926677945855749652480 }, { argument := 2151, coefficient := 554597137599850363154807652352 }, { argument := 4797, coefficient := 24877643029479002004372800405504 }, { argument := 6091, coefficient := 4753689750855860255612637020160 }, { argument := 14143, coefficient := 63778670823982791762802880020480 }, { argument := 19025, coefficient := 24164589566850622966030904852480 }, { argument := 24343, coefficient := 4674461588341595918019093069824 }, { argument := 45911, coefficient := 85724871840434013276214554263552 }, { argument := 111337, coefficient := 62590248386268826698899720765440 }, { argument := 502429911281, coefficient := (-135876298711963338972927874826240) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18
