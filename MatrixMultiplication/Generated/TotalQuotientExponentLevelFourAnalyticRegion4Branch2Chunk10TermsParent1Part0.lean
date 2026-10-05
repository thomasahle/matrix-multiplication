import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10

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
def constantNumerator : ℤ := (-601380436780463905839402450944)
def positiveArguments : Array ℕ := #[
    13, 12582943, 12582881, 21058709, 37663271, 21055261,
    585109, 24580747, 24580721, 585071
  ]
def positiveCoefficients : Array ℕ := #[
    1029966112685436388716071354368, 237685073116236888616638349312, 237683901969349136944625352704, 198893883108210686976933756928, 711439074422545221429141438464, 198861317668944817903540109312,
    5526198260850750482680905728, 232158591513397165955244621824, 232158345950340056733693509632, 5525839360998052389644664832
  ]
def positiveScales : Array ℕ := #[
    3, 23, 23, 24, 25, 24,
    19, 24, 24, 19
  ]
def negativeArguments : Array ℕ := #[
    1227065777019, 103099378977239, 12887408740649, 2453972170219, 63358054322975, 113300436601913,
    63347582047343, 1227065777019, 1227059242117, 1227059242117, 103098871952937, 12887345362647,
    2453959100949, 113300436601913, 405302412513837, 56640991858893, 103099378977239, 103098871952937,
    63347582047343, 56640991858893, 63337112250461, 12887408740649, 12887345362647, 2453972170219,
    2453959100949, 3, 7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1381553244035464133508857856, 58039790593002888675425517568, 58039729202158109526698491904, 1381463518921981972686307328, 17833706864991865826548121600, 63782475507661236605714169856,
    17830759181452241056204587008, 1381553244035464133508857856, 1381545886389911107831595008, 1381545886389911107831595008, 58039505163695694302196793344, 58039443773011918840148262912,
    1381456161577044222136025088, 63782475507661236605714169856, 228164974246209921020690694144, 63772087457401453088165855232, 58039790593002888675425517568, 58039505163695694302196793344,
    17830759181452241056204587008, 63772087457401453088165855232, 17827812195618714807399612416, 58039729202158109526698491904, 58039443773011918840148262912, 1381463518921981972686307328,
    1381456161577044222136025088, 475368975085586025561263702016, 1109194275199700726309615304704, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    40, 46, 43, 41, 45, 46,
    45, 40, 40, 40, 46, 43,
    41, 46, 48, 45, 46, 46,
    45, 45, 45, 43, 43, 41,
    41, 1, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3700439718136550, 23584966055024664, 23584958946408428, 24327913659151267, 25166654965559091, 24327677423407541,
    19158345883938221, 24551025423568079, 24551023897573328, 19158252184829412
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40158349725575499, 46551028971031961, 43551027445038961, 41158256026559232, 45848593267266707, 46687146749054093,
    45848354788520624, 40158349725575499, 40158342042290715, 40158342042290715, 46551021876098392, 43551020350101890,
    41158248343089364, 46687146749054093, 48525992091302636, 45686911762734541, 46551028971031961, 46551021876098392,
    45848354788520624, 45686911762734541, 45848116326808373, 43551027445038961, 43551020350101890, 41158256026559232,
    41158248343089364, 1584962500724866, 2807354922807594, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 652590897 / 1000000000000
noncomputable def negativeCeiling : ℝ := 627285203 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1381553244035464133508857856, coefficient := (-1381553244035464133508857856) }, { argument := 58039790593002888675425517568, coefficient := (-58039790593002888675425517568) }, { argument := 58039729202158109526698491904, coefficient := (-58039729202158109526698491904) }, { argument := 1381463518921981972686307328, coefficient := (-1381463518921981972686307328) }, { argument := 17833706864991865826548121600, coefficient := (-17833706864991865826548121600) }, { argument := 63782475507661236605714169856, coefficient := (-63782475507661236605714169856) }, { argument := 17830759181452241056204587008, coefficient := (-17830759181452241056204587008) }, { argument := 1381553244035464133508857856, coefficient := (-1381553244035464133508857856) }, { argument := 1381545886389911107831595008, coefficient := (-1381545886389911107831595008) }, { argument := 1381545886389911107831595008, coefficient := (-1381545886389911107831595008) }, { argument := 58039505163695694302196793344, coefficient := (-58039505163695694302196793344) }, { argument := 58039443773011918840148262912, coefficient := (-58039443773011918840148262912) }, { argument := 1381456161577044222136025088, coefficient := (-1381456161577044222136025088) }, { argument := 63782475507661236605714169856, coefficient := (-63782475507661236605714169856) }, { argument := 228164974246209921020690694144, coefficient := (-228164974246209921020690694144) }, { argument := 63772087457401453088165855232, coefficient := (-63772087457401453088165855232) }, { argument := 58039790593002888675425517568, coefficient := (-58039790593002888675425517568) }, { argument := 58039505163695694302196793344, coefficient := (-58039505163695694302196793344) }, { argument := 17830759181452241056204587008, coefficient := (-17830759181452241056204587008) }, { argument := 63772087457401453088165855232, coefficient := (-63772087457401453088165855232) }, { argument := 17827812195618714807399612416, coefficient := (-17827812195618714807399612416) }, { argument := 58039729202158109526698491904, coefficient := (-58039729202158109526698491904) }, { argument := 58039443773011918840148262912, coefficient := (-58039443773011918840148262912) }, { argument := 1381463518921981972686307328, coefficient := (-1381463518921981972686307328) }, { argument := 1381456161577044222136025088, coefficient := (-1381456161577044222136025088) }, { argument := 1029966112685436388716071354368, coefficient := 1029966112685436388716071354368 }, { argument := 237685073116236888616638349312, coefficient := 237685073116236888616638349312 }, { argument := 237683901969349136944625352704, coefficient := 237683901969349136944625352704 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 198893883108210686976933756928, coefficient := 198893883108210686976933756928 }, { argument := 711439074422545221429141438464, coefficient := 711439074422545221429141438464 }, { argument := 198861317668944817903540109312, coefficient := 198861317668944817903540109312 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 5526198260850750482680905728, coefficient := 5526198260850750482680905728 }, { argument := 232158591513397165955244621824, coefficient := 232158591513397165955244621824 }, { argument := 232158345950340056733693509632, coefficient := 232158345950340056733693509632 }, { argument := 5525839360998052389644664832, coefficient := 5525839360998052389644664832 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10
