import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3

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
def constantNumerator : ℤ := (-4233832305608455876422186041344)
def positiveArguments : Array ℕ := #[
    15, 5, 489, 535, 489, 535,
    1, 16777213, 16777219, 17993963, 64671003, 8999165
  ]
def positiveCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 792281625142643375935439503360, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240,
    158456325028528675187087900672, 158456296694329777969216618496, 158456353362727572404959182848, 169948175530393059596745834496, 610800353961524548447739314176, 169989420679254443078042255360
  ]
def positiveScales : Array ℕ := #[
    3, 2, 8, 9, 8, 9,
    0, 23, 24, 24, 25, 23
  ]
def negativeArguments : Array ℕ := #[
    17993963, 64671003, 8999165, 8396995141, 4487903675, 1001,
    4487903675, 17993963, 4487903675, 4487906885, 1001, 4487906885,
    8396998075, 4487906885, 64671003, 8999165, 4487903675, 4487906885,
    5, 1, 1, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    84974087765196529798372917248, 305400176980762274223869657088, 84994710339627221539021127680, 38724305088552412691210174464, 10348401315023195947506073600, 38724311853895801724188229632,
    10348401315023195947506073600, 84974087765196529798372917248, 10348401315023195947506073600, 10348408716779255523463659520, 38724311853895801724188229632, 10348408716779255523463659520,
    38724318619239190757166284800, 10348408716779255523463659520, 305400176980762274223869657088, 84994710339627221539021127680, 10348401315023195947506073600, 10348408716779255523463659520,
    792281625142643375935439503360, 158456325028528675187087900672, 158456325028528675187087900672, 316912650057057350374175801344, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    24, 25, 23, 32, 32, 9,
    32, 24, 32, 32, 9, 32,
    32, 32, 25, 23, 32, 32,
    2, 0, 0, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3906890595303263, 2321928094887362, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509,
    0, 23999999740566425, 24000000257973953, 24101009625720284, 25946615649308979, 23101359714517042
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24101009625720285, 25946615659760637, 23101359714517044, 32967226020692274, 32063394565340465, 9967226272738856,
    32063394565340465, 24101009625720285, 32063394565340465, 32063395597236370, 9967226272738856, 32063395597236370,
    32967226524785395, 32063395597236370, 25946615659760637, 23101359714517044, 32063394565340465, 32063395597236370,
    2321928094887363, 0, 0, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 474091851 / 1000000000000
noncomputable def negativeCeiling : ℝ := 39959761 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 84974087765196529798372917248, coefficient := (-84974087765196529798372917248) }, { argument := 305400176980762274223869657088, coefficient := (-305400176980762274223869657088) }, { argument := 84994710339627221539021127680, coefficient := (-84994710339627221539021127680) }, { argument := 38724305088552412691210174464, coefficient := (-38724305088552412691210174464) }, { argument := 10348401315023195947506073600, coefficient := (-10348401315023195947506073600) }, { argument := 38724311853895801724188229632, coefficient := (-38724311853895801724188229632) }, { argument := 10348401315023195947506073600, coefficient := (-10348401315023195947506073600) }, { argument := 84974087765196529798372917248, coefficient := (-84974087765196529798372917248) }, { argument := 10348401315023195947506073600, coefficient := (-10348401315023195947506073600) }, { argument := 10348408716779255523463659520, coefficient := (-10348408716779255523463659520) }, { argument := 38724311853895801724188229632, coefficient := (-38724311853895801724188229632) }, { argument := 10348408716779255523463659520, coefficient := (-10348408716779255523463659520) }, { argument := 38724318619239190757166284800, coefficient := (-38724318619239190757166284800) }, { argument := 10348408716779255523463659520, coefficient := (-10348408716779255523463659520) }, { argument := 305400176980762274223869657088, coefficient := (-305400176980762274223869657088) }, { argument := 84994710339627221539021127680, coefficient := (-84994710339627221539021127680) }, { argument := 10348401315023195947506073600, coefficient := (-10348401315023195947506073600) }, { argument := 10348408716779255523463659520, coefficient := (-10348408716779255523463659520) }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456296694329777969216618496, coefficient := 158456296694329777969216618496 }, { argument := 158456353362727572404959182848, coefficient := 158456353362727572404959182848 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 169948175530393059596745834496, coefficient := 169948175530393059596745834496 }, { argument := 610800353961524548447739314176, coefficient := 610800353961524548447739314176 }, { argument := 169989420679254443078042255360, coefficient := 169989420679254443078042255360 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3
