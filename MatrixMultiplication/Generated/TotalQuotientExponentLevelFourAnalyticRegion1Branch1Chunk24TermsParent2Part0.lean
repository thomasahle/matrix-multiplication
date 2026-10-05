import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 24, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24

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
def constantNumerator : ℤ := (-4469582511839865482523288010752)
def positiveArguments : Array ℕ := #[
    15, 61, 67, 61, 67, 5,
    1, 16777215, 16777217, 17955861, 32375785, 17955865
  ]
def positiveCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 37757171198204098384423288832, 41470991316060239209120661504, 37757171198204098384423288832, 41470991316060239209120661504, 792281625142643375935439503360,
    158456325028528675187087900672, 158456315583795709447797473280, 158456334473261640926378328064, 169588312314932461152881344512, 611561287762375265859603005440, 169588350093864324110043054080
  ]
def positiveScales : Array ℕ := #[
    3, 5, 6, 5, 6, 2,
    0, 23, 24, 24, 24, 24
  ]
def negativeArguments : Array ℕ := #[
    17955861, 32375785, 17955865, 1048575939, 562036669, 125,
    562036669, 17955861, 562036669, 562036803, 125, 562036803,
    1048576061, 562036803, 32375785, 17955865, 562036669, 562036803,
    1, 5, 1, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    84794156157466230576440672256, 305780643881187632929801502720, 84794175046932162055021527040, 38685623977165356598032334848, 10367746593083206863740207104, 38685626227668133590597632000,
    10367746593083206863740207104, 84794156157466230576440672256, 10367746593083206863740207104, 10367749064946912740820123648, 38685626227668133590597632000, 10367749064946912740820123648,
    38685628478170910583162929152, 10367749064946912740820123648, 305780643881187632929801502720, 84794175046932162055021527040, 10367746593083206863740207104, 10367749064946912740820123648,
    158456325028528675187087900672, 792281625142643375935439503360, 158456325028528675187087900672, 316912650057057350374175801344, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    24, 24, 24, 29, 29, 6,
    29, 24, 29, 29, 6, 29,
    29, 29, 24, 24, 29, 29,
    0, 2, 0, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3906890595303263, 5930737337099561, 6066089190457772, 5930737337099561, 6066089190457772, 2321928094887362,
    0, 23999999912549092, 24000000085991322, 24097951497422871, 24948411837137216, 24097951818809828
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24097951497422872, 24948411847911657, 24097951818809829, 29965784214309248, 29066089018475112, 6965784298236803,
    29066089018475112, 24097951497422872, 29066089018475112, 29066089362440414, 6965784298236803, 29066089362440414,
    29965784382164353, 29066089362440414, 24948411847911657, 24097951818809829, 29066089018475112, 29066089362440414,
    0, 2321928094887363, 0, 0, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 1852287 / 4000000000
noncomputable def negativeCeiling : ℝ := 19286799 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 84794156157466230576440672256, coefficient := (-84794156157466230576440672256) }, { argument := 305780643881187632929801502720, coefficient := (-305780643881187632929801502720) }, { argument := 84794175046932162055021527040, coefficient := (-84794175046932162055021527040) }, { argument := 38685623977165356598032334848, coefficient := (-38685623977165356598032334848) }, { argument := 10367746593083206863740207104, coefficient := (-10367746593083206863740207104) }, { argument := 38685626227668133590597632000, coefficient := (-38685626227668133590597632000) }, { argument := 10367746593083206863740207104, coefficient := (-10367746593083206863740207104) }, { argument := 84794156157466230576440672256, coefficient := (-84794156157466230576440672256) }, { argument := 10367746593083206863740207104, coefficient := (-10367746593083206863740207104) }, { argument := 10367749064946912740820123648, coefficient := (-10367749064946912740820123648) }, { argument := 38685626227668133590597632000, coefficient := (-38685626227668133590597632000) }, { argument := 10367749064946912740820123648, coefficient := (-10367749064946912740820123648) }, { argument := 38685628478170910583162929152, coefficient := (-38685628478170910583162929152) }, { argument := 10367749064946912740820123648, coefficient := (-10367749064946912740820123648) }, { argument := 305780643881187632929801502720, coefficient := (-305780643881187632929801502720) }, { argument := 84794175046932162055021527040, coefficient := (-84794175046932162055021527040) }, { argument := 10367746593083206863740207104, coefficient := (-10367746593083206863740207104) }, { argument := 10367749064946912740820123648, coefficient := (-10367749064946912740820123648) }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456315583795709447797473280, coefficient := 158456315583795709447797473280 }, { argument := 158456334473261640926378328064, coefficient := 158456334473261640926378328064 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 169588312314932461152881344512, coefficient := 169588312314932461152881344512 }, { argument := 611561287762375265859603005440, coefficient := 611561287762375265859603005440 }, { argument := 169588350093864324110043054080, coefficient := 169588350093864324110043054080 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24
