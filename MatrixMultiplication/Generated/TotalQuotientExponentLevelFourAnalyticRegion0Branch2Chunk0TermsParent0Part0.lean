import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 0, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    1, 48085, 1100569, 14479933, 1100543, 24043
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 454149984657573780201144320, 10394580315370725126384386048, 136759100546796220856177524736, 10394334752313615904833273856, 454159429390539519491571712
  ]
def positiveScales : Array ℕ := #[
    0, 15, 20, 23, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    2312167225, 52920860365, 696267578305, 52919610155, 1156107655, 52920860365,
    1211252123761, 15936165381877, 1211223508967, 26460980467, 696267578305, 15936165381877,
    209668459684489, 15935788903619, 348141029119, 52919610155, 1211223508967, 15935788903619,
    1211194894849, 26460355349, 1156107655, 26460980467, 348141029119, 26460355349,
    578065849, 1
  ]
def negativeCoefficients : Array ℕ := #[
    650817215808017111449600, 14895897938746253183549440, 195981900387784727807918080, 14895546035915619754311680, 650830750532272243343360, 14895897938746253183549440,
    340937163326360093999497216, 4485631779720990955575181312, 340929108977885363780452352, 14896207721379896653512704, 195981900387784727807918080, 4485631779720990955575181312,
    59016424806650657732804214784, 4485525810512088337234264064, 195985976126588674667184128, 14895546035915619754311680, 340929108977885363780452352, 4485525810512088337234264064,
    340921054819687717817810944, 14895855811230913829797888, 650830750532272243343360, 14896207721379896653512704, 195985976126588674667184128, 14895855811230913829797888,
    650844285538002351947776, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    31, 35, 39, 35, 30, 35,
    40, 43, 40, 34, 39, 43,
    47, 43, 38, 35, 40, 43,
    40, 34, 30, 34, 38, 34,
    29, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15553299298480189, 20069818166927335, 23787551591132640, 20069784084090055, 14553329301184558
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31106598596960563, 35623117465418205, 39340850889643920, 35623083382580916, 30106628599664932, 35623117465418205,
    40139636333854671, 43857369760083413, 40139602251017392, 34623147468122582, 39340850889643920, 43857369760083413,
    47575103182330072, 43857335677244850, 38340880892348289, 35623083382580916, 40139602251017392, 43857335677244850,
    40139568168180113, 34623113385285293, 30106628599664932, 34623147468122582, 38340880892348289, 34623113385285293,
    29106658602369301, 0
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
noncomputable def positiveFloor : ℝ := 22172669 / 500000000000
noncomputable def negativeCeiling : ℝ := 44345339 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 650817215808017111449600, coefficient := (-650817215808017111449600) }, { argument := 14895897938746253183549440, coefficient := (-14895897938746253183549440) }, { argument := 195981900387784727807918080, coefficient := (-195981900387784727807918080) }, { argument := 14895546035915619754311680, coefficient := (-14895546035915619754311680) }, { argument := 650830750532272243343360, coefficient := (-650830750532272243343360) }, { argument := 14895897938746253183549440, coefficient := (-14895897938746253183549440) }, { argument := 340937163326360093999497216, coefficient := (-340937163326360093999497216) }, { argument := 4485631779720990955575181312, coefficient := (-4485631779720990955575181312) }, { argument := 340929108977885363780452352, coefficient := (-340929108977885363780452352) }, { argument := 14896207721379896653512704, coefficient := (-14896207721379896653512704) }, { argument := 195981900387784727807918080, coefficient := (-195981900387784727807918080) }, { argument := 4485631779720990955575181312, coefficient := (-4485631779720990955575181312) }, { argument := 59016424806650657732804214784, coefficient := (-59016424806650657732804214784) }, { argument := 4485525810512088337234264064, coefficient := (-4485525810512088337234264064) }, { argument := 195985976126588674667184128, coefficient := (-195985976126588674667184128) }, { argument := 14895546035915619754311680, coefficient := (-14895546035915619754311680) }, { argument := 340929108977885363780452352, coefficient := (-340929108977885363780452352) }, { argument := 4485525810512088337234264064, coefficient := (-4485525810512088337234264064) }, { argument := 340921054819687717817810944, coefficient := (-340921054819687717817810944) }, { argument := 14895855811230913829797888, coefficient := (-14895855811230913829797888) }, { argument := 650830750532272243343360, coefficient := (-650830750532272243343360) }, { argument := 14896207721379896653512704, coefficient := (-14896207721379896653512704) }, { argument := 195985976126588674667184128, coefficient := (-195985976126588674667184128) }, { argument := 14895855811230913829797888, coefficient := (-14895855811230913829797888) }, { argument := 650844285538002351947776, coefficient := (-650844285538002351947776) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 454149984657573780201144320, coefficient := 454149984657573780201144320 }, { argument := 10394580315370725126384386048, coefficient := 10394580315370725126384386048 }, { argument := 136759100546796220856177524736, coefficient := 136759100546796220856177524736 }, { argument := 10394334752313615904833273856, coefficient := 10394334752313615904833273856 }, { argument := 454159429390539519491571712, coefficient := 454159429390539519491571712 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0
