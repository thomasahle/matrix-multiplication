import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 6, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6

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
    1, 6015, 1318507, 14043967, 1322055, 44567
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 454480550311374655366103040, 12452946528458014603549343744, 132641518094654725365709144064, 12486456441020457605985730560, 420923414084102956477579264
  ]
def positiveScales : Array ℕ := #[
    0, 12, 20, 23, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    36180225, 7930819605, 84474461505, 7952160825, 268070505, 7930819605,
    1738460709049, 18517068797269, 1743138771885, 58761901469, 84474461505, 18517068797269,
    197233009097089, 18566896792185, 625897477289, 7952160825, 1743138771885, 18566896792185,
    1747829423025, 58920025185, 268070505, 58761901469, 625897477289, 58920025185,
    1986217489, 1
  ]
def negativeCoefficients : Array ℕ := #[
    651764991312722814566400, 17858618108910312137687040, 190219576678120654362378240, 17906674264130128026009600, 603641113213510342410240, 17858618108910312137687040,
    489333187591957791473926144, 5212091508460906683735998464, 490649945219771876832706560, 16540004847460637594353664, 190219576678120654362378240, 5212091508460906683735998464,
    55516156642175729257764880384, 5226116842169426469307023360, 176174477843179617684291584, 17906674264130128026009600, 490649945219771876832706560, 5226116842169426469307023360,
    491970246140161188849254400, 16584512716739139977871360, 603641113213510342410240, 16540004847460637594353664, 176174477843179617684291584, 16584512716739139977871360,
    559070521458572639862784, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    25, 32, 36, 32, 27, 32,
    40, 44, 40, 35, 36, 44,
    47, 44, 39, 32, 40, 44,
    40, 35, 27, 35, 39, 35,
    30, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 12554349022063343, 20330473799865652, 23743447175542703, 20334350766273187, 15443688229645390
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25108698044126878, 32884822825247758, 36297796197618224, 32888699791898237, 27998037274654975, 32884822825247758,
    40660947599759387, 44073920975420437, 40664824566169771, 35774162029888966, 36297796197618224, 44073920975420437,
    47486894351109743, 44077797941827973, 39187135405200178, 32888699791898237, 40664824566169771, 44077797941827973,
    40668701532580424, 35778038996328663, 27998037274654975, 35774162029888966, 39187135405200178, 35778038996328663,
    30887376462767668, 0
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
noncomputable def positiveFloor : ℝ := 8831957 / 200000000000
noncomputable def negativeCeiling : ℝ := 22079893 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 651764991312722814566400, coefficient := (-651764991312722814566400) }, { argument := 17858618108910312137687040, coefficient := (-17858618108910312137687040) }, { argument := 190219576678120654362378240, coefficient := (-190219576678120654362378240) }, { argument := 17906674264130128026009600, coefficient := (-17906674264130128026009600) }, { argument := 603641113213510342410240, coefficient := (-603641113213510342410240) }, { argument := 17858618108910312137687040, coefficient := (-17858618108910312137687040) }, { argument := 489333187591957791473926144, coefficient := (-489333187591957791473926144) }, { argument := 5212091508460906683735998464, coefficient := (-5212091508460906683735998464) }, { argument := 490649945219771876832706560, coefficient := (-490649945219771876832706560) }, { argument := 16540004847460637594353664, coefficient := (-16540004847460637594353664) }, { argument := 190219576678120654362378240, coefficient := (-190219576678120654362378240) }, { argument := 5212091508460906683735998464, coefficient := (-5212091508460906683735998464) }, { argument := 55516156642175729257764880384, coefficient := (-55516156642175729257764880384) }, { argument := 5226116842169426469307023360, coefficient := (-5226116842169426469307023360) }, { argument := 176174477843179617684291584, coefficient := (-176174477843179617684291584) }, { argument := 17906674264130128026009600, coefficient := (-17906674264130128026009600) }, { argument := 490649945219771876832706560, coefficient := (-490649945219771876832706560) }, { argument := 5226116842169426469307023360, coefficient := (-5226116842169426469307023360) }, { argument := 491970246140161188849254400, coefficient := (-491970246140161188849254400) }, { argument := 16584512716739139977871360, coefficient := (-16584512716739139977871360) }, { argument := 603641113213510342410240, coefficient := (-603641113213510342410240) }, { argument := 16540004847460637594353664, coefficient := (-16540004847460637594353664) }, { argument := 176174477843179617684291584, coefficient := (-176174477843179617684291584) }, { argument := 16584512716739139977871360, coefficient := (-16584512716739139977871360) }, { argument := 559070521458572639862784, coefficient := (-559070521458572639862784) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 454480550311374655366103040, coefficient := 454480550311374655366103040 }, { argument := 12452946528458014603549343744, coefficient := 12452946528458014603549343744 }, { argument := 132641518094654725365709144064, coefficient := 132641518094654725365709144064 }, { argument := 12486456441020457605985730560, coefficient := 12486456441020457605985730560 }, { argument := 420923414084102956477579264, coefficient := 420923414084102956477579264 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6
