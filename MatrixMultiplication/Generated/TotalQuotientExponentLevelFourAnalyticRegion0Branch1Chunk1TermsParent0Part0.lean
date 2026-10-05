import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1

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
def constantNumerator : ℤ := 1270330008744691090586540703744
def positiveArguments : Array ℕ := #[
    3, 148553, 7828307, 2377757, 172353, 24472587,
    12238167, 693315
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 89794778640606003895063281664, 295745076755310589711143141376, 89829119689669431955057278976, 6511312243376255692129173504, 231137049195822804302617903104,
    231172438610245429423849340928, 6548175036141536142667284480
  ]
def positiveScales : Array ℕ := #[
    1, 17, 22, 21, 17, 24,
    23, 19
  ]
def negativeArguments : Array ℕ := #[
    546354048989, 38778259286805, 38784059418033, 8584045215, 546354048989, 1798683929153,
    273282765553, 1798683929153, 127719592875531, 127739424910317, 1809004631235, 38778259286805,
    127719592875531, 1212283966455, 273282765553, 1212283966455, 19399443437361, 549590352765,
    38784059418033, 127739424910317, 19399443437361, 8584045215, 1809004631235, 549590352765,
    3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    615139972859805529209307136, 21830219259266434246807388160, 21833484442871074343979319296, 618545645305687827535626240, 615139972859805529209307136, 2025138068272687606736617472,
    615378080555634710118662144, 2025138068272687606736617472, 71899738860269108413618716672, 71910903303328136952916475904, 2036758145785361882299760640, 21830219259266434246807388160,
    71899738860269108413618716672, 21838566478375859490882846720, 615378080555634710118662144, 21838566478375859490882846720, 21841831558923503415028875264, 618783726979718361498255360,
    21833484442871074343979319296, 71910903303328136952916475904, 21841831558923503415028875264, 618545645305687827535626240, 2036758145785361882299760640, 618783726979718361498255360,
    475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    38, 45, 45, 32, 38, 40,
    37, 40, 46, 46, 40, 45,
    46, 40, 37, 40, 44, 38,
    45, 46, 44, 32, 40, 38,
    1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 17180618214860357, 22900268903797994, 21181169852612871, 17395006885108659, 24544663281149627,
    23544884155408684, 19403151448278835
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38991045215390469, 45140313277448226, 45140529047701474, 32999010552557366, 38991045215390469, 40710078832330123,
    37991603544314231, 40710078832330123, 46859973189747074, 46860197191073570, 40718333240168359, 45140313277448226,
    46859973189747074, 40140864815191153, 37991603544314231, 40140864815191153, 44141080496170934, 38999565747302896,
    45140529047701474, 46860197191073570, 44141080496170934, 32999010552557366, 40718333240168359, 38999565747302896,
    1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 13438133 / 50000000000
noncomputable def negativeCeiling : ℝ := 278331657 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 615139972859805529209307136, coefficient := (-615139972859805529209307136) }, { argument := 21830219259266434246807388160, coefficient := (-21830219259266434246807388160) }, { argument := 21833484442871074343979319296, coefficient := (-21833484442871074343979319296) }, { argument := 618545645305687827535626240, coefficient := (-618545645305687827535626240) }, { argument := 615139972859805529209307136, coefficient := (-615139972859805529209307136) }, { argument := 2025138068272687606736617472, coefficient := (-2025138068272687606736617472) }, { argument := 615378080555634710118662144, coefficient := (-615378080555634710118662144) }, { argument := 2025138068272687606736617472, coefficient := (-2025138068272687606736617472) }, { argument := 71899738860269108413618716672, coefficient := (-71899738860269108413618716672) }, { argument := 71910903303328136952916475904, coefficient := (-71910903303328136952916475904) }, { argument := 2036758145785361882299760640, coefficient := (-2036758145785361882299760640) }, { argument := 21830219259266434246807388160, coefficient := (-21830219259266434246807388160) }, { argument := 71899738860269108413618716672, coefficient := (-71899738860269108413618716672) }, { argument := 21838566478375859490882846720, coefficient := (-21838566478375859490882846720) }, { argument := 615378080555634710118662144, coefficient := (-615378080555634710118662144) }, { argument := 21838566478375859490882846720, coefficient := (-21838566478375859490882846720) }, { argument := 21841831558923503415028875264, coefficient := (-21841831558923503415028875264) }, { argument := 618783726979718361498255360, coefficient := (-618783726979718361498255360) }, { argument := 21833484442871074343979319296, coefficient := (-21833484442871074343979319296) }, { argument := 71910903303328136952916475904, coefficient := (-71910903303328136952916475904) }, { argument := 21841831558923503415028875264, coefficient := (-21841831558923503415028875264) }, { argument := 618545645305687827535626240, coefficient := (-618545645305687827535626240) }, { argument := 2036758145785361882299760640, coefficient := (-2036758145785361882299760640) }, { argument := 618783726979718361498255360, coefficient := (-618783726979718361498255360) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 89794778640606003895063281664, coefficient := 89794778640606003895063281664 }, { argument := 295745076755310589711143141376, coefficient := 295745076755310589711143141376 }, { argument := 89829119689669431955057278976, coefficient := 89829119689669431955057278976 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 6511312243376255692129173504, coefficient := 6511312243376255692129173504 }, { argument := 231137049195822804302617903104, coefficient := 231137049195822804302617903104 }, { argument := 231172438610245429423849340928, coefficient := 231172438610245429423849340928 }, { argument := 6548175036141536142667284480, coefficient := 6548175036141536142667284480 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1
