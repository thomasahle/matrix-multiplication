import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 2873935, 11029279, 1437001, 89091, 8210441,
    2052607, 178165
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 27143548635891947634446827520, 104168594959636075385735610368, 27144181433000652166905462784, 1682881409301358246933561344, 77545422775957465435966799872,
    77545299994428910825191243776, 1682720848840940678996295680
  ]
def positiveScales : Array ℕ := #[
    0, 21, 23, 20, 16, 22,
    20, 17
  ]
def negativeArguments : Array ℕ := #[
    256041743085, 23596273755335, 5899059098545, 512034629275, 256041743085, 982609495389,
    128023856091, 982609495389, 90555244502039, 22638775280353, 1965031493035, 23596273755335,
    90555244502039, 11798411927441, 128023856091, 11798411927441, 2949598311607, 256023283165,
    5899059098545, 22638775280353, 2949598311607, 512034629275, 1965031493035, 256023283165,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    144138687343612283867627520, 6641760605741182518831349760, 6641750089510949010622382080, 144124935350230003902054400, 144138687343612283867627520, 553159969660576438438330368,
    144142047646490401160822784, 553159969660576438438330368, 25489035337239187312905027584, 25488994979180541728650166272, 553107193737732212874280960, 6641760605741182518831349760,
    25489035337239187312905027584, 6641915444998362886247022592, 144142047646490401160822784, 6641915444998362886247022592, 6641904928522964673323073536, 144128295332508122721812480,
    6641750089510949010622382080, 25488994979180541728650166272, 6641904928522964673323073536, 144124935350230003902054400, 553107193737732212874280960, 144128295332508122721812480,
    158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    37, 44, 42, 38, 37, 39,
    36, 39, 46, 44, 40, 44,
    46, 43, 36, 43, 41, 37,
    42, 44, 41, 38, 40, 37,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 21454596001948191, 23394835147151449, 20454629635082216, 16442992077164403, 22969028282700040,
    20969025998407381, 17442854425854227
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37897588083295113, 44423624285532001, 42423622001239308, 38897450431974596, 37897588083295113, 39837827225686337,
    36897621716431668, 39837827225686337, 46363863430735240, 44363861146442547, 40837689574372508, 44423624285532001,
    46363863430735240, 43423657918666026, 36897621716431668, 43423657918666026, 41423655634373333, 37897484065111145,
    42423622001239308, 44363861146442547, 41423655634373333, 38897450431974596, 40837689574372508, 37897484065111145,
    0, 0
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
noncomputable def positiveFloor : ℝ := 1059081 / 12500000000
noncomputable def negativeCeiling : ℝ := 84726481 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 144138687343612283867627520, coefficient := (-144138687343612283867627520) }, { argument := 6641760605741182518831349760, coefficient := (-6641760605741182518831349760) }, { argument := 6641750089510949010622382080, coefficient := (-6641750089510949010622382080) }, { argument := 144124935350230003902054400, coefficient := (-144124935350230003902054400) }, { argument := 144138687343612283867627520, coefficient := (-144138687343612283867627520) }, { argument := 553159969660576438438330368, coefficient := (-553159969660576438438330368) }, { argument := 144142047646490401160822784, coefficient := (-144142047646490401160822784) }, { argument := 553159969660576438438330368, coefficient := (-553159969660576438438330368) }, { argument := 25489035337239187312905027584, coefficient := (-25489035337239187312905027584) }, { argument := 25488994979180541728650166272, coefficient := (-25488994979180541728650166272) }, { argument := 553107193737732212874280960, coefficient := (-553107193737732212874280960) }, { argument := 6641760605741182518831349760, coefficient := (-6641760605741182518831349760) }, { argument := 25489035337239187312905027584, coefficient := (-25489035337239187312905027584) }, { argument := 6641915444998362886247022592, coefficient := (-6641915444998362886247022592) }, { argument := 144142047646490401160822784, coefficient := (-144142047646490401160822784) }, { argument := 6641915444998362886247022592, coefficient := (-6641915444998362886247022592) }, { argument := 6641904928522964673323073536, coefficient := (-6641904928522964673323073536) }, { argument := 144128295332508122721812480, coefficient := (-144128295332508122721812480) }, { argument := 6641750089510949010622382080, coefficient := (-6641750089510949010622382080) }, { argument := 25488994979180541728650166272, coefficient := (-25488994979180541728650166272) }, { argument := 6641904928522964673323073536, coefficient := (-6641904928522964673323073536) }, { argument := 144124935350230003902054400, coefficient := (-144124935350230003902054400) }, { argument := 553107193737732212874280960, coefficient := (-553107193737732212874280960) }, { argument := 144128295332508122721812480, coefficient := (-144128295332508122721812480) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 27143548635891947634446827520, coefficient := 27143548635891947634446827520 }, { argument := 104168594959636075385735610368, coefficient := 104168594959636075385735610368 }, { argument := 27144181433000652166905462784, coefficient := 27144181433000652166905462784 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1682881409301358246933561344, coefficient := 1682881409301358246933561344 }, { argument := 77545422775957465435966799872, coefficient := 77545422775957465435966799872 }, { argument := 77545299994428910825191243776, coefficient := 77545299994428910825191243776 }, { argument := 1682720848840940678996295680, coefficient := 1682720848840940678996295680 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11
