import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    7, 1, 25156251, 25175397, 18770983, 63112263,
    9390025, 7013, 8160387, 2041047, 228225
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 158456325028528675187087900672, 475188146228223981106740854784, 475549803942948070015786549248, 177286921939431803044637966336, 596078470898508086886946308096,
    177372557333232161190943129600, 2119549193239348600553603072, 77072676112090350992914120704, 77108575542093126035828637696, 2155524181105849557791539200
  ]
def positiveScales : Array ℕ := #[
    2, 0, 24, 24, 24, 25,
    23, 12, 22, 20, 17
  ]
def negativeArguments : Array ℕ := #[
    7013, 8160387, 2041047, 228225, 157402245193783, 529223186182791,
    78739141088929, 157402245193783, 157522591129545, 7013, 157522591129545, 529624882417017,
    78799336581471, 529223186182791, 529624882417017, 8160387, 78739141088929, 78799336581471,
    2041047, 228225, 1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1059774596619674300276801536, 38536338056045175496457060352, 38554287771046563017914318848, 1077762090552924778895769600, 44304793300125035234641051648, 148963084005540260937933520896,
    44326195808446694380795854848, 44304793300125035234641051648, 44338667669590866287677931520, 1059774596619674300276801536, 44338667669590866287677931520, 149076151443713782505539633152,
    44360082858169386214675709952, 148963084005540260937933520896, 149076151443713782505539633152, 38536338056045175496457060352, 44326195808446694380795854848, 44360082858169386214675709952,
    38554287771046563017914318848, 1077762090552924778895769600, 158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    12, 22, 20, 17, 47, 48,
    46, 47, 47, 12, 47, 48,
    46, 48, 48, 22, 46, 46,
    20, 17, 0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 0, 24584413599675292, 24585511193006033, 24162000867501855, 25911417018539976,
    23162697568239220, 12775816012648766, 22960206141068884, 20960877972816958, 17800097308970370
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    12775816013064368, 22960206154204373, 20960877986100454, 17800097309657793, 47161449448092074, 48910869603688904,
    46162146208751726, 47161449448092074, 47162552076231496, 12775816013064368, 47162552076231496, 48911964237121006,
    46163248717092352, 48910869603688904, 48911964237121006, 22960206154204373, 46162146208751726, 46163248717092352,
    20960877986100454, 17800097309657793, 0, 1584962500724866, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 323654609 / 500000000000
noncomputable def negativeCeiling : ℝ := 627965443 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1059774596619674300276801536, coefficient := (-1059774596619674300276801536) }, { argument := 38536338056045175496457060352, coefficient := (-38536338056045175496457060352) }, { argument := 38554287771046563017914318848, coefficient := (-38554287771046563017914318848) }, { argument := 1077762090552924778895769600, coefficient := (-1077762090552924778895769600) }, { argument := 44304793300125035234641051648, coefficient := (-44304793300125035234641051648) }, { argument := 148963084005540260937933520896, coefficient := (-148963084005540260937933520896) }, { argument := 44326195808446694380795854848, coefficient := (-44326195808446694380795854848) }, { argument := 44304793300125035234641051648, coefficient := (-44304793300125035234641051648) }, { argument := 44338667669590866287677931520, coefficient := (-44338667669590866287677931520) }, { argument := 1059774596619674300276801536, coefficient := (-1059774596619674300276801536) }, { argument := 44338667669590866287677931520, coefficient := (-44338667669590866287677931520) }, { argument := 149076151443713782505539633152, coefficient := (-149076151443713782505539633152) }, { argument := 44360082858169386214675709952, coefficient := (-44360082858169386214675709952) }, { argument := 148963084005540260937933520896, coefficient := (-148963084005540260937933520896) }, { argument := 149076151443713782505539633152, coefficient := (-149076151443713782505539633152) }, { argument := 38536338056045175496457060352, coefficient := (-38536338056045175496457060352) }, { argument := 44326195808446694380795854848, coefficient := (-44326195808446694380795854848) }, { argument := 44360082858169386214675709952, coefficient := (-44360082858169386214675709952) }, { argument := 38554287771046563017914318848, coefficient := (-38554287771046563017914318848) }, { argument := 1077762090552924778895769600, coefficient := (-1077762090552924778895769600) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475188146228223981106740854784, coefficient := 475188146228223981106740854784 }, { argument := 475549803942948070015786549248, coefficient := 475549803942948070015786549248 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 177286921939431803044637966336, coefficient := 177286921939431803044637966336 }, { argument := 596078470898508086886946308096, coefficient := 596078470898508086886946308096 }, { argument := 177372557333232161190943129600, coefficient := 177372557333232161190943129600 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2119549193239348600553603072, coefficient := 2119549193239348600553603072 }, { argument := 77072676112090350992914120704, coefficient := 77072676112090350992914120704 }, { argument := 77108575542093126035828637696, coefficient := 77108575542093126035828637696 }, { argument := 2155524181105849557791539200, coefficient := 2155524181105849557791539200 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5
