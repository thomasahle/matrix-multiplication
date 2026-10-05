import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 0, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0

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
    1, 1559045, 10543307, 3115819, 58071, 2039083,
    8155897, 232703
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 29449527413142024088746721280, 99578719190809820938155065344, 29428078424576830160186114048, 2193860352213785337636323328, 77034377719914278170231046144,
    77030269261074181578895130624, 2197817695326430100325400576
  ]
def positiveScales : Array ℕ := #[
    0, 20, 23, 21, 15, 20,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    90535302195, 3179022155735, 12715410438365, 362794448635, 90535302195, 612260380797,
    180938725149, 612260380797, 21498678067481, 85990125931379, 2453459168821, 3179022155735,
    21498678067481, 6353413553977, 180938725149, 6353413553977, 25412298834643, 725060428757,
    12715410438365, 85990125931379, 25412298834643, 362794448635, 2453459168821, 725060428757,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    203867376614638624293519360, 7158521497985348451728097280, 7158139714010441149453434880, 204235117960583818898309120, 203867376614638624293519360, 689343905702771796190691328,
    203718893789482248333950976, 689343905702771796190691328, 24205359633416421664719110144, 24204068693881280605794074624, 690587362404436402373656576, 7158521497985348451728097280,
    24205359633416421664719110144, 7153307728555368968668315648, 203718893789482248333950976, 7153307728555368968668315648, 7152926222645369034200055808, 204086367298194828890734592,
    7158139714010441149453434880, 24204068693881280605794074624, 7152926222645369034200055808, 204235117960583818898309120, 690587362404436402373656576, 204086367298194828890734592,
    158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    36, 41, 43, 38, 36, 39,
    37, 39, 44, 46, 41, 41,
    44, 42, 37, 42, 44, 39,
    43, 46, 44, 38, 41, 39,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 20572231139655986, 23329824116024454, 21571179998042343, 15825530257377616, 20959489069403038,
    22959412124390183, 17828130284410333
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36397761397100502, 41531720209814402, 43531643264800579, 38400361424136716, 36397761397100502, 39155354373468804,
    37396710255486853, 39155354373468804, 44289313186181954, 46289236241168132, 41157954400505018, 41531720209814402,
    44289313186181954, 42530669068200730, 37396710255486853, 42530669068200730, 44530592123186906, 39399310282523068,
    43531643264800579, 46289236241168132, 44530592123186906, 38400361424136716, 41157954400505018, 39399310282523068,
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
noncomputable def positiveFloor : ℝ := 84510621 / 1000000000000
noncomputable def negativeCeiling : ℝ := 42255311 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 203867376614638624293519360, coefficient := (-203867376614638624293519360) }, { argument := 7158521497985348451728097280, coefficient := (-7158521497985348451728097280) }, { argument := 7158139714010441149453434880, coefficient := (-7158139714010441149453434880) }, { argument := 204235117960583818898309120, coefficient := (-204235117960583818898309120) }, { argument := 203867376614638624293519360, coefficient := (-203867376614638624293519360) }, { argument := 689343905702771796190691328, coefficient := (-689343905702771796190691328) }, { argument := 203718893789482248333950976, coefficient := (-203718893789482248333950976) }, { argument := 689343905702771796190691328, coefficient := (-689343905702771796190691328) }, { argument := 24205359633416421664719110144, coefficient := (-24205359633416421664719110144) }, { argument := 24204068693881280605794074624, coefficient := (-24204068693881280605794074624) }, { argument := 690587362404436402373656576, coefficient := (-690587362404436402373656576) }, { argument := 7158521497985348451728097280, coefficient := (-7158521497985348451728097280) }, { argument := 24205359633416421664719110144, coefficient := (-24205359633416421664719110144) }, { argument := 7153307728555368968668315648, coefficient := (-7153307728555368968668315648) }, { argument := 203718893789482248333950976, coefficient := (-203718893789482248333950976) }, { argument := 7153307728555368968668315648, coefficient := (-7153307728555368968668315648) }, { argument := 7152926222645369034200055808, coefficient := (-7152926222645369034200055808) }, { argument := 204086367298194828890734592, coefficient := (-204086367298194828890734592) }, { argument := 7158139714010441149453434880, coefficient := (-7158139714010441149453434880) }, { argument := 24204068693881280605794074624, coefficient := (-24204068693881280605794074624) }, { argument := 7152926222645369034200055808, coefficient := (-7152926222645369034200055808) }, { argument := 204235117960583818898309120, coefficient := (-204235117960583818898309120) }, { argument := 690587362404436402373656576, coefficient := (-690587362404436402373656576) }, { argument := 204086367298194828890734592, coefficient := (-204086367298194828890734592) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 29449527413142024088746721280, coefficient := 29449527413142024088746721280 }, { argument := 99578719190809820938155065344, coefficient := 99578719190809820938155065344 }, { argument := 29428078424576830160186114048, coefficient := 29428078424576830160186114048 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 2193860352213785337636323328, coefficient := 2193860352213785337636323328 }, { argument := 77034377719914278170231046144, coefficient := 77034377719914278170231046144 }, { argument := 77030269261074181578895130624, coefficient := 77030269261074181578895130624 }, { argument := 2197817695326430100325400576, coefficient := 2197817695326430100325400576 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0
