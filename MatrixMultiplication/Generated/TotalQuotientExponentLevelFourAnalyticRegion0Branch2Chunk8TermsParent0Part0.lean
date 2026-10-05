import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8

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
def constantNumerator : ℤ := (-106741178018839937541233180672)
def positiveArguments : Array ℕ := #[
    11, 20971323, 20971717, 9039815, 64503093, 18080573,
    1074859, 5108173, 20436947, 1071943
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 396137091346533186687291359232, 396144533796110189248148144128, 341514554938738094779578449920, 1218428977698494528384151846912, 341532367705111479081324511232,
    10151756230821567969496137728, 385962639422394947202898198528, 386043014099933388564435304448, 10124215389493472198609862656
  ]
def positiveScales : Array ℕ := #[
    3, 24, 24, 23, 25, 24,
    20, 22, 24, 20
  ]
def negativeArguments : Array ℕ := #[
    1127062966569, 342800450817909, 85717958931771, 8992041275991, 13618682186739, 194373068954875,
    54478060008249, 1127062966569, 1127079734999, 1127079734999, 342806923473035, 85719578168005,
    8992177974697, 194373068954875, 173356742676511, 194382284268169, 342800450817909, 342806923473035,
    54478060008249, 194382284268169, 27240667174175, 85717958931771, 85719578168005, 8992041275991,
    8992177974697, 5, 3, 5
  ]
def negativeCoefficients : Array ℕ := #[
    2537920178131617095312474112, 96489748910373313321635938304, 96509841976020838740450607104, 2531034608740824186246660096, 30666546010737486010905526272, 109422310114504346798391296000,
    30668421344127214580492402688, 2537920178131617095312474112, 2537957937279166889435594752, 2537957937279166889435594752, 96491570800824160279813160960, 96511665073945855541767045120,
    2531073086005911913058271232, 109422310114504346798391296000, 390364680860048950498036809728, 109427497874693966895647817728, 96489748910373313321635938304, 96491570800824160279813160960,
    30668421344127214580492402688, 109427497874693966895647817728, 30670264633734558064522035200, 96509841976020838740450607104, 96511665073945855541767045120, 2531034608740824186246660096,
    2531073086005911913058271232, 792281625142643375935439503360, 1901475900342344102245054808064, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    40, 48, 46, 43, 43, 47,
    45, 40, 40, 40, 48, 46,
    43, 47, 47, 47, 48, 48,
    45, 47, 44, 46, 46, 43,
    43, 2, 1, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 24321914542590820, 24321941647056597, 23107861817483045, 25942865004778312, 24107937063820786,
    20035715988820305, 22284375955370217, 24284676357701697, 20031796762616448
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40035705256660018, 48284362335167343, 46284662731309506, 43031785796597184, 43630652341110177, 47465821670943237,
    45630740562700562, 40035705256660018, 40035726720900758, 40035726720900758, 48284389575444510, 46284689983965189,
    43031807728552361, 47465821670943237, 47300737279395809, 47465890068132790, 48284362335167343, 48284389575444510,
    45630740562700562, 47465890068132790, 44630827271593482, 46284662731309506, 46284689983965189, 43031785796597184,
    43031807728552361, 2321928094887363, 1584962500724866, 2321928094887363
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
noncomputable def positiveFloor : ℝ := 1100387227 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1068710051 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2537920178131617095312474112, coefficient := (-2537920178131617095312474112) }, { argument := 96489748910373313321635938304, coefficient := (-96489748910373313321635938304) }, { argument := 96509841976020838740450607104, coefficient := (-96509841976020838740450607104) }, { argument := 2531034608740824186246660096, coefficient := (-2531034608740824186246660096) }, { argument := 30666546010737486010905526272, coefficient := (-30666546010737486010905526272) }, { argument := 109422310114504346798391296000, coefficient := (-109422310114504346798391296000) }, { argument := 30668421344127214580492402688, coefficient := (-30668421344127214580492402688) }, { argument := 2537920178131617095312474112, coefficient := (-2537920178131617095312474112) }, { argument := 2537957937279166889435594752, coefficient := (-2537957937279166889435594752) }, { argument := 2537957937279166889435594752, coefficient := (-2537957937279166889435594752) }, { argument := 96491570800824160279813160960, coefficient := (-96491570800824160279813160960) }, { argument := 96511665073945855541767045120, coefficient := (-96511665073945855541767045120) }, { argument := 2531073086005911913058271232, coefficient := (-2531073086005911913058271232) }, { argument := 109422310114504346798391296000, coefficient := (-109422310114504346798391296000) }, { argument := 390364680860048950498036809728, coefficient := (-390364680860048950498036809728) }, { argument := 109427497874693966895647817728, coefficient := (-109427497874693966895647817728) }, { argument := 96489748910373313321635938304, coefficient := (-96489748910373313321635938304) }, { argument := 96491570800824160279813160960, coefficient := (-96491570800824160279813160960) }, { argument := 30668421344127214580492402688, coefficient := (-30668421344127214580492402688) }, { argument := 109427497874693966895647817728, coefficient := (-109427497874693966895647817728) }, { argument := 30670264633734558064522035200, coefficient := (-30670264633734558064522035200) }, { argument := 96509841976020838740450607104, coefficient := (-96509841976020838740450607104) }, { argument := 96511665073945855541767045120, coefficient := (-96511665073945855541767045120) }, { argument := 2531034608740824186246660096, coefficient := (-2531034608740824186246660096) }, { argument := 2531073086005911913058271232, coefficient := (-2531073086005911913058271232) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 396137091346533186687291359232, coefficient := 396137091346533186687291359232 }, { argument := 396144533796110189248148144128, coefficient := 396144533796110189248148144128 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 341514554938738094779578449920, coefficient := 341514554938738094779578449920 }, { argument := 1218428977698494528384151846912, coefficient := 1218428977698494528384151846912 }, { argument := 341532367705111479081324511232, coefficient := 341532367705111479081324511232 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 10151756230821567969496137728, coefficient := 10151756230821567969496137728 }, { argument := 385962639422394947202898198528, coefficient := 385962639422394947202898198528 }, { argument := 386043014099933388564435304448, coefficient := 386043014099933388564435304448 }, { argument := 10124215389493472198609862656, coefficient := 10124215389493472198609862656 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk8
