import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16

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
    69, 305, 555, 951, 1897, 2069,
    4109, 4849, 6651, 22709, 22811, 45439,
    123227, 124011
  ]
def positiveCoefficients : Array ℕ := #[
    835777886362974497274295132094464, 40089450232217754822333238870016, 838313187563430956077288538505216, 2931442013027780490961126162432, 2772985687999251815774038261760, 524807348494486972219635127025664,
    523539697894258742818138423820288, 39376396769589375783991343316992, 4215572071058976874677286509477888, 101966645155858202482891064082432, 102758926781000845858826503585792, 979339316838821476993796770103296,
    947489595508087213281192102068224, 949707984058486614733811332677632
  ]
def positiveScales : Array ℕ := #[
    6, 8, 9, 9, 10, 11,
    12, 12, 12, 14, 14, 15,
    16, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 13, 27, 31, 87,
    93, 119, 171, 207, 253, 369,
    413, 479, 497, 925, 1867, 4035,
    4047, 5701, 5705, 12361, 7328963452393
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 713053462628379038341895553024, 2059932225370872777432142708736, 2139160387885137115025686659072, 9824292151768777861599449841664, 55142801109927978965106589433856,
    29472876455306333584798349524992, 47140756695987280868158650449920, 54192063159756806913984062029824, 524807348494486972219635127025664, 40089450232217754822333238870016, 29235191967763540572017717673984,
    523539697894258742818138423820288, 37950289844332617707307552210944, 39376396769589375783991343316992, 146572100651389024548056308121600, 147918979414131518287146555277312, 319685635745056602189949839605760,
    320636373695227774241072367009792, 451679754493820988620794060865536, 451996667143878045971168236666880, 979339316838821476993796770103296, 2107786035529488437338643254738944
  ]
def negativeScales : Array ℕ := #[
    1, 3, 3, 4, 4, 6,
    6, 6, 7, 7, 7, 8,
    8, 8, 8, 9, 10, 11,
    11, 12, 12, 13, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6108524456778168, 8252665432450248, 9116343961237468, 9893301530621223, 10889503963188028, 11014717929860009,
    12004571615167656, 12243471538396329, 12699355555584036, 14470976557333334, 14477442073170891, 15471643464591952,
    16910958870550369, 16920108569999150
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 3700439718214233, 4754887502413606, 4954196321574415, 6442943495848765,
    6539158811108986, 6894817767286876, 7417852514885912, 7693486957561383, 7982993592700323, 8527477006061059,
    8689997971476554, 8903881850417809, 8957102053308650, 9853309557248504, 10866506214592011, 11978352974859598,
    11982637151571397, 12476999286133185, 12478011171176172, 13593507840974660, 42736746308820958
  ]

abbrev PositiveTerm := Fin 14
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
noncomputable def positiveFloor : ℝ := 1557929785379 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1644055200441 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 9, coefficient := (-713053462628379038341895553024) }, { argument := 13, coefficient := (-2059932225370872777432142708736) }, { argument := 27, coefficient := (-2139160387885137115025686659072) }, { argument := 31, coefficient := (-9824292151768777861599449841664) }, { argument := 69, coefficient := 835777886362974497274295132094464 }, { argument := 87, coefficient := (-55142801109927978965106589433856) }, { argument := 93, coefficient := (-29472876455306333584798349524992) }, { argument := 119, coefficient := (-47140756695987280868158650449920) }, { argument := 171, coefficient := (-54192063159756806913984062029824) }, { argument := 207, coefficient := (-524807348494486972219635127025664) }, { argument := 253, coefficient := (-40089450232217754822333238870016) }, { argument := 305, coefficient := 40089450232217754822333238870016 }, { argument := 369, coefficient := (-29235191967763540572017717673984) }, { argument := 413, coefficient := (-523539697894258742818138423820288) }, { argument := 479, coefficient := (-37950289844332617707307552210944) }, { argument := 497, coefficient := (-39376396769589375783991343316992) }, { argument := 555, coefficient := 838313187563430956077288538505216 }, { argument := 925, coefficient := (-146572100651389024548056308121600) }, { argument := 951, coefficient := 2931442013027780490961126162432 }, { argument := 1867, coefficient := (-147918979414131518287146555277312) }, { argument := 1897, coefficient := 2772985687999251815774038261760 }, { argument := 2069, coefficient := 524807348494486972219635127025664 }, { argument := 4035, coefficient := (-319685635745056602189949839605760) }, { argument := 4047, coefficient := (-320636373695227774241072367009792) }, { argument := 4109, coefficient := 523539697894258742818138423820288 }, { argument := 4849, coefficient := 39376396769589375783991343316992 }, { argument := 5701, coefficient := (-451679754493820988620794060865536) }, { argument := 5705, coefficient := (-451996667143878045971168236666880) }, { argument := 6651, coefficient := 4215572071058976874677286509477888 }, { argument := 12361, coefficient := (-979339316838821476993796770103296) }, { argument := 22709, coefficient := 101966645155858202482891064082432 }, { argument := 22811, coefficient := 102758926781000845858826503585792 }, { argument := 45439, coefficient := 979339316838821476993796770103296 }, { argument := 123227, coefficient := 947489595508087213281192102068224 }, { argument := 124011, coefficient := 949707984058486614733811332677632 }, { argument := 7328963452393, coefficient := (-2107786035529488437338643254738944) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk16
