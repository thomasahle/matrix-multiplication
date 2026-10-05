import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 19, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    143, 349, 571, 1001, 1003, 1223,
    2439, 7137, 14021, 18917, 18931, 19665
  ]
def positiveCoefficients : Array ℕ := #[
    445420729655194105950904088788992, 792281625142643375935439503360, 445024588842622784262936369037312, 11963452539653914976625136500736, 12201137027196707989405768351744, 87943260390833414728833784872960,
    87864032228319150391240240922624, 929980171592434794673018889043968, 2221716133225000554798159455322112, 235228414504850818315231988547584, 235545327154907875665606164348928, 615127453760748317076275230408704
  ]
def positiveScales : Array ℕ := #[
    7, 8, 9, 9, 9, 10,
    11, 12, 13, 14, 14, 14
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 7, 15, 61, 71,
    77, 83, 87, 151, 239, 401,
    475, 569, 801, 1575, 1579, 1703,
    1941, 2969, 2973, 3405, 662936003109
  ]
def negativeCoefficients : Array ℕ := #[
    3802951800684688204490109616128, 792281625142643375935439503360, 1109194275199700726309615304704, 4753689750855860255612637020160, 4832917913370124593206180970496, 45001596308102143753132963790848,
    12201137027196707989405768351744, 6575937488683940020264147877888, 6892850138740997370638323679232, 11963452539653914976625136500736, 37871061681818353369714008260608, 63540986336439998750022248169472,
    37633377194275560356933376409600, 45080824470616408090726507741184, 63461758173925734412428704219136, 124784355959966331709831721779200, 125101268610023389060205897580544, 269851121523584333843610694844416,
    615127453760748317076275230408704, 235228414504850818315231988547584, 235545327154907875665606164348928, 269771893361070069506017150894080, 1110858066612500277399079727661056
  ]
def negativeScales : Array ℕ := #[
    1, 2, 2, 3, 5, 6,
    6, 6, 6, 7, 7, 8,
    8, 9, 9, 10, 10, 10,
    10, 11, 11, 11, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7159871336778389, 8447083226209649, 9157346935362842, 9967226257978146, 9970105889712599, 10256208688527386,
    11252074042796183, 12801102057105355, 13775301627846313, 14207395692946912, 14208463000677500, 14263342565830272
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 2807354922807594, 3906890600547867, 5930737345064576, 6149747119504683,
    6266786540694902, 6375039431346928, 6442943495848765, 7238404739325080, 7900866812416730, 8647458426474890,
    8891783706984896, 9152284842306582, 9645658432427781, 10621136113284685, 10624795455871307, 10733862719835940,
    10922584409225367, 11535761377987515, 11537703747908557, 11733439083055346, 39270078649462950
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
noncomputable def positiveFloor : ℝ := 810993126527 / 1000000000000
noncomputable def negativeCeiling : ℝ := 202470210633 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-3802951800684688204490109616128) }, { argument := 5, coefficient := (-792281625142643375935439503360) }, { argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 15, coefficient := (-4753689750855860255612637020160) }, { argument := 61, coefficient := (-4832917913370124593206180970496) }, { argument := 71, coefficient := (-45001596308102143753132963790848) }, { argument := 77, coefficient := (-12201137027196707989405768351744) }, { argument := 83, coefficient := (-6575937488683940020264147877888) }, { argument := 87, coefficient := (-6892850138740997370638323679232) }, { argument := 143, coefficient := 445420729655194105950904088788992 }, { argument := 151, coefficient := (-11963452539653914976625136500736) }, { argument := 239, coefficient := (-37871061681818353369714008260608) }, { argument := 349, coefficient := 792281625142643375935439503360 }, { argument := 401, coefficient := (-63540986336439998750022248169472) }, { argument := 475, coefficient := (-37633377194275560356933376409600) }, { argument := 569, coefficient := (-45080824470616408090726507741184) }, { argument := 571, coefficient := 445024588842622784262936369037312 }, { argument := 801, coefficient := (-63461758173925734412428704219136) }, { argument := 1001, coefficient := 11963452539653914976625136500736 }, { argument := 1003, coefficient := 12201137027196707989405768351744 }, { argument := 1223, coefficient := 87943260390833414728833784872960 }, { argument := 1575, coefficient := (-124784355959966331709831721779200) }, { argument := 1579, coefficient := (-125101268610023389060205897580544) }, { argument := 1703, coefficient := (-269851121523584333843610694844416) }, { argument := 1941, coefficient := (-615127453760748317076275230408704) }, { argument := 2439, coefficient := 87864032228319150391240240922624 }, { argument := 2969, coefficient := (-235228414504850818315231988547584) }, { argument := 2973, coefficient := (-235545327154907875665606164348928) }, { argument := 3405, coefficient := (-269771893361070069506017150894080) }, { argument := 7137, coefficient := 929980171592434794673018889043968 }, { argument := 14021, coefficient := 2221716133225000554798159455322112 }, { argument := 18917, coefficient := 235228414504850818315231988547584 }, { argument := 18931, coefficient := 235545327154907875665606164348928 }, { argument := 19665, coefficient := 615127453760748317076275230408704 }, { argument := 662936003109, coefficient := (-1110858066612500277399079727661056) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19
