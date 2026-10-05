import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10

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
    13, 25165807, 25165841, 21548587, 74339795, 10776065,
    652435, 766043, 12258279, 649279
  ]
def positiveCoefficients : Array ℕ := #[
    1029966112685436388716071354368, 237684326982332595212694585344, 237684648103253430348569116672, 203520650004001119092923695104, 702119512502800873817783664640, 203554112692898733398907944960,
    6162074352502113949995499520, 231522290408762344219860795392, 231552343549059326642000756736, 6132266775262240749406650368
  ]
def positiveScales : Array ℕ := #[
    3, 24, 24, 24, 26, 23,
    19, 19, 23, 19
  ]
def negativeArguments : Array ℕ := #[
    5473018859135, 6426030062997, 102829827253051, 5446544472171, 66335932002975, 228842559900951,
    33173403344933, 5473018859135, 5473024061825, 5473024061825, 6426038813291, 102829967318213,
    5446549555093, 228842559900951, 789491988519647, 114440124845061, 6426030062997, 6426038813291,
    33173403344933, 114440124845061, 16589420972523, 102829827253051, 102829967318213, 5446544472171,
    5446549555093, 3, 7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1540517855912005196117442560, 57880533194369788272678273024, 57888046462426619736240422912, 1533065978457884401311154176, 18671904915617048147106201600, 64413454218527083351146233856,
    18674965867856428048209412096, 1540517855912005196117442560, 1540519320339051778880307200, 1540519320339051778880307200, 57880612010011383837252124672, 57888125312103043584759955456,
    1533067409173235973392171008, 64413454218527083351146233856, 222222239081817133446890258432, 64424062951056220110855340032, 57880533194369788272678273024, 57880612010011383837252124672,
    18674965867856428048209412096, 64424062951056220110855340032, 18678027527536718540389220352, 57888046462426619736240422912, 57888125312103043584759955456, 1533065978457884401311154176,
    1533067409173235973392171008, 475368975085586025561263702016, 1109194275199700726309615304704, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    42, 42, 46, 42, 45, 47,
    44, 42, 42, 42, 42, 46,
    42, 47, 49, 46, 42, 42,
    44, 46, 43, 46, 46, 42,
    42, 1, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3700439718136550, 24584961526152240, 24584963475288950, 24361089935153414, 26147631374029566, 23361327122323242,
    19315474652213184, 19547065851111259, 23547253110413976, 19308479022650194
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    42315473966495351, 42547064868857463, 46547252127863564, 42308478349461471, 45914855781962253, 47701348716488420,
    44915092268766980, 42315473966495351, 42315475337930694, 42315475337930694, 42547066833366973, 46547254092966320,
    42308479695838606, 47701348716488420, 49487917954633377, 46701586305138180, 42547064868857463, 42547066833366973,
    44915092268766980, 46701586305138180, 43915328771456102, 46547252127863564, 46547254092966320, 42308478349461471,
    42308479695838606, 1584962500724866, 2807354922807594, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 161855539 / 250000000000
noncomputable def negativeCeiling : ℝ := 125871063 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1540517855912005196117442560, coefficient := (-1540517855912005196117442560) }, { argument := 57880533194369788272678273024, coefficient := (-57880533194369788272678273024) }, { argument := 57888046462426619736240422912, coefficient := (-57888046462426619736240422912) }, { argument := 1533065978457884401311154176, coefficient := (-1533065978457884401311154176) }, { argument := 18671904915617048147106201600, coefficient := (-18671904915617048147106201600) }, { argument := 64413454218527083351146233856, coefficient := (-64413454218527083351146233856) }, { argument := 18674965867856428048209412096, coefficient := (-18674965867856428048209412096) }, { argument := 1540517855912005196117442560, coefficient := (-1540517855912005196117442560) }, { argument := 1540519320339051778880307200, coefficient := (-1540519320339051778880307200) }, { argument := 1540519320339051778880307200, coefficient := (-1540519320339051778880307200) }, { argument := 57880612010011383837252124672, coefficient := (-57880612010011383837252124672) }, { argument := 57888125312103043584759955456, coefficient := (-57888125312103043584759955456) }, { argument := 1533067409173235973392171008, coefficient := (-1533067409173235973392171008) }, { argument := 64413454218527083351146233856, coefficient := (-64413454218527083351146233856) }, { argument := 222222239081817133446890258432, coefficient := (-222222239081817133446890258432) }, { argument := 64424062951056220110855340032, coefficient := (-64424062951056220110855340032) }, { argument := 57880533194369788272678273024, coefficient := (-57880533194369788272678273024) }, { argument := 57880612010011383837252124672, coefficient := (-57880612010011383837252124672) }, { argument := 18674965867856428048209412096, coefficient := (-18674965867856428048209412096) }, { argument := 64424062951056220110855340032, coefficient := (-64424062951056220110855340032) }, { argument := 18678027527536718540389220352, coefficient := (-18678027527536718540389220352) }, { argument := 57888046462426619736240422912, coefficient := (-57888046462426619736240422912) }, { argument := 57888125312103043584759955456, coefficient := (-57888125312103043584759955456) }, { argument := 1533065978457884401311154176, coefficient := (-1533065978457884401311154176) }, { argument := 1533067409173235973392171008, coefficient := (-1533067409173235973392171008) }, { argument := 1029966112685436388716071354368, coefficient := 1029966112685436388716071354368 }, { argument := 237684326982332595212694585344, coefficient := 237684326982332595212694585344 }, { argument := 237684648103253430348569116672, coefficient := 237684648103253430348569116672 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 203520650004001119092923695104, coefficient := 203520650004001119092923695104 }, { argument := 702119512502800873817783664640, coefficient := 702119512502800873817783664640 }, { argument := 203554112692898733398907944960, coefficient := 203554112692898733398907944960 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 6162074352502113949995499520, coefficient := 6162074352502113949995499520 }, { argument := 231522290408762344219860795392, coefficient := 231522290408762344219860795392 }, { argument := 231552343549059326642000756736, coefficient := 231552343549059326642000756736 }, { argument := 6132266775262240749406650368, coefficient := 6132266775262240749406650368 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10
