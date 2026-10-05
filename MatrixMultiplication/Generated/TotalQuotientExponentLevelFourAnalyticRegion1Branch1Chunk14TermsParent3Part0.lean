import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 14, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14

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
def constantNumerator : ℤ := (-1136120382366996878507065305202688)
def positiveArguments : Array ℕ := #[
    6915, 3367, 29762777645, 29762784723, 10032115327, 36423611265,
    19596015
  ]
def positiveCoefficients : Array ℕ := #[
    547862743786137894459356416573440, 266761223185528024677462480781312, 281101487175699904030545113251840, 281101554025519835533242758332416, 47375325172507650691371831918592, 172005641022909238932130957885440,
    47380256990111135053959690977280
  ]
def positiveScales : Array ℕ := #[
    12, 11, 34, 34, 33, 35,
    24
  ]
def negativeArguments : Array ℕ := #[
    5005614711, 9086986205, 5006135759, 124834122483891553, 124834152070513311, 628312577,
    124834152271839903, 124834181858458977, 18249638855, 5027023921, 3367, 887,
    3367
  ]
def negativeCoefficients : Array ℕ := #[
    23638347137385625577027436281856, 85824158169581669740199658127360, 23640807716996791839926742155264, 70275363437697106830380326977536, 70275380093484447390456487084032, 23736978035122025114344395636736,
    70275380206821242979327972212736, 70275396862607072581729149517824, 86181482853327569191931299758080, 23739449273114343214032948822016, 266761223185528024677462480781312, 562203041201219739563787871584256,
    266761223185528024677462480781312
  ]
def negativeScales : Array ℕ := #[
    32, 33, 32, 56, 56, 29,
    56, 56, 34, 32, 11, 9,
    11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12755513536022131, 11717248005820939, 34792790122720124, 34792790465812909, 33223906787127671, 35084154916103930,
    24224056965273236
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32220900103078527, 33081154742679682, 32221050269299428, 56792789951765548, 56792790293695039, 29226907218052764,
    56792790296021749, 56792790637951127, 34087148863427605, 32227057408073443, 11717248005935692, 9792790294858386,
    11717248005935692
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 13
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
noncomputable def positiveFloor : ℝ := 462596318221 / 1000000000000
noncomputable def negativeCeiling : ℝ := 17564734273 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23638347137385625577027436281856, coefficient := (-23638347137385625577027436281856) }, { argument := 85824158169581669740199658127360, coefficient := (-85824158169581669740199658127360) }, { argument := 23640807716996791839926742155264, coefficient := (-23640807716996791839926742155264) }, { argument := 70275363437697106830380326977536, coefficient := (-70275363437697106830380326977536) }, { argument := 70275380093484447390456487084032, coefficient := (-70275380093484447390456487084032) }, { argument := 23736978035122025114344395636736, coefficient := (-23736978035122025114344395636736) }, { argument := 70275380206821242979327972212736, coefficient := (-70275380206821242979327972212736) }, { argument := 70275396862607072581729149517824, coefficient := (-70275396862607072581729149517824) }, { argument := 86181482853327569191931299758080, coefficient := (-86181482853327569191931299758080) }, { argument := 23739449273114343214032948822016, coefficient := (-23739449273114343214032948822016) }, { argument := 547862743786137894459356416573440, coefficient := 547862743786137894459356416573440 }, { argument := 266761223185528024677462480781312, coefficient := 266761223185528024677462480781312 }, { argument := 266761223185528024677462480781312, coefficient := (-266761223185528024677462480781312) }, { argument := 281101487175699904030545113251840, coefficient := 281101487175699904030545113251840 }, { argument := 281101554025519835533242758332416, coefficient := 281101554025519835533242758332416 }, { argument := 562203041201219739563787871584256, coefficient := (-562203041201219739563787871584256) }, { argument := 47375325172507650691371831918592, coefficient := 47375325172507650691371831918592 }, { argument := 172005641022909238932130957885440, coefficient := 172005641022909238932130957885440 }, { argument := 47380256990111135053959690977280, coefficient := 47380256990111135053959690977280 }, { argument := 266761223185528024677462480781312, coefficient := (-266761223185528024677462480781312) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
