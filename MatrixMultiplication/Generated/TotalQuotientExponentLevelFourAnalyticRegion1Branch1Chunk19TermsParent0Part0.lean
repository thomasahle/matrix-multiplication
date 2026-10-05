import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 19, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19

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
def constantNumerator : ℤ := (-1098313414966488341534057024192512)
def positiveArguments : Array ℕ := #[
    7095, 3373, 31222400321, 31222397631, 10009177007, 4571513099,
    10008267769
  ]
def positiveCoefficients : Array ℕ := #[
    562123813038705475226194327633920, 267236592160613610703023744483328, 294887233581257703442516207992832, 294887208174926025603824958308352, 47267002018966312251173604687872, 172706881877737137631151345631232,
    47262708263910160820698794164224
  ]
def positiveScales : Array ℕ := #[
    12, 11, 34, 34, 33, 32,
    33
  ]
def negativeArguments : Array ℕ := #[
    156722775, 18323691309, 5014674931, 32739061049328079, 32739058228657713, 4994048207,
    32739058228657713, 32739055407989199, 18248413483, 2496796419, 3373, 1861,
    3373
  ]
def negativeCoefficients : Array ℕ := #[
    23683276152394264356988964044800, 86531185680071415382114842968064, 23681132816641050793985469054976, 73721811571106928173779194478592, 73721805219521923547478909517824, 23583725866572047894184640643072,
    73721805219521923547478909517824, 73721798867941089254433569636352, 86175696197665722249036502663168, 23581575447269110026713325109248, 267236592160613610703023744483328, 589774441756183729046341166301184,
    267236592160613610703023744483328
  ]
def negativeScales : Array ℕ := #[
    27, 34, 32, 54, 54, 32,
    54, 54, 34, 31, 11, 10,
    11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12792586968913521, 11719816603011014, 34861862402073468, 34861862277776496, 33220604303993405, 32090024607699435,
    33220473242994445
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    27223639607014169, 34092991112611331, 32223509037249591, 54861862466524712, 54861862342227699, 32217562601496713,
    54861862342227699, 54861862217930757, 34087051990416851, 31217431047189631, 11719816603132712, 10861862342227719,
    11719816603132712
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
noncomputable def positiveFloor : ℝ := 2976623509 / 6250000000
noncomputable def negativeCeiling : ℝ := 22653402823 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23683276152394264356988964044800, coefficient := (-23683276152394264356988964044800) }, { argument := 86531185680071415382114842968064, coefficient := (-86531185680071415382114842968064) }, { argument := 23681132816641050793985469054976, coefficient := (-23681132816641050793985469054976) }, { argument := 73721811571106928173779194478592, coefficient := (-73721811571106928173779194478592) }, { argument := 73721805219521923547478909517824, coefficient := (-73721805219521923547478909517824) }, { argument := 23583725866572047894184640643072, coefficient := (-23583725866572047894184640643072) }, { argument := 73721805219521923547478909517824, coefficient := (-73721805219521923547478909517824) }, { argument := 73721798867941089254433569636352, coefficient := (-73721798867941089254433569636352) }, { argument := 86175696197665722249036502663168, coefficient := (-86175696197665722249036502663168) }, { argument := 23581575447269110026713325109248, coefficient := (-23581575447269110026713325109248) }, { argument := 562123813038705475226194327633920, coefficient := 562123813038705475226194327633920 }, { argument := 267236592160613610703023744483328, coefficient := 267236592160613610703023744483328 }, { argument := 267236592160613610703023744483328, coefficient := (-267236592160613610703023744483328) }, { argument := 294887233581257703442516207992832, coefficient := 294887233581257703442516207992832 }, { argument := 294887208174926025603824958308352, coefficient := 294887208174926025603824958308352 }, { argument := 589774441756183729046341166301184, coefficient := (-589774441756183729046341166301184) }, { argument := 47267002018966312251173604687872, coefficient := 47267002018966312251173604687872 }, { argument := 172706881877737137631151345631232, coefficient := 172706881877737137631151345631232 }, { argument := 47262708263910160820698794164224, coefficient := 47262708263910160820698794164224 }, { argument := 267236592160613610703023744483328, coefficient := (-267236592160613610703023744483328) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19
