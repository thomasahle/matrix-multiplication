import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 1,
parent chunk 9, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 80078894575450910421096062779392
def positiveArguments : Array ℕ := #[
    5, 9, 67, 17, 5, 15,
    5, 133, 17, 15, 2423, 15,
    133, 133, 5, 15, 5, 17,
    17, 9, 15409857, 53064241, 7705991, 1121635,
    20410695, 81650735, 2235375, 139181, 5121865, 56586729,
    5121927, 69581
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 696341272098026404630757376, 5183873914507529901140082688, 5261245166962866168321277952, 773712524553362671811952640, 4642275147320176030871715840,
    773712524553362671811952640, 5145188288279861767549485056, 5261245166962866168321277952, 4642275147320176030871715840, 93735272349639887690018062336, 4642275147320176030871715840,
    5145188288279861767549485056, 5145188288279861767549485056, 773712524553362671811952640, 4642275147320176030871715840, 773712524553362671811952640, 5261245166962866168321277952,
    5261245166962866168321277952, 696341272098026404630757376, 145541984405228364767579602944, 501177586274634450408122089472, 145562054462780560759737810944, 21187086120053978037055651840,
    771094255680600425719671029760, 771169388531342881775020933120, 21112519953289466339131392000, 1314527378904560180974845952, 48374647211566270764894126080, 534446544809655512067125280768,
    48375232785010146600900624384, 1314347928978211134456725504
  ]
def positiveScales : Array ℕ := #[
    2, 3, 6, 4, 2, 3,
    2, 7, 4, 3, 11, 3,
    7, 7, 2, 3, 2, 4,
    4, 3, 23, 25, 22, 20,
    24, 26, 21, 17, 22, 25,
    22, 16
  ]
def negativeArguments : Array ℕ := #[
    1129193580371, 164174358403, 1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    635679473473498978296266752, 184843894831885264692969472, 158456325028528675187087900672, 792281625142643375935439503360, 1584563250285286751870879006720, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    40, 37, 0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 3169925001442312, 6066089190457772, 4087462841250339, 2321928094887362, 3906890595303263,
    2321928094887362, 7055282435501189, 4087462841250339, 3906890595303263, 11242578689451346, 3906890595303263,
    7055282435501189, 7055282435501189, 2321928094887362, 3906890595303263, 2321928094887362, 4087462841250339,
    4087462841250339, 3169925001442312, 23877350138062573, 25661236647449997, 22877549070187072, 20097171842988806,
    24282821972303987, 26282962536845810, 21092085443354069, 17086602752601303, 22288237796801286, 25753960408935111,
    22288255260469533, 16086405792693424
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40038429970641712, 37256437860928099, 0, 2321928094887363, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 32
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 193887831 / 200000000000
noncomputable def negativeCeiling : ℝ := 66820153 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 635679473473498978296266752, coefficient := (-635679473473498978296266752) }, { argument := 184843894831885264692969472, coefficient := (-184843894831885264692969472) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5183873914507529901140082688, coefficient := 5183873914507529901140082688 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 773712524553362671811952640, coefficient := 773712524553362671811952640 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 145541984405228364767579602944, coefficient := 145541984405228364767579602944 }, { argument := 501177586274634450408122089472, coefficient := 501177586274634450408122089472 }, { argument := 145562054462780560759737810944, coefficient := 145562054462780560759737810944 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 21187086120053978037055651840, coefficient := 21187086120053978037055651840 }, { argument := 771094255680600425719671029760, coefficient := 771094255680600425719671029760 }, { argument := 771169388531342881775020933120, coefficient := 771169388531342881775020933120 }, { argument := 21112519953289466339131392000, coefficient := 21112519953289466339131392000 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 1314527378904560180974845952, coefficient := 1314527378904560180974845952 }, { argument := 48374647211566270764894126080, coefficient := 48374647211566270764894126080 }, { argument := 534446544809655512067125280768, coefficient := 534446544809655512067125280768 }, { argument := 48375232785010146600900624384, coefficient := 48375232785010146600900624384 }, { argument := 1314347928978211134456725504, coefficient := 1314347928978211134456725504 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end TermShard2


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9
