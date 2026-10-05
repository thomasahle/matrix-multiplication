import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 18, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18

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
    261, 383, 473, 1951, 9809, 12955,
    13217, 26253, 26325, 60463, 61607, 101675,
    102643
  ]
def positiveCoefficients : Array ℕ := #[
    191415240634462639626002184011776, 395903128083778894954939119828992, 1267650600228229401496703205376, 1109194275199700726309615304704, 1554298092204837774910145217691648, 34147338043647929502817442594816,
    52765956234500048837300270923776, 51498305634271819435803567718400, 35494216806390423241907689750528, 351139216263219544214586787889152, 355259080713961289769451073306624, 335531268247909469708658629672960,
    336085865385509320071813437325312
  ]
def positiveScales : Array ℕ := #[
    8, 8, 8, 10, 13, 13,
    13, 14, 14, 15, 15, 16,
    16
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 37, 59, 123, 153,
    159, 271, 325, 333, 389, 521,
    1193, 1543, 2121, 4235, 19623664279671
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 1109194275199700726309615304704, 187612288833777951421512074395648, 9348923176683191836038186139648, 9745063989254513524005905891328, 24243817729364887303624448802816,
    25194555679536059354746976206848, 42941664082731270975700821082112, 51498305634271819435803567718400, 52765956234500048837300270923776, 123279020872195309295554386722816, 41277872669931719886236398125056,
    189038395759034709498195865501696, 122249054759509872906838315368448, 336085865385509320071813437325312, 335531268247909469708658629672960, 777149046102418887455072608845824
  ]
def negativeScales : Array ℕ := #[
    1, 2, 5, 5, 6, 7,
    7, 8, 8, 8, 8, 9,
    10, 10, 11, 12, 44
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8027905996569884, 8581200581924749, 8885696373130892, 10929998062151574, 13259890349895821, 13661221395065699,
    13690107130046508, 14680194672337687, 14684145910797358, 15883764942464419, 15910806663446516, 16633605465235989,
    16647275716985478
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 5209453365628950, 5882643052550791, 6942514514520450, 7257387842692652,
    7312882955284356, 8082149041353872, 8344295907915818, 8379378367071265, 8603626344992442, 9025139562278509,
    10220378327695229, 10591522346575200, 11050528905530556, 12048146254219561, 44157659691225234
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 303569597201 / 500000000000
noncomputable def negativeCeiling : ℝ := 37177457733 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-950737950171172051122527404032) }, { argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 37, coefficient := (-187612288833777951421512074395648) }, { argument := 59, coefficient := (-9348923176683191836038186139648) }, { argument := 123, coefficient := (-9745063989254513524005905891328) }, { argument := 153, coefficient := (-24243817729364887303624448802816) }, { argument := 159, coefficient := (-25194555679536059354746976206848) }, { argument := 261, coefficient := 191415240634462639626002184011776 }, { argument := 271, coefficient := (-42941664082731270975700821082112) }, { argument := 325, coefficient := (-51498305634271819435803567718400) }, { argument := 333, coefficient := (-52765956234500048837300270923776) }, { argument := 383, coefficient := 395903128083778894954939119828992 }, { argument := 389, coefficient := (-123279020872195309295554386722816) }, { argument := 473, coefficient := 1267650600228229401496703205376 }, { argument := 521, coefficient := (-41277872669931719886236398125056) }, { argument := 1193, coefficient := (-189038395759034709498195865501696) }, { argument := 1543, coefficient := (-122249054759509872906838315368448) }, { argument := 1951, coefficient := 1109194275199700726309615304704 }, { argument := 2121, coefficient := (-336085865385509320071813437325312) }, { argument := 4235, coefficient := (-335531268247909469708658629672960) }, { argument := 9809, coefficient := 1554298092204837774910145217691648 }, { argument := 12955, coefficient := 34147338043647929502817442594816 }, { argument := 13217, coefficient := 52765956234500048837300270923776 }, { argument := 26253, coefficient := 51498305634271819435803567718400 }, { argument := 26325, coefficient := 35494216806390423241907689750528 }, { argument := 60463, coefficient := 351139216263219544214586787889152 }, { argument := 61607, coefficient := 355259080713961289769451073306624 }, { argument := 101675, coefficient := 335531268247909469708658629672960 }, { argument := 102643, coefficient := 336085865385509320071813437325312 }, { argument := 19623664279671, coefficient := (-777149046102418887455072608845824) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18
