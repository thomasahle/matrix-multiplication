import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7

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
    1, 44253, 1318493, 3511195, 20659, 23757
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 417957767932860819283378176, 12452814302196494253483360256, 132649196662555871408826613760, 12487599253709312060127444992, 448757042134136645367103488
  ]
def positiveScales : Array ℕ := #[
    0, 15, 20, 21, 14, 14
  ]
def negativeArguments : Array ℕ := #[
    1958328009, 58347270729, 155380912335, 914222727, 1051318521, 58347270729,
    1738423791049, 4629486029135, 27238746887, 31323438201, 155380912335, 4629486029135,
    12328490328025, 72537777505, 83415459615, 914222727, 27238746887, 72537777505,
    426794281, 490795863, 1051318521, 31323438201, 83415459615, 490795863,
    564395049, 1
  ]
def negativeCoefficients : Array ℕ := #[
    551220330725100333563904, 16423296669575615531188224, 174943354723098426385367040, 16469172530603354769850368, 591839712427912621719552, 16423296669575615531188224,
    489322796098767587475718144, 5212337888932325797123850240, 490689641321329831662583808, 17633528076248294948339712, 174943354723098426385367040, 5212337888932325797123850240,
    55522584447334153999246950400, 5226897723868831152791879680, 187834916419526328865259520, 16469172530603354769850368, 490689641321329831662583808, 5226897723868831152791879680,
    492060304608117442798944256, 17682784525774248040464384, 591839712427912621719552, 17633528076248294948339712, 187834916419526328865259520, 17682784525774248040464384,
    635452333091538207768576, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    30, 35, 37, 29, 29, 35,
    40, 42, 34, 34, 37, 42,
    43, 36, 36, 29, 34, 36,
    28, 28, 29, 34, 36, 28,
    29, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15433487641262925, 20330458481146977, 21743530690202026, 14334482801711899, 14536065045722443
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30866975284912491, 35763946122714004, 37177018331477057, 29767970443306230, 29969552701433304, 35763946122714004,
    40660916962322016, 42073989171361108, 34664941282889897, 34866523529236051, 37177018331477057, 42073989171361108,
    43487061380428434, 36078013491926030, 36279595735936628, 29767970443306230, 34664941282889897, 36078013491926030,
    28668965603458069, 28870547849985356, 29969552701433304, 34866523529236051, 36279595735936628, 28870547849985356,
    29072130091444997, 0
  ]

abbrev PositiveTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 20038159 / 500000000000
noncomputable def negativeCeiling : ℝ := 40076319 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 551220330725100333563904, coefficient := (-551220330725100333563904) }, { argument := 16423296669575615531188224, coefficient := (-16423296669575615531188224) }, { argument := 174943354723098426385367040, coefficient := (-174943354723098426385367040) }, { argument := 16469172530603354769850368, coefficient := (-16469172530603354769850368) }, { argument := 591839712427912621719552, coefficient := (-591839712427912621719552) }, { argument := 16423296669575615531188224, coefficient := (-16423296669575615531188224) }, { argument := 489322796098767587475718144, coefficient := (-489322796098767587475718144) }, { argument := 5212337888932325797123850240, coefficient := (-5212337888932325797123850240) }, { argument := 490689641321329831662583808, coefficient := (-490689641321329831662583808) }, { argument := 17633528076248294948339712, coefficient := (-17633528076248294948339712) }, { argument := 174943354723098426385367040, coefficient := (-174943354723098426385367040) }, { argument := 5212337888932325797123850240, coefficient := (-5212337888932325797123850240) }, { argument := 55522584447334153999246950400, coefficient := (-55522584447334153999246950400) }, { argument := 5226897723868831152791879680, coefficient := (-5226897723868831152791879680) }, { argument := 187834916419526328865259520, coefficient := (-187834916419526328865259520) }, { argument := 16469172530603354769850368, coefficient := (-16469172530603354769850368) }, { argument := 490689641321329831662583808, coefficient := (-490689641321329831662583808) }, { argument := 5226897723868831152791879680, coefficient := (-5226897723868831152791879680) }, { argument := 492060304608117442798944256, coefficient := (-492060304608117442798944256) }, { argument := 17682784525774248040464384, coefficient := (-17682784525774248040464384) }, { argument := 591839712427912621719552, coefficient := (-591839712427912621719552) }, { argument := 17633528076248294948339712, coefficient := (-17633528076248294948339712) }, { argument := 187834916419526328865259520, coefficient := (-187834916419526328865259520) }, { argument := 17682784525774248040464384, coefficient := (-17682784525774248040464384) }, { argument := 635452333091538207768576, coefficient := (-635452333091538207768576) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 417957767932860819283378176, coefficient := 417957767932860819283378176 }, { argument := 12452814302196494253483360256, coefficient := 12452814302196494253483360256 }, { argument := 132649196662555871408826613760, coefficient := 132649196662555871408826613760 }, { argument := 12487599253709312060127444992, coefficient := 12487599253709312060127444992 }, { argument := 448757042134136645367103488, coefficient := 448757042134136645367103488 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7
