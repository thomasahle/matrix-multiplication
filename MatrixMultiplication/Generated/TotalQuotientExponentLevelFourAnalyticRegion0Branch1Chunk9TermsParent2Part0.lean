import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 475368975085586025561263702016
def positiveArguments : Array ℕ := #[
    3, 4587301, 31974375, 9182671, 574377, 24594549,
    24588407, 574315
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 86651665956937625433731497984, 301989433621410224359342080000, 86727875507238175768190124032, 5424837386662436417814134784, 232288947717790299641723486208,
    232230938167914728919918444544, 5424251813218560581807636480
  ]
def positiveScales : Array ℕ := #[
    1, 22, 24, 23, 19, 24,
    24, 19
  ]
def negativeArguments : Array ℕ := #[
    877932624265, 37607888322467, 37598481154287, 877837632997, 877932624265, 6123363546303,
    1757218199599, 6123363546303, 262130160320817, 262064768378809, 6122703594071, 37607888322467,
    262130160320817, 75282124029833, 1757218199599, 75282124029833, 75263284647529, 1757027946975,
    37598481154287, 262064768378809, 75263284647529, 877837632997, 6122703594071, 1757027946975,
    3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    494232129937031959339335680, 21171358979406701138966216704, 21166063214517943690585964544, 494178654607135927974232064, 494232129937031959339335680, 1723573611586516858089504768,
    494612951807669391478226944, 1723573611586516858089504768, 73783080771462488588342525952, 73764674576108722220594888704, 1723387851547384512644120576, 21171358979406701138966216704,
    73783080771462488588342525952, 21190034108025960093553000448, 494612951807669391478226944, 21190034108025960093553000448, 21184731293330698548778369024, 494559400454759850285465600,
    21166063214517943690585964544, 73764674576108722220594888704, 21184731293330698548778369024, 494178654607135927974232064, 1723387851547384512644120576, 494559400454759850285465600,
    475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    39, 45, 45, 39, 39, 42,
    40, 42, 47, 47, 42, 45,
    47, 46, 40, 46, 46, 40,
    45, 47, 46, 39, 42, 40,
    1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 22129214143620023, 24930412822913595, 23130482426445543, 19131638454359803, 24551835264244063,
    24551474934824774, 19131482717064476
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39675319270157910, 45096100535068579, 45095739616836591, 39675163163821136, 39675319270157910, 42477461477608087,
    40676430485376715, 42477461477608087, 47897276690223970, 47896916745353044, 42477305981185873, 45096100535068579,
    47897276690223970, 46097372566757282, 40676430485376715, 46097372566757282, 46097011486551594, 40676274277469667,
    45095739616836591, 47896916745353044, 46097011486551594, 39675163163821136, 42477305981185873, 40676274277469667,
    1584962500724866, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 143349651 / 500000000000
noncomputable def negativeCeiling : ℝ := 286699303 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 494232129937031959339335680, coefficient := (-494232129937031959339335680) }, { argument := 21171358979406701138966216704, coefficient := (-21171358979406701138966216704) }, { argument := 21166063214517943690585964544, coefficient := (-21166063214517943690585964544) }, { argument := 494178654607135927974232064, coefficient := (-494178654607135927974232064) }, { argument := 494232129937031959339335680, coefficient := (-494232129937031959339335680) }, { argument := 1723573611586516858089504768, coefficient := (-1723573611586516858089504768) }, { argument := 494612951807669391478226944, coefficient := (-494612951807669391478226944) }, { argument := 1723573611586516858089504768, coefficient := (-1723573611586516858089504768) }, { argument := 73783080771462488588342525952, coefficient := (-73783080771462488588342525952) }, { argument := 73764674576108722220594888704, coefficient := (-73764674576108722220594888704) }, { argument := 1723387851547384512644120576, coefficient := (-1723387851547384512644120576) }, { argument := 21171358979406701138966216704, coefficient := (-21171358979406701138966216704) }, { argument := 73783080771462488588342525952, coefficient := (-73783080771462488588342525952) }, { argument := 21190034108025960093553000448, coefficient := (-21190034108025960093553000448) }, { argument := 494612951807669391478226944, coefficient := (-494612951807669391478226944) }, { argument := 21190034108025960093553000448, coefficient := (-21190034108025960093553000448) }, { argument := 21184731293330698548778369024, coefficient := (-21184731293330698548778369024) }, { argument := 494559400454759850285465600, coefficient := (-494559400454759850285465600) }, { argument := 21166063214517943690585964544, coefficient := (-21166063214517943690585964544) }, { argument := 73764674576108722220594888704, coefficient := (-73764674576108722220594888704) }, { argument := 21184731293330698548778369024, coefficient := (-21184731293330698548778369024) }, { argument := 494178654607135927974232064, coefficient := (-494178654607135927974232064) }, { argument := 1723387851547384512644120576, coefficient := (-1723387851547384512644120576) }, { argument := 494559400454759850285465600, coefficient := (-494559400454759850285465600) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 86651665956937625433731497984, coefficient := 86651665956937625433731497984 }, { argument := 301989433621410224359342080000, coefficient := 301989433621410224359342080000 }, { argument := 86727875507238175768190124032, coefficient := 86727875507238175768190124032 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 5424837386662436417814134784, coefficient := 5424837386662436417814134784 }, { argument := 232288947717790299641723486208, coefficient := 232288947717790299641723486208 }, { argument := 232230938167914728919918444544, coefficient := 232230938167914728919918444544 }, { argument := 5424251813218560581807636480, coefficient := 5424251813218560581807636480 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9
