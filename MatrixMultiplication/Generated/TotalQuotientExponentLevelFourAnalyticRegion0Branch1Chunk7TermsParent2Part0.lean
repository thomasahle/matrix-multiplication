import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    7, 1, 25156267, 25175381, 9314629, 7924185,
    9320279, 237277, 8151335, 8151323, 237281
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 158456325028528675187087900672, 475188448459678884764034531328, 475549501711493166358492872704, 175948367159862402108815835136, 598734490368934392923066204160,
    176055092642375256090645364736, 2241017903911721614740291584, 76987182389284478935965368320, 76987069052488890064480239616, 2241055682843584571902001152
  ]
def positiveScales : Array ℕ := #[
    2, 0, 24, 24, 23, 22,
    23, 17, 22, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    237277, 8151335, 8151323, 237281, 78107271584065, 66447550753877,
    78154650613099, 78107271584065, 78166271108799, 237277, 78166271108799, 66498212615083,
    78213683350165, 66447550753877, 66498212615083, 8151335, 78154650613099, 78213683350165,
    8151323, 237281, 1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1120508951955860807370145792, 38493591194642239467982684160, 38493534526244445032240119808, 1120527841421792285951000576, 43970484900115158104570593280, 149626582407421288883993706496,
    43997156922302995393452965888, 43970484900115158104570593280, 44003698679816042949837324288, 1120508951955860807370145792, 44003698679816042949837324288, 149740662777045907577539395584,
    44030389398884632651869716480, 149626582407421288883993706496, 149740662777045907577539395584, 38493591194642239467982684160, 43997156922302995393452965888, 44030389398884632651869716480,
    38493534526244445032240119808, 1120527841421792285951000576, 158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    17, 22, 22, 17, 46, 45,
    46, 46, 46, 17, 46, 45,
    46, 45, 45, 22, 46, 46,
    22, 17, 0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 0, 24584414517264853, 24585510276113719, 23151066877351067, 22917831131092893,
    23151941711531176, 17856212736693376, 22958604927329878, 22958602803462681, 17856237057346070
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    17856212738763286, 22958604940118775, 22958602816251124, 17856237059416933, 46150522099315608, 45917281262442673,
    46151396957263892, 46150522099315608, 46151611449749802, 17856212738763286, 46151611449749802, 45918380802966471,
    46152486260179676, 45917281262442673, 45918380802966471, 22958604940118775, 46151396957263892, 46152486260179676,
    22958602816251124, 17856237059416933, 0, 1584962500724866, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 625613441 / 1000000000000
noncomputable def negativeCeiling : ℝ := 606269667 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1120508951955860807370145792, coefficient := (-1120508951955860807370145792) }, { argument := 38493591194642239467982684160, coefficient := (-38493591194642239467982684160) }, { argument := 38493534526244445032240119808, coefficient := (-38493534526244445032240119808) }, { argument := 1120527841421792285951000576, coefficient := (-1120527841421792285951000576) }, { argument := 43970484900115158104570593280, coefficient := (-43970484900115158104570593280) }, { argument := 149626582407421288883993706496, coefficient := (-149626582407421288883993706496) }, { argument := 43997156922302995393452965888, coefficient := (-43997156922302995393452965888) }, { argument := 43970484900115158104570593280, coefficient := (-43970484900115158104570593280) }, { argument := 44003698679816042949837324288, coefficient := (-44003698679816042949837324288) }, { argument := 1120508951955860807370145792, coefficient := (-1120508951955860807370145792) }, { argument := 44003698679816042949837324288, coefficient := (-44003698679816042949837324288) }, { argument := 149740662777045907577539395584, coefficient := (-149740662777045907577539395584) }, { argument := 44030389398884632651869716480, coefficient := (-44030389398884632651869716480) }, { argument := 149626582407421288883993706496, coefficient := (-149626582407421288883993706496) }, { argument := 149740662777045907577539395584, coefficient := (-149740662777045907577539395584) }, { argument := 38493591194642239467982684160, coefficient := (-38493591194642239467982684160) }, { argument := 43997156922302995393452965888, coefficient := (-43997156922302995393452965888) }, { argument := 44030389398884632651869716480, coefficient := (-44030389398884632651869716480) }, { argument := 38493534526244445032240119808, coefficient := (-38493534526244445032240119808) }, { argument := 1120527841421792285951000576, coefficient := (-1120527841421792285951000576) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475188448459678884764034531328, coefficient := 475188448459678884764034531328 }, { argument := 475549501711493166358492872704, coefficient := 475549501711493166358492872704 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 175948367159862402108815835136, coefficient := 175948367159862402108815835136 }, { argument := 598734490368934392923066204160, coefficient := 598734490368934392923066204160 }, { argument := 176055092642375256090645364736, coefficient := 176055092642375256090645364736 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2241017903911721614740291584, coefficient := 2241017903911721614740291584 }, { argument := 76987182389284478935965368320, coefficient := 76987182389284478935965368320 }, { argument := 76987069052488890064480239616, coefficient := 76987069052488890064480239616 }, { argument := 2241055682843584571902001152, coefficient := 2241055682843584571902001152 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7
