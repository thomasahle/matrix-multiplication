import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 3, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3

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
def constantNumerator : ℤ := 375273396609371034501857148928
def positiveArguments : Array ℕ := #[
    13, 25165841, 25165807, 22273057, 36464227, 22239001,
    686545, 24479295, 12239217, 343687
  ]
def positiveCoefficients : Array ℕ := #[
    1029966112685436388716071354368, 237684648103253430348569116672, 237684326982332595212694585344, 210363075695690262828856377344, 688789773634201417926697811968, 210041425869809045554061115392,
    6484234193963481146473840640, 231200404464556983462804848640, 231192272549473481933746864128, 6492063877592079018238148608
  ]
def positiveScales : Array ℕ := #[
    3, 24, 24, 24, 25, 24,
    19, 24, 23, 18
  ]
def negativeArguments : Array ℕ := #[
    5759161209547, 205347348147941, 102670062766315, 2883057694269, 8860528616405, 232020525297449,
    70775134040623, 5759161209547, 5759152549173, 5759152549173, 205347071594779, 102669924513557,
    2883053341123, 232020525297449, 379924375947069, 231667148112477, 205347348147941, 205347071594779,
    70775134040623, 231667148112477, 17666560312029, 102670062766315, 102669924513557, 2883057694269,
    2883053341123, 3, 7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1621059767330155264403832832, 57800140037536662469839159296, 57798107052060208717396705280, 1623017194699688722644860928, 19952136687573587245599293440, 65307971954493628562007916544,
    19921429205777915606820978688, 1621059767330155264403832832, 1621057329651585308833087488, 1621057329651585308833087488, 57800062194741829261563265024, 57798029222676532249476726784,
    1623014744096350786474213376, 65307971954493628562007916544, 213878409743023522716768534528, 65208505119583557684572454912, 57800140037536662469839159296, 57800062194741829261563265024,
    19921429205777915606820978688, 65208505119583557684572454912, 19890778609543049485637124096, 57798107052060208717396705280, 57798029222676532249476726784, 1623017194699688722644860928,
    1623014744096350786474213376, 475368975085586025561263702016, 1109194275199700726309615304704, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    42, 47, 46, 41, 43, 47,
    46, 42, 42, 42, 47, 46,
    41, 47, 48, 47, 47, 47,
    46, 47, 44, 46, 46, 41,
    41, 1, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3700439718136550, 24584963475288950, 24584961526152240, 24408796247306513, 25119978475135011, 24406588646305479,
    19388994760212161, 24545058673440973, 23545007929239569, 18390735757074478
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    42388995844943333, 47545059644922984, 46545008900588371, 41390736846241817, 43010529910737488, 47721245765079768,
    46008307809981237, 42388995844943333, 42388993675480184, 42388993675480184, 47545057701960741, 46545006957892543,
    41390734667906330, 47721245765079768, 48432705606706028, 47719046803832353, 47545059644922984, 47545057701960741,
    46008307809981237, 47719046803832353, 44006086407333588, 46545008900588371, 46545006957892543, 41390736846241817,
    41390734667906330, 1584962500724866, 2807354922807594, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 32755923 / 50000000000
noncomputable def negativeCeiling : ℝ := 80196101 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1621059767330155264403832832, coefficient := (-1621059767330155264403832832) }, { argument := 57800140037536662469839159296, coefficient := (-57800140037536662469839159296) }, { argument := 57798107052060208717396705280, coefficient := (-57798107052060208717396705280) }, { argument := 1623017194699688722644860928, coefficient := (-1623017194699688722644860928) }, { argument := 19952136687573587245599293440, coefficient := (-19952136687573587245599293440) }, { argument := 65307971954493628562007916544, coefficient := (-65307971954493628562007916544) }, { argument := 19921429205777915606820978688, coefficient := (-19921429205777915606820978688) }, { argument := 1621059767330155264403832832, coefficient := (-1621059767330155264403832832) }, { argument := 1621057329651585308833087488, coefficient := (-1621057329651585308833087488) }, { argument := 1621057329651585308833087488, coefficient := (-1621057329651585308833087488) }, { argument := 57800062194741829261563265024, coefficient := (-57800062194741829261563265024) }, { argument := 57798029222676532249476726784, coefficient := (-57798029222676532249476726784) }, { argument := 1623014744096350786474213376, coefficient := (-1623014744096350786474213376) }, { argument := 65307971954493628562007916544, coefficient := (-65307971954493628562007916544) }, { argument := 213878409743023522716768534528, coefficient := (-213878409743023522716768534528) }, { argument := 65208505119583557684572454912, coefficient := (-65208505119583557684572454912) }, { argument := 57800140037536662469839159296, coefficient := (-57800140037536662469839159296) }, { argument := 57800062194741829261563265024, coefficient := (-57800062194741829261563265024) }, { argument := 19921429205777915606820978688, coefficient := (-19921429205777915606820978688) }, { argument := 65208505119583557684572454912, coefficient := (-65208505119583557684572454912) }, { argument := 19890778609543049485637124096, coefficient := (-19890778609543049485637124096) }, { argument := 57798107052060208717396705280, coefficient := (-57798107052060208717396705280) }, { argument := 57798029222676532249476726784, coefficient := (-57798029222676532249476726784) }, { argument := 1623017194699688722644860928, coefficient := (-1623017194699688722644860928) }, { argument := 1623014744096350786474213376, coefficient := (-1623014744096350786474213376) }, { argument := 1029966112685436388716071354368, coefficient := 1029966112685436388716071354368 }, { argument := 237684648103253430348569116672, coefficient := 237684648103253430348569116672 }, { argument := 237684326982332595212694585344, coefficient := 237684326982332595212694585344 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 210363075695690262828856377344, coefficient := 210363075695690262828856377344 }, { argument := 688789773634201417926697811968, coefficient := 688789773634201417926697811968 }, { argument := 210041425869809045554061115392, coefficient := 210041425869809045554061115392 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 6484234193963481146473840640, coefficient := 6484234193963481146473840640 }, { argument := 231200404464556983462804848640, coefficient := 231200404464556983462804848640 }, { argument := 231192272549473481933746864128, coefficient := 231192272549473481933746864128 }, { argument := 6492063877592079018238148608, coefficient := 6492063877592079018238148608 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3
