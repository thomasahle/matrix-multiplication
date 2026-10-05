import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8

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
def constantNumerator : ℤ := (-2465939010262682229735948288)
def positiveArguments : Array ℕ := #[
    1, 1517265, 10706119, 3036567, 201239, 16374759,
    16374727, 100617
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 57320651053049697961267691520, 202232870108855532582439223296, 57359128895152119830468886528, 3801297234584818132635877376, 154655226133336137579550998528,
    154654923901881233922257321984, 3801202787255160739731603456
  ]
def positiveScales : Array ℕ := #[
    0, 20, 23, 21, 17, 23,
    23, 16
  ]
def negativeArguments : Array ℕ := #[
    304954287707, 24845606293883, 24845556858459, 152473385181, 304954287707, 1078028702825,
    76283023695, 1078028702825, 87653489729251, 87653320260563, 269500448655, 24845606293883,
    87653489729251, 12431169161169, 76283023695, 12431169161169, 12431144395497, 152562288645,
    24845556858459, 87653320260563, 12431144395497, 152473385181, 269500448655, 152562288645,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    343348004120570057266823168, 13986832905865691116387434496, 13986805076196052953578078208, 343339540342534853401509888, 343348004120570057266823168, 1213752416084342292139212800,
    343548197087496716911902720, 1213752416084342292139212800, 49344527960297300240013197312, 49344432557907284269157318656, 1213722120138839489909882880, 13986832905865691116387434496,
    49344527960297300240013197312, 13996252200505077433374867456, 343548197087496716911902720, 13996252200505077433374867456, 13996224316837279738393264128, 343539733146206026554408960,
    13986805076196052953578078208, 49344432557907284269157318656, 13996224316837279738393264128, 343339540342534853401509888, 1213722120138839489909882880, 343539733146206026554408960,
    316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    38, 44, 44, 37, 38, 39,
    36, 39, 46, 46, 37, 44,
    46, 43, 36, 43, 43, 37,
    44, 46, 43, 37, 37, 37,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 20533041652797724, 23351932257822002, 21534009771050015, 17618550400127233, 23964970336932094,
    23964967517575438, 16618514554367619
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38149802044334860, 44498055981159784, 44498053110619570, 37149766480414420, 38149802044334860, 39971532744348856,
    36150642978986341, 39971532744348856, 46316876763366641, 46316873974066719, 37971496733407915, 44498055981159784,
    46316876763366641, 43499027222902902, 36150642978986341, 43499027222902902, 43499024348728534, 37150607435104431,
    44498053110619570, 46316873974066719, 43499024348728534, 37149766480414420, 37971496733407915, 37150607435104431,
    0, 0
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
noncomputable def positiveFloor : ℝ := 17667301 / 100000000000
noncomputable def negativeCeiling : ℝ := 172828631 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 343348004120570057266823168, coefficient := (-343348004120570057266823168) }, { argument := 13986832905865691116387434496, coefficient := (-13986832905865691116387434496) }, { argument := 13986805076196052953578078208, coefficient := (-13986805076196052953578078208) }, { argument := 343339540342534853401509888, coefficient := (-343339540342534853401509888) }, { argument := 343348004120570057266823168, coefficient := (-343348004120570057266823168) }, { argument := 1213752416084342292139212800, coefficient := (-1213752416084342292139212800) }, { argument := 343548197087496716911902720, coefficient := (-343548197087496716911902720) }, { argument := 1213752416084342292139212800, coefficient := (-1213752416084342292139212800) }, { argument := 49344527960297300240013197312, coefficient := (-49344527960297300240013197312) }, { argument := 49344432557907284269157318656, coefficient := (-49344432557907284269157318656) }, { argument := 1213722120138839489909882880, coefficient := (-1213722120138839489909882880) }, { argument := 13986832905865691116387434496, coefficient := (-13986832905865691116387434496) }, { argument := 49344527960297300240013197312, coefficient := (-49344527960297300240013197312) }, { argument := 13996252200505077433374867456, coefficient := (-13996252200505077433374867456) }, { argument := 343548197087496716911902720, coefficient := (-343548197087496716911902720) }, { argument := 13996252200505077433374867456, coefficient := (-13996252200505077433374867456) }, { argument := 13996224316837279738393264128, coefficient := (-13996224316837279738393264128) }, { argument := 343539733146206026554408960, coefficient := (-343539733146206026554408960) }, { argument := 13986805076196052953578078208, coefficient := (-13986805076196052953578078208) }, { argument := 49344432557907284269157318656, coefficient := (-49344432557907284269157318656) }, { argument := 13996224316837279738393264128, coefficient := (-13996224316837279738393264128) }, { argument := 343339540342534853401509888, coefficient := (-343339540342534853401509888) }, { argument := 1213722120138839489909882880, coefficient := (-1213722120138839489909882880) }, { argument := 343539733146206026554408960, coefficient := (-343539733146206026554408960) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 57320651053049697961267691520, coefficient := 57320651053049697961267691520 }, { argument := 202232870108855532582439223296, coefficient := 202232870108855532582439223296 }, { argument := 57359128895152119830468886528, coefficient := 57359128895152119830468886528 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 3801297234584818132635877376, coefficient := 3801297234584818132635877376 }, { argument := 154655226133336137579550998528, coefficient := 154655226133336137579550998528 }, { argument := 154654923901881233922257321984, coefficient := 154654923901881233922257321984 }, { argument := 3801202787255160739731603456, coefficient := 3801202787255160739731603456 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk8
