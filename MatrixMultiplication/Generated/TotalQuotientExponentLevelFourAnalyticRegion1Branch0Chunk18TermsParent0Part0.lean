import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 18, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    257, 265, 491, 529, 1967, 2333,
    4675, 18563, 22805, 26915, 29105, 29239,
    30983, 31131, 90743
  ]
def positiveCoefficients : Array ℕ := #[
    224453384402910868402510011301888, 843225333639315345008088263426048, 3248354663084837841335301963776, 840452347951316093192314225164288, 3327582825599102178928845914112, 24402274054393415978811536703488,
    24560730379421944653998624604160, 1242456044548693342141956229169152, 881017167158619434040208727736320, 4264851988142849292660470846586880, 180560982370008425375686662815744, 181749404807722390439589822070784,
    419592348675543931895408760979456, 420939227438286425634499008135168, 882364045921361927779298974892032
  ]
def positiveScales : Array ℕ := #[
    8, 8, 8, 9, 10, 11,
    12, 14, 14, 14, 14, 14,
    14, 14, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 21, 33, 39, 41,
    53, 111, 171, 189, 465, 695,
    937, 1147, 1235, 1359, 1647, 2279,
    2975, 6611, 11137, 439843118517
  ]
def negativeCoefficients : Array ℕ := #[
    15687176177824338843521702166528, 1426106925256758076683791106048, 3327582825599102178928845914112, 2614529362970723140586950361088, 98876746817801893316742850019328, 3248354663084837841335301963776,
    8398185226512019784915658735616, 8794326039083341472883378487296, 108384126319513613827968124059648, 14974122715195959805179806613504, 73682191138265833961995873812480, 881017167158619434040208727736320,
    74236788275865684325150681464832, 181749404807722390439589822070784, 97846780705116456928026778664960, 107671072856885234789626228506624, 521955134643973456066267544813568, 180560982370008425375686662815744,
    471407566959872808681586504499200, 523777382381801535830919055671296, 882364045921361927779298974892032, 2132425994071424646330235423293440
  ]
def negativeScales : Array ℕ := #[
    1, 3, 4, 5, 5, 5,
    5, 6, 7, 7, 8, 9,
    9, 10, 10, 10, 10, 11,
    11, 12, 13, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8005624549193878, 8049848549450561, 8939579213775465, 9047123912114025, 10941781241718677, 11187970591984199,
    12190750649662361, 14180142265411970, 14477062549745108, 14716122804900257, 14828979397063870, 14835606350139134,
    14919189222315806, 14926064299387892, 16469498736103625
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 4392317422778766, 5044394119358454, 5285402218862249, 5357552004618085,
    5727920454700926, 6794415866926375, 7417852514885912, 7562242424222992, 8861086908132560, 9440869167610903,
    9871905240275299, 10163649676015826, 10270295326472041, 10408329740767401, 10685624839777780, 11154185209265298,
    11538673953083609, 12690652799406491, 13443073042388688, 38678198084607632
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 22
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
noncomputable def positiveFloor : ℝ := 857099258161 / 500000000000
noncomputable def negativeCeiling : ℝ := 311317977041 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-15687176177824338843521702166528) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 21, coefficient := (-3327582825599102178928845914112) }, { argument := 33, coefficient := (-2614529362970723140586950361088) }, { argument := 39, coefficient := (-98876746817801893316742850019328) }, { argument := 41, coefficient := (-3248354663084837841335301963776) }, { argument := 53, coefficient := (-8398185226512019784915658735616) }, { argument := 111, coefficient := (-8794326039083341472883378487296) }, { argument := 171, coefficient := (-108384126319513613827968124059648) }, { argument := 189, coefficient := (-14974122715195959805179806613504) }, { argument := 257, coefficient := 224453384402910868402510011301888 }, { argument := 265, coefficient := 843225333639315345008088263426048 }, { argument := 465, coefficient := (-73682191138265833961995873812480) }, { argument := 491, coefficient := 3248354663084837841335301963776 }, { argument := 529, coefficient := 840452347951316093192314225164288 }, { argument := 695, coefficient := (-881017167158619434040208727736320) }, { argument := 937, coefficient := (-74236788275865684325150681464832) }, { argument := 1147, coefficient := (-181749404807722390439589822070784) }, { argument := 1235, coefficient := (-97846780705116456928026778664960) }, { argument := 1359, coefficient := (-107671072856885234789626228506624) }, { argument := 1647, coefficient := (-521955134643973456066267544813568) }, { argument := 1967, coefficient := 3327582825599102178928845914112 }, { argument := 2279, coefficient := (-180560982370008425375686662815744) }, { argument := 2333, coefficient := 24402274054393415978811536703488 }, { argument := 2975, coefficient := (-471407566959872808681586504499200) }, { argument := 4675, coefficient := 24560730379421944653998624604160 }, { argument := 6611, coefficient := (-523777382381801535830919055671296) }, { argument := 11137, coefficient := (-882364045921361927779298974892032) }, { argument := 18563, coefficient := 1242456044548693342141956229169152 }, { argument := 22805, coefficient := 881017167158619434040208727736320 }, { argument := 26915, coefficient := 4264851988142849292660470846586880 }, { argument := 29105, coefficient := 180560982370008425375686662815744 }, { argument := 29239, coefficient := 181749404807722390439589822070784 }, { argument := 30983, coefficient := 419592348675543931895408760979456 }, { argument := 31131, coefficient := 420939227438286425634499008135168 }, { argument := 90743, coefficient := 882364045921361927779298974892032 }, { argument := 439843118517, coefficient := (-2132425994071424646330235423293440) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk18
