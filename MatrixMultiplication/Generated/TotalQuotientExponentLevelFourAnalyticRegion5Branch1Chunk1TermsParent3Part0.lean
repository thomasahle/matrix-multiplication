import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1

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
def constantNumerator : ℤ := 1053516499325823538318417068032
def positiveArguments : Array ℕ := #[
    1, 16777249, 16777183, 6202817, 42291361, 12411869,
    51013, 31971, 8184503, 204085
  ]
def positiveCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456636704716544583672004608, 158456013352340805790503796736, 117167900400696176461928726528, 399430611402680963348679360512, 117226788310737560937743515648,
    3854433302250067380580384768, 154602269515597237378124611584, 154600890584584239441722212352, 3855056654625806173748592640
  ]
def positiveScales : Array ℕ := #[
    0, 24, 23, 22, 25, 23,
    15, 14, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    3423433065469, 137314667658319, 68656721461031, 1711993356467, 19237465551133, 32790697999095,
    19247139068149, 3423433065469, 3423415892995, 3423415892995, 137314131182513, 68656453222617,
    1711984770893, 32790697999095, 223569910591623, 65614342625675, 137314667658319, 137314131182513,
    19247139068149, 65614342625675, 150443921051, 68656721461031, 68656453222617, 1711993356467,
    1711984770893, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    963610742373376452317937664, 38650642881156809184734347264, 38650298148547393413732892672, 963766580280693241050824704, 10829730335954416533027946496, 36919043822485677695859425280,
    10835176041907994002076991488, 963610742373376452317937664, 963605908751657237972254720, 963605908751657237972254720, 38650491876641809504327958528, 38650147143744726307128213504,
    963761747032209845823471616, 36919043822485677695859425280, 125858670753961056214896869376, 36937591124893747763583385600, 38650642881156809184734347264, 38650491876641809504327958528,
    10835176041907994002076991488, 36937591124893747763583385600, 10840626988567038703211380736, 38650298148547393413732892672, 38650147143744726307128213504, 963766580280693241050824704,
    963761747032209845823471616, 316912650057057350374175801344, 633825300114114700748351602688, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    41, 46, 45, 40, 44, 44,
    44, 41, 41, 41, 46, 45,
    40, 44, 47, 45, 46, 46,
    44, 45, 37, 45, 45, 40,
    40, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 24000002837710948, 23999997160823954, 22564492131427490, 25333859653435095, 23565217039470750,
    15638577325565731, 14964476248668600, 22964463380902912, 17638810624367123
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41638580943978776, 46964479081013518, 45964466213275323, 40638814241915831, 44128983976632194, 44898351849757541,
    44129709250307677, 41638580943978776, 41638573707177368, 41638573707177368, 46964473444524127, 45964460576724921,
    40638807006843306, 44898351849757541, 47667719362964335, 45899076445559617, 46964479081013518, 46964473444524127,
    44129709250307677, 45899076445559617, 37130434857000806, 45964466213275323, 45964460576724921, 40638814241915831,
    40638807006843306, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 43820137 / 125000000000
noncomputable def negativeCeiling : ℝ := 351798249 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 963610742373376452317937664, coefficient := (-963610742373376452317937664) }, { argument := 38650642881156809184734347264, coefficient := (-38650642881156809184734347264) }, { argument := 38650298148547393413732892672, coefficient := (-38650298148547393413732892672) }, { argument := 963766580280693241050824704, coefficient := (-963766580280693241050824704) }, { argument := 10829730335954416533027946496, coefficient := (-10829730335954416533027946496) }, { argument := 36919043822485677695859425280, coefficient := (-36919043822485677695859425280) }, { argument := 10835176041907994002076991488, coefficient := (-10835176041907994002076991488) }, { argument := 963610742373376452317937664, coefficient := (-963610742373376452317937664) }, { argument := 963605908751657237972254720, coefficient := (-963605908751657237972254720) }, { argument := 963605908751657237972254720, coefficient := (-963605908751657237972254720) }, { argument := 38650491876641809504327958528, coefficient := (-38650491876641809504327958528) }, { argument := 38650147143744726307128213504, coefficient := (-38650147143744726307128213504) }, { argument := 963761747032209845823471616, coefficient := (-963761747032209845823471616) }, { argument := 36919043822485677695859425280, coefficient := (-36919043822485677695859425280) }, { argument := 125858670753961056214896869376, coefficient := (-125858670753961056214896869376) }, { argument := 36937591124893747763583385600, coefficient := (-36937591124893747763583385600) }, { argument := 38650642881156809184734347264, coefficient := (-38650642881156809184734347264) }, { argument := 38650491876641809504327958528, coefficient := (-38650491876641809504327958528) }, { argument := 10835176041907994002076991488, coefficient := (-10835176041907994002076991488) }, { argument := 36937591124893747763583385600, coefficient := (-36937591124893747763583385600) }, { argument := 10840626988567038703211380736, coefficient := (-10840626988567038703211380736) }, { argument := 38650298148547393413732892672, coefficient := (-38650298148547393413732892672) }, { argument := 38650147143744726307128213504, coefficient := (-38650147143744726307128213504) }, { argument := 963766580280693241050824704, coefficient := (-963766580280693241050824704) }, { argument := 963761747032209845823471616, coefficient := (-963761747032209845823471616) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 158456636704716544583672004608, coefficient := 158456636704716544583672004608 }, { argument := 158456013352340805790503796736, coefficient := 158456013352340805790503796736 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 117167900400696176461928726528, coefficient := 117167900400696176461928726528 }, { argument := 399430611402680963348679360512, coefficient := 399430611402680963348679360512 }, { argument := 117226788310737560937743515648, coefficient := 117226788310737560937743515648 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 3854433302250067380580384768, coefficient := 3854433302250067380580384768 }, { argument := 154602269515597237378124611584, coefficient := 154602269515597237378124611584 }, { argument := 154600890584584239441722212352, coefficient := 154600890584584239441722212352 }, { argument := 3855056654625806173748592640, coefficient := 3855056654625806173748592640 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1
