import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 2, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2

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
def constantNumerator : ℤ := 204280366988843894212722163712
def positiveArguments : Array ℕ := #[
    1, 8386807, 8390409, 3020639, 42939875, 12086433,
    407831, 4092347, 8184677, 407859
  ]
def positiveCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158422305100386082262968434688, 158490344956671268111207366656, 114116514963591057989227773952, 405555652957224413540909056000, 114153132193299229218214772736,
    3851854890150420554293706752, 154604498472577151850665476096, 154604177351656316714790944768, 3852119342673461254425673728
  ]
def positiveScales : Array ℕ := #[
    0, 22, 23, 21, 25, 23,
    18, 21, 22, 18
  ]
def negativeArguments : Array ℕ := #[
    1710259924189, 68643388927039, 68643246423111, 1710377314973, 4562112380705, 64853055127541,
    18254321271687, 1710259924189, 1710874465059, 1710874465059, 68672990204865, 68672847496121,
    1710991955299, 64853055127541, 115239453599543, 64873816617373, 68643388927039, 68672990204865,
    18254321271687, 64873816617373, 4565052666551, 68643246423111, 68672847496121, 1710377314973,
    1710991955299, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    962790744660534142296915968, 38642792599157608954795655168, 38642712376577979000796741632, 962856829796919033594904576, 10272963808882682192818339840, 36509024363278985317467553792,
    10276269309633861484327993344, 962790744660534142296915968, 963136700414676134849937408, 963136700414676134849937408, 38659456637130966970537082880, 38659376299250179356598730752,
    963202841539811593617932288, 36509024363278985317467553792, 129748090072320354692819320832, 36520712043012866760167653376, 38642792599157608954795655168, 38659456637130966970537082880,
    10276269309633861484327993344, 36520712043012866760167653376, 10279584744002886364611739648, 38642712376577979000796741632, 38659376299250179356598730752, 962856829796919033594904576,
    963202841539811593617932288, 316912650057057350374175801344, 633825300114114700748351602688, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    40, 45, 45, 40, 42, 45,
    44, 40, 40, 40, 45, 45,
    40, 45, 46, 45, 45, 45,
    44, 45, 42, 45, 45, 40,
    40, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 22999690224538594, 23000309707508922, 21526422345568076, 25355814655661072, 23526885197259679,
    18637611915917047, 21964497048375919, 22964494051826405, 18637710962028093
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40637352740290448, 45964186027266568, 45964183032222588, 40637451762250520, 42052839124335850, 45882239775920381,
    44053303261323835, 40637352740290448, 40637871045024838, 40637871045024838, 45964808030658688, 45964805032602885,
    40637970115278269, 45882239775920381, 46711628053698904, 45882701553808329, 45964186027266568, 45964808030658688,
    44053303261323835, 45882701553808329, 42053768643180661, 45964183032222588, 45964805032602885, 40637451762250520,
    40637970115278269, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 358754691 / 1000000000000
noncomputable def negativeCeiling : ℝ := 69953907 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 962790744660534142296915968, coefficient := (-962790744660534142296915968) }, { argument := 38642792599157608954795655168, coefficient := (-38642792599157608954795655168) }, { argument := 38642712376577979000796741632, coefficient := (-38642712376577979000796741632) }, { argument := 962856829796919033594904576, coefficient := (-962856829796919033594904576) }, { argument := 10272963808882682192818339840, coefficient := (-10272963808882682192818339840) }, { argument := 36509024363278985317467553792, coefficient := (-36509024363278985317467553792) }, { argument := 10276269309633861484327993344, coefficient := (-10276269309633861484327993344) }, { argument := 962790744660534142296915968, coefficient := (-962790744660534142296915968) }, { argument := 963136700414676134849937408, coefficient := (-963136700414676134849937408) }, { argument := 963136700414676134849937408, coefficient := (-963136700414676134849937408) }, { argument := 38659456637130966970537082880, coefficient := (-38659456637130966970537082880) }, { argument := 38659376299250179356598730752, coefficient := (-38659376299250179356598730752) }, { argument := 963202841539811593617932288, coefficient := (-963202841539811593617932288) }, { argument := 36509024363278985317467553792, coefficient := (-36509024363278985317467553792) }, { argument := 129748090072320354692819320832, coefficient := (-129748090072320354692819320832) }, { argument := 36520712043012866760167653376, coefficient := (-36520712043012866760167653376) }, { argument := 38642792599157608954795655168, coefficient := (-38642792599157608954795655168) }, { argument := 38659456637130966970537082880, coefficient := (-38659456637130966970537082880) }, { argument := 10276269309633861484327993344, coefficient := (-10276269309633861484327993344) }, { argument := 36520712043012866760167653376, coefficient := (-36520712043012866760167653376) }, { argument := 10279584744002886364611739648, coefficient := (-10279584744002886364611739648) }, { argument := 38642712376577979000796741632, coefficient := (-38642712376577979000796741632) }, { argument := 38659376299250179356598730752, coefficient := (-38659376299250179356598730752) }, { argument := 962856829796919033594904576, coefficient := (-962856829796919033594904576) }, { argument := 963202841539811593617932288, coefficient := (-963202841539811593617932288) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 158422305100386082262968434688, coefficient := 158422305100386082262968434688 }, { argument := 158490344956671268111207366656, coefficient := 158490344956671268111207366656 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 114116514963591057989227773952, coefficient := 114116514963591057989227773952 }, { argument := 405555652957224413540909056000, coefficient := 405555652957224413540909056000 }, { argument := 114153132193299229218214772736, coefficient := 114153132193299229218214772736 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 3851854890150420554293706752, coefficient := 3851854890150420554293706752 }, { argument := 154604498472577151850665476096, coefficient := 154604498472577151850665476096 }, { argument := 154604177351656316714790944768, coefficient := 154604177351656316714790944768 }, { argument := 3852119342673461254425673728, coefficient := 3852119342673461254425673728 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2
