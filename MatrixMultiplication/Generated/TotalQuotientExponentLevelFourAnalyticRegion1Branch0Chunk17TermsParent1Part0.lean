import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 17, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17

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
    69, 259, 587, 589, 1235, 2211,
    4925, 8329, 18039, 27295, 33425, 35519,
    65551, 111299, 112393
  ]
def positiveCoefficients : Array ℕ := #[
    3089898338056309166148214063104, 212014562888171367400323611099136, 871351331331879184853796365795328, 868816030131422726050802959384576, 27571400554963989482553294716928, 3248354663084837841335301963776,
    27175259742392667794585574965248, 457542638519876549602716313190400, 182066317457779447789963997872128, 4325065391653690189231564248842240, 458493376470047721653838840594432, 179293331769780195974189959610368,
    1191116195239450051381339749351424, 898368134749243323973194852859904, 896466658848900979870949798051840
  ]
def positiveScales : Array ℕ := #[
    6, 8, 9, 9, 10, 11,
    12, 13, 14, 14, 15, 15,
    16, 16, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 29, 31, 39, 41,
    109, 215, 253, 397, 995, 1149,
    1159, 1259, 1265, 1743, 2263, 3187,
    3485, 11315, 11339, 9047730261621
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 1426106925256758076683791106048, 11488083564568328951063872798720, 12280365189710972326999312302080, 3089898338056309166148214063104, 3248354663084837841335301963776,
    17271739428109625595392581173248, 17034054940566832582611949322240, 80178900464435509644666477740032, 503257288290607072394191172534272, 78832021701693015905576230584320, 273099476186669171684945996808192,
    91825440354032367270917438439424, 99748256605458801030271833473024, 100223625580544387055833097175040, 276189374524725480851094210871296, 179293331769780195974189959610368, 505000307865920887821249139441664,
    276110146362211216513500666920960, 896466658848900979870949798051840, 898368134749243323973194852859904, 2162532695826845094615782124421120
  ]
def negativeScales : Array ℕ := #[
    1, 3, 4, 4, 5, 5,
    6, 7, 7, 8, 9, 10,
    10, 10, 10, 10, 11, 11,
    11, 13, 13, 43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6108524456778168, 8016808287686553, 9197216693110051, 9202123823830460, 10270295326472039, 11110483309816225,
    12265908009231100, 13023927577174379, 14138831743917223, 14736349076623456, 15028639939868077, 15116303344251277,
    16000330168906265, 16764081104819947, 16778192659616360
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 4857980997143165, 4954196321574415, 5285402218862249, 5357552004618085,
    6768184325109843, 7748192849805622, 7982993592700323, 8632995197156697, 9958552727465983, 10166163082646114,
    10178664851006472, 10298062567719017, 10304921669581673, 10767356854452783, 11144020869266893, 11637983303793500,
    11766942941080008, 13465948964154339, 13469005792435018, 43040693057805603
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
noncomputable def positiveFloor : ℝ := 1798450532779 / 1000000000000
noncomputable def negativeCeiling : ℝ := 431204167271 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 29, coefficient := (-11488083564568328951063872798720) }, { argument := 31, coefficient := (-12280365189710972326999312302080) }, { argument := 39, coefficient := (-3089898338056309166148214063104) }, { argument := 41, coefficient := (-3248354663084837841335301963776) }, { argument := 69, coefficient := 3089898338056309166148214063104 }, { argument := 109, coefficient := (-17271739428109625595392581173248) }, { argument := 215, coefficient := (-17034054940566832582611949322240) }, { argument := 253, coefficient := (-80178900464435509644666477740032) }, { argument := 259, coefficient := 212014562888171367400323611099136 }, { argument := 397, coefficient := (-503257288290607072394191172534272) }, { argument := 587, coefficient := 871351331331879184853796365795328 }, { argument := 589, coefficient := 868816030131422726050802959384576 }, { argument := 995, coefficient := (-78832021701693015905576230584320) }, { argument := 1149, coefficient := (-273099476186669171684945996808192) }, { argument := 1159, coefficient := (-91825440354032367270917438439424) }, { argument := 1235, coefficient := 27571400554963989482553294716928 }, { argument := 1259, coefficient := (-99748256605458801030271833473024) }, { argument := 1265, coefficient := (-100223625580544387055833097175040) }, { argument := 1743, coefficient := (-276189374524725480851094210871296) }, { argument := 2211, coefficient := 3248354663084837841335301963776 }, { argument := 2263, coefficient := (-179293331769780195974189959610368) }, { argument := 3187, coefficient := (-505000307865920887821249139441664) }, { argument := 3485, coefficient := (-276110146362211216513500666920960) }, { argument := 4925, coefficient := 27175259742392667794585574965248 }, { argument := 8329, coefficient := 457542638519876549602716313190400 }, { argument := 11315, coefficient := (-896466658848900979870949798051840) }, { argument := 11339, coefficient := (-898368134749243323973194852859904) }, { argument := 18039, coefficient := 182066317457779447789963997872128 }, { argument := 27295, coefficient := 4325065391653690189231564248842240 }, { argument := 33425, coefficient := 458493376470047721653838840594432 }, { argument := 35519, coefficient := 179293331769780195974189959610368 }, { argument := 65551, coefficient := 1191116195239450051381339749351424 }, { argument := 111299, coefficient := 898368134749243323973194852859904 }, { argument := 112393, coefficient := 896466658848900979870949798051840 }, { argument := 9047730261621, coefficient := (-2162532695826845094615782124421120) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17
