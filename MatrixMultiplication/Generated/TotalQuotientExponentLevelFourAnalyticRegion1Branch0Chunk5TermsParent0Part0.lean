import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk5

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
    89, 129, 285, 465, 931, 1135,
    1167, 1727, 2275, 2329, 3527, 4569
  ]
def positiveCoefficients : Array ℕ := #[
    86437925303062392314556449816576, 46982300370958752192971562549248, 1267650600228229401496703205376, 8556641551540548460102746636288, 8635869714054812797696290586624, 359695857814760092674689534525440,
    13389559464910673053308927606784, 75425210713579649389053840719872, 80416584951978302657447109591040, 13151874977367880040528295755776, 77089002126379200478518263676928, 80812725764549624345414829342720
  ]
def positiveScales : Array ℕ := #[
    6, 7, 8, 8, 9, 10,
    10, 10, 11, 11, 11, 12
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 9, 17, 35, 47,
    125, 127, 253, 257, 293, 387,
    593, 1091, 1560033993
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 1109194275199700726309615304704, 5704427701027032306735164424192, 2693757525484987478180494311424, 8318957063997755447322114785280, 29789789105363390935172525326336,
    9903520314283042199192993792000, 10061976639311570874380081692672, 40089450232217754822333238870016, 40723275532331869523081590472704, 46427703233358901829816754896896, 30661298893020298648701508780032,
    46982300370958752192971562549248, 86437925303062392314556449816576, 179847928907380046337344767262720
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 5, 5,
    6, 6, 7, 8, 8, 8,
    9, 10, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6475733430966389, 7011227255423254, 8154818109052103, 8861086905863166, 9862637357422660, 10148476582178277,
    10188588845707347, 10754052367513689, 11151650829973420, 11185494924210865, 11784225860397322, 12157662727208448
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 3169925001442313, 4087462841250340, 5129283016944967, 5554588851679165,
    6965784298236803, 6988684706517367, 7982993592700323, 8005624549193879, 8194756854422248, 8596189756149498,
    9211888294546004, 10091435386323608, 30538930319612051
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 808101769 / 7812500000
noncomputable def negativeCeiling : ℝ := 101929019471 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 9, coefficient := (-5704427701027032306735164424192) }, { argument := 17, coefficient := (-2693757525484987478180494311424) }, { argument := 35, coefficient := (-8318957063997755447322114785280) }, { argument := 47, coefficient := (-29789789105363390935172525326336) }, { argument := 89, coefficient := 86437925303062392314556449816576 }, { argument := 125, coefficient := (-9903520314283042199192993792000) }, { argument := 127, coefficient := (-10061976639311570874380081692672) }, { argument := 129, coefficient := 46982300370958752192971562549248 }, { argument := 253, coefficient := (-40089450232217754822333238870016) }, { argument := 257, coefficient := (-40723275532331869523081590472704) }, { argument := 285, coefficient := 1267650600228229401496703205376 }, { argument := 293, coefficient := (-46427703233358901829816754896896) }, { argument := 387, coefficient := (-30661298893020298648701508780032) }, { argument := 465, coefficient := 8556641551540548460102746636288 }, { argument := 593, coefficient := (-46982300370958752192971562549248) }, { argument := 931, coefficient := 8635869714054812797696290586624 }, { argument := 1091, coefficient := (-86437925303062392314556449816576) }, { argument := 1135, coefficient := 359695857814760092674689534525440 }, { argument := 1167, coefficient := 13389559464910673053308927606784 }, { argument := 1727, coefficient := 75425210713579649389053840719872 }, { argument := 2275, coefficient := 80416584951978302657447109591040 }, { argument := 2329, coefficient := 13151874977367880040528295755776 }, { argument := 3527, coefficient := 77089002126379200478518263676928 }, { argument := 4569, coefficient := 80812725764549624345414829342720 }, { argument := 1560033993, coefficient := (-179847928907380046337344767262720) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk5
