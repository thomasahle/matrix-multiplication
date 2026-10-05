import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4

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
def constantNumerator : ℤ := 757192854764344568737775484928
def positiveArguments : Array ℕ := #[
    7, 1048353, 1048799, 9043377, 8061219, 9043395,
    218671, 4084967, 16339871, 437351
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 316845252442613834797685932032, 316980047671500865950665670656, 170824561747016974094793965568, 609088486666751336318484086784, 170824901757403740709249351680,
    8261156809404705508192944128, 308651379910857055994497728512, 308651436579254850430240292864, 8261326814598088815420637184
  ]
def positiveScales : Array ℕ := #[
    2, 19, 20, 23, 22, 23,
    17, 21, 23, 18
  ]
def negativeArguments : Array ℕ := #[
    1833920213217, 8564979192921, 68519846083195, 458489490551, 851887910463, 48600981553491,
    13630156528317, 1833920213217, 1834770386719, 1834770386719, 8568614235047, 68548926506373,
    458702033801, 48600981553491, 86643692786985, 48601257645147, 8564979192921, 8568614235047,
    13630156528317, 48601257645147, 1703760183837, 68519846083195, 68548926506373, 458489490551,
    458702033801, 1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2064810597217825443343761408, 77146474203350134343054917632, 77146488321940185465676103680, 2064853098798772146768183296, 15346248304490389042303598592, 54719840603535604352374800384,
    15346191965482493652718583808, 2064810597217825443343761408, 2065767807484527310752710656, 2065767807484527310752710656, 77179215752078393654193946624, 77179229967687239749444042752,
    2065810308500272260942135296, 54719840603535604352374800384, 195104251274734689028700897280, 54720151455105374778166345728, 77146474203350134343054917632, 77179215752078393654193946624,
    15346191965482493652718583808, 54720151455105374778166345728, 15346107458114001923739746304, 77146488321940185465676103680, 77179229967687239749444042752, 2064853098798772146768183296,
    2065810308500272260942135296, 633825300114114700748351602688, 950737950171172051122527404032, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    40, 42, 45, 38, 39, 45,
    43, 40, 40, 40, 42, 45,
    38, 45, 46, 45, 42, 42,
    43, 45, 40, 45, 45, 38,
    38, 0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 19999693148868470, 20000306784428469, 23108430177294975, 22942566585212127, 23108433048842285,
    17738402378258116, 21961892992288406, 23961893257167209, 18738432066972591
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40738068013032227, 42961586892853402, 45961587156881311, 38738097708825789, 39631872660073459, 45466050684569608,
    43631867363654757, 40738068013032227, 40738736666377895, 40738736666377895, 42962199053806170, 45962199319535624,
    38738766348016807, 45466050684569608, 46300159966001080, 45466058880184570, 42961586892853402, 42962199053806170,
    43631867363654757, 45466058880184570, 40631859419097733, 45961587156881311, 45962199319535624, 38738097708825789,
    38738766348016807, 0, 1584962500724866, 0
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
noncomputable def positiveFloor : ℝ := 627555001 / 1000000000000
noncomputable def negativeCeiling : ℝ := 615885771 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2064810597217825443343761408, coefficient := (-2064810597217825443343761408) }, { argument := 77146474203350134343054917632, coefficient := (-77146474203350134343054917632) }, { argument := 77146488321940185465676103680, coefficient := (-77146488321940185465676103680) }, { argument := 2064853098798772146768183296, coefficient := (-2064853098798772146768183296) }, { argument := 15346248304490389042303598592, coefficient := (-15346248304490389042303598592) }, { argument := 54719840603535604352374800384, coefficient := (-54719840603535604352374800384) }, { argument := 15346191965482493652718583808, coefficient := (-15346191965482493652718583808) }, { argument := 2064810597217825443343761408, coefficient := (-2064810597217825443343761408) }, { argument := 2065767807484527310752710656, coefficient := (-2065767807484527310752710656) }, { argument := 2065767807484527310752710656, coefficient := (-2065767807484527310752710656) }, { argument := 77179215752078393654193946624, coefficient := (-77179215752078393654193946624) }, { argument := 77179229967687239749444042752, coefficient := (-77179229967687239749444042752) }, { argument := 2065810308500272260942135296, coefficient := (-2065810308500272260942135296) }, { argument := 54719840603535604352374800384, coefficient := (-54719840603535604352374800384) }, { argument := 195104251274734689028700897280, coefficient := (-195104251274734689028700897280) }, { argument := 54720151455105374778166345728, coefficient := (-54720151455105374778166345728) }, { argument := 77146474203350134343054917632, coefficient := (-77146474203350134343054917632) }, { argument := 77179215752078393654193946624, coefficient := (-77179215752078393654193946624) }, { argument := 15346191965482493652718583808, coefficient := (-15346191965482493652718583808) }, { argument := 54720151455105374778166345728, coefficient := (-54720151455105374778166345728) }, { argument := 15346107458114001923739746304, coefficient := (-15346107458114001923739746304) }, { argument := 77146488321940185465676103680, coefficient := (-77146488321940185465676103680) }, { argument := 77179229967687239749444042752, coefficient := (-77179229967687239749444042752) }, { argument := 2064853098798772146768183296, coefficient := (-2064853098798772146768183296) }, { argument := 2065810308500272260942135296, coefficient := (-2065810308500272260942135296) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 316845252442613834797685932032, coefficient := 316845252442613834797685932032 }, { argument := 316980047671500865950665670656, coefficient := 316980047671500865950665670656 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 170824561747016974094793965568, coefficient := 170824561747016974094793965568 }, { argument := 609088486666751336318484086784, coefficient := 609088486666751336318484086784 }, { argument := 170824901757403740709249351680, coefficient := 170824901757403740709249351680 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 8261156809404705508192944128, coefficient := 8261156809404705508192944128 }, { argument := 308651379910857055994497728512, coefficient := 308651379910857055994497728512 }, { argument := 308651436579254850430240292864, coefficient := 308651436579254850430240292864 }, { argument := 8261326814598088815420637184, coefficient := 8261326814598088815420637184 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4
