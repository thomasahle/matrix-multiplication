import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 9, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9

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
def constantNumerator : ℤ := 384428150898185864989804331008
def positiveArguments : Array ℕ := #[
    3, 2276561, 32125651, 9099753, 565725, 12296197,
    24601757, 142943
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 86006042900865619018695835648, 303418195045535401258036232192, 85944737139185005284531634176, 5343121557042860077036339200, 232268594318249131470852456448,
    232357025353007348447124127744, 5400233857286685566250778624
  ]
def positiveScales : Array ℕ := #[
    1, 21, 24, 23, 19, 23,
    24, 17
  ]
def negativeArguments : Array ℕ := #[
    429176790075, 2332767901991, 18669259651059, 216887988557, 429176790075, 6058994618229,
    1715588743071, 6058994618229, 131674033311163, 263448249958341, 382729673045, 2332767901991,
    131674033311163, 37297633304533, 1715588743071, 37297633304533, 74623702605935, 216745458697,
    18669259651059, 263448249958341, 74623702605935, 216887988557, 382729673045, 216745458697,
    3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    483210107964458896510156800, 21011705308297042667946115072, 21019717701948087144667938816, 488388332223220800223707136, 483210107964458896510156800, 1705455369055997816916148224,
    482895301500973325091864576, 1705455369055997816916148224, 74125890919315495547731705856, 74154090021487113497210781696, 1723661212909093767159480320, 21011705308297042667946115072,
    74125890919315495547731705856, 20996700931512027519748407296, 482895301500973325091864576, 20996700931512027519748407296, 21004704953068473581683343360, 488067383511028215742201856,
    21019717701948087144667938816, 74154090021487113497210781696, 21004704953068473581683343360, 488388332223220800223707136, 1723661212909093767159480320, 488067383511028215742201856,
    475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    38, 41, 44, 37, 38, 42,
    40, 42, 46, 47, 38, 41,
    46, 45, 40, 45, 46, 37,
    44, 47, 46, 37, 38, 37,
    1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21118424685926378, 24937222353329470, 23117395955238660, 19109741401082424, 23551708848263501,
    24552258017364149, 17125080446539045
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38642781100886384, 41085179912621227, 44085729950659350, 37658159201319792, 38642781100886384, 42462215562771160,
    40641840893460694, 42462215562771160, 46903964201053726, 47904512929324548, 38477534801300912, 41085179912621227,
    46903964201053726, 45084149321706812, 40641840893460694, 45084149321706812, 46084699177698689, 37657210809856718,
    44085729950659350, 47904512929324548, 46084699177698689, 37658159201319792, 38477534801300912, 37657210809856718,
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
noncomputable def positiveFloor : ℝ := 282784013 / 1000000000000
noncomputable def negativeCeiling : ℝ := 140844677 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 483210107964458896510156800, coefficient := (-483210107964458896510156800) }, { argument := 21011705308297042667946115072, coefficient := (-21011705308297042667946115072) }, { argument := 21019717701948087144667938816, coefficient := (-21019717701948087144667938816) }, { argument := 488388332223220800223707136, coefficient := (-488388332223220800223707136) }, { argument := 483210107964458896510156800, coefficient := (-483210107964458896510156800) }, { argument := 1705455369055997816916148224, coefficient := (-1705455369055997816916148224) }, { argument := 482895301500973325091864576, coefficient := (-482895301500973325091864576) }, { argument := 1705455369055997816916148224, coefficient := (-1705455369055997816916148224) }, { argument := 74125890919315495547731705856, coefficient := (-74125890919315495547731705856) }, { argument := 74154090021487113497210781696, coefficient := (-74154090021487113497210781696) }, { argument := 1723661212909093767159480320, coefficient := (-1723661212909093767159480320) }, { argument := 21011705308297042667946115072, coefficient := (-21011705308297042667946115072) }, { argument := 74125890919315495547731705856, coefficient := (-74125890919315495547731705856) }, { argument := 20996700931512027519748407296, coefficient := (-20996700931512027519748407296) }, { argument := 482895301500973325091864576, coefficient := (-482895301500973325091864576) }, { argument := 20996700931512027519748407296, coefficient := (-20996700931512027519748407296) }, { argument := 21004704953068473581683343360, coefficient := (-21004704953068473581683343360) }, { argument := 488067383511028215742201856, coefficient := (-488067383511028215742201856) }, { argument := 21019717701948087144667938816, coefficient := (-21019717701948087144667938816) }, { argument := 74154090021487113497210781696, coefficient := (-74154090021487113497210781696) }, { argument := 21004704953068473581683343360, coefficient := (-21004704953068473581683343360) }, { argument := 488388332223220800223707136, coefficient := (-488388332223220800223707136) }, { argument := 1723661212909093767159480320, coefficient := (-1723661212909093767159480320) }, { argument := 488067383511028215742201856, coefficient := (-488067383511028215742201856) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 86006042900865619018695835648, coefficient := 86006042900865619018695835648 }, { argument := 303418195045535401258036232192, coefficient := 303418195045535401258036232192 }, { argument := 85944737139185005284531634176, coefficient := 85944737139185005284531634176 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 5343121557042860077036339200, coefficient := 5343121557042860077036339200 }, { argument := 232268594318249131470852456448, coefficient := 232268594318249131470852456448 }, { argument := 232357025353007348447124127744, coefficient := 232357025353007348447124127744 }, { argument := 5400233857286685566250778624, coefficient := 5400233857286685566250778624 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk9
