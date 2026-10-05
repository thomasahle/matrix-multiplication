import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 144921, 8243685, 1030465, 72445, 48085,
    1100569, 14479933, 1100543, 24043
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1368740146127903708028076032, 77859403478670502406935019520, 77859734044324303282099978240, 1368447359405965790024826880, 454149984657573780201144320,
    10394580315370725126384386048, 136759100546796220856177524736, 10394334752313615904833273856, 454159429390539519491571712
  ]
def positiveScales : Array ℕ := #[
    0, 17, 22, 19, 16, 15,
    20, 23, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    6968526285, 159495560049, 2098446370293, 159491792103, 3484335603, 6968526285,
    396397593225, 49549909525, 3483517825, 396397593225, 9072744156765, 119368006473105,
    9072529820955, 198202918455, 159495560049, 9072744156765, 1134097834585, 79730721205,
    49549909525, 1134097834585, 14921064158845, 1134071042495, 24775469995, 2098446370293,
    119368006473105, 14921064158845, 1048998746185, 3483517825, 79730721205, 1048998746185,
    79728837635, 1741795135, 159491792103, 9072529820955, 1134071042495, 79728837635,
    3484335603, 198202918455, 24775469995, 1741795135, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1961465773777969175592960, 44894009050245310546182144, 590660143206782791694942208, 44892948467732713536749568, 1961506565413069060571136, 1961465773777969175592960,
    111576003321166965610905600, 111576477036515895227187200, 1961046197326060086886400, 111576003321166965610905600, 2553750450227168684109987840, 33599106842014664528630906880,
    2553690120060040674520596480, 111578323712210350595112960, 44894009050245310546182144, 2553750450227168684109987840, 2553761292619346205558702080, 44884405788602362977320960,
    111576477036515895227187200, 2553761292619346205558702080, 33599249492872802668705218560, 2553700962196075967162613760, 111578797437410904396267520, 590660143206782791694942208,
    33599106842014664528630906880, 33599249492872802668705218560, 590533795303860439057694720, 1961046197326060086886400, 44884405788602362977320960, 590533795303860439057694720,
    44883345432958597196677120, 1961086980235435693834240, 44892948467732713536749568, 2553690120060040674520596480, 2553700962196075967162613760, 44883345432958597196677120,
    1961506565413069060571136, 111578323712210350595112960, 111578797437410904396267520, 1961086980235435693834240, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 37, 40, 37, 31, 32,
    38, 35, 31, 38, 43, 46,
    43, 37, 37, 43, 40, 36,
    35, 40, 43, 40, 34, 40,
    46, 43, 39, 31, 36, 39,
    36, 30, 37, 43, 40, 36,
    31, 37, 34, 30, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 17144907140419750, 22974857947365051, 19974864072564938, 16144598501020707, 15553299298480189,
    20069818166927335, 23787551591132640, 20069784084090055, 14553329301184558
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32698206438969426, 37214725307347087, 40932458739311267, 37214691224509808, 31698236441673844, 32698206438969426,
    38528157246818612, 35528163372018597, 31697897799569878, 38528157246818612, 43044676115264989, 46762409539795531,
    43044642032427710, 37528187249522981, 37214725307347087, 43044676115264989, 40044682240464975, 36214416667948043,
    35528163372018597, 40044682240464975, 43762415664995554, 40044648157627695, 34528193374722967, 40932458739311267,
    46762409539795531, 43762415664995554, 39932150099871207, 31697897799569878, 36214416667948043, 39932150099871207,
    36214382585110764, 30697927802274296, 37214691224509808, 43044642032427710, 40044648157627695, 36214382585110764,
    31698236441673844, 37528187249522981, 34528193374722967, 30697927802274296, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 133041 / 1562500000
noncomputable def negativeCeiling : ℝ := 85146241 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1961465773777969175592960, coefficient := (-1961465773777969175592960) }, { argument := 44894009050245310546182144, coefficient := (-44894009050245310546182144) }, { argument := 590660143206782791694942208, coefficient := (-590660143206782791694942208) }, { argument := 44892948467732713536749568, coefficient := (-44892948467732713536749568) }, { argument := 1961506565413069060571136, coefficient := (-1961506565413069060571136) }, { argument := 1961465773777969175592960, coefficient := (-1961465773777969175592960) }, { argument := 111576003321166965610905600, coefficient := (-111576003321166965610905600) }, { argument := 111576477036515895227187200, coefficient := (-111576477036515895227187200) }, { argument := 1961046197326060086886400, coefficient := (-1961046197326060086886400) }, { argument := 111576003321166965610905600, coefficient := (-111576003321166965610905600) }, { argument := 2553750450227168684109987840, coefficient := (-2553750450227168684109987840) }, { argument := 33599106842014664528630906880, coefficient := (-33599106842014664528630906880) }, { argument := 2553690120060040674520596480, coefficient := (-2553690120060040674520596480) }, { argument := 111578323712210350595112960, coefficient := (-111578323712210350595112960) }, { argument := 44894009050245310546182144, coefficient := (-44894009050245310546182144) }, { argument := 2553750450227168684109987840, coefficient := (-2553750450227168684109987840) }, { argument := 2553761292619346205558702080, coefficient := (-2553761292619346205558702080) }, { argument := 44884405788602362977320960, coefficient := (-44884405788602362977320960) }, { argument := 111576477036515895227187200, coefficient := (-111576477036515895227187200) }, { argument := 2553761292619346205558702080, coefficient := (-2553761292619346205558702080) }, { argument := 33599249492872802668705218560, coefficient := (-33599249492872802668705218560) }, { argument := 2553700962196075967162613760, coefficient := (-2553700962196075967162613760) }, { argument := 111578797437410904396267520, coefficient := (-111578797437410904396267520) }, { argument := 590660143206782791694942208, coefficient := (-590660143206782791694942208) }, { argument := 33599106842014664528630906880, coefficient := (-33599106842014664528630906880) }, { argument := 33599249492872802668705218560, coefficient := (-33599249492872802668705218560) }, { argument := 590533795303860439057694720, coefficient := (-590533795303860439057694720) }, { argument := 1961046197326060086886400, coefficient := (-1961046197326060086886400) }, { argument := 44884405788602362977320960, coefficient := (-44884405788602362977320960) }, { argument := 590533795303860439057694720, coefficient := (-590533795303860439057694720) }, { argument := 44883345432958597196677120, coefficient := (-44883345432958597196677120) }, { argument := 1961086980235435693834240, coefficient := (-1961086980235435693834240) }, { argument := 44892948467732713536749568, coefficient := (-44892948467732713536749568) }, { argument := 2553690120060040674520596480, coefficient := (-2553690120060040674520596480) }, { argument := 2553700962196075967162613760, coefficient := (-2553700962196075967162613760) }, { argument := 44883345432958597196677120, coefficient := (-44883345432958597196677120) }, { argument := 1961506565413069060571136, coefficient := (-1961506565413069060571136) }, { argument := 111578323712210350595112960, coefficient := (-111578323712210350595112960) }, { argument := 111578797437410904396267520, coefficient := (-111578797437410904396267520) }, { argument := 1961086980235435693834240, coefficient := (-1961086980235435693834240) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 1368740146127903708028076032, coefficient := 1368740146127903708028076032 }, { argument := 77859403478670502406935019520, coefficient := 77859403478670502406935019520 }, { argument := 77859734044324303282099978240, coefficient := 77859734044324303282099978240 }, { argument := 1368447359405965790024826880, coefficient := 1368447359405965790024826880 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 454149984657573780201144320, coefficient := 454149984657573780201144320 }, { argument := 10394580315370725126384386048, coefficient := 10394580315370725126384386048 }, { argument := 136759100546796220856177524736, coefficient := 136759100546796220856177524736 }, { argument := 10394334752313615904833273856, coefficient := 10394334752313615904833273856 }, { argument := 454159429390539519491571712, coefficient := 454159429390539519491571712 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0
