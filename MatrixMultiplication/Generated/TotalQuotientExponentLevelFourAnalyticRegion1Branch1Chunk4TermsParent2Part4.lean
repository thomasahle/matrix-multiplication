import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-54239955012289222144418300035072000)
def positiveArguments : Array ℕ := #[
    30785, 22925, 24235, 1965, 421165, 761765,
    22925, 421165, 12445, 12445, 24235, 24235,
    761765, 24235, 30785, 1965, 93, 285,
    843, 1881, 93, 939, 1911, 93,
    285, 93, 29360119, 29360137, 2612906761, 9403346581,
    1306739505, 419664691, 33243581893, 4155447829, 839334701, 2616125,
    1863737905, 19290906149, 931869409, 2616125, 9797809, 1927970639,
    1927970653, 9797795, 355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    595468501709381746293274050560, 443433990634645981282225356800, 468773075813768608784066805760, 608138044298943060044194775040, 8146515885087924741842025840640, 14734678031659807892320802570240,
    443433990634645981282225356800, 8146515885087924741842025840640, 481442618403329922534987530240, 481442618403329922534987530240, 468773075813768608784066805760, 468773075813768608784066805760,
    14734678031659807892320802570240, 468773075813768608784066805760, 595468501709381746293274050560, 608138044298943060044194775040, 7195526478346272847851159552, 176406455598166689173125201920,
    130447931639696946467495215104, 145535325868487518567828291584, 7195526478346272847851159552, 145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552,
    176406455598166689173125201920, 7195526478346272847851159552, 554596967594656979847579959296, 554597307605043746462035345408, 12339103311009886660537568198656, 44406048720921273388891295973376,
    12341805680507342332141460520960, 7927241883288985807541443231744, 313976753804070864610716922413056, 313976760783728526292052548255744, 7927292119823630574827226529792, 197668816239957609354887168000,
    35205013661702763834668241387520, 364394914488886168073346341666816, 35205030907785159274612561805312, 197668816239957609354887168000, 46268844827158555701557592064, 9104583925570372436352768671744,
    9104583991683503196527801663488, 46268778714027795526524600320, 3356875324881955821574946816, 151724657720328756109997244416, 3374791983317963255515709440
  ]
def positiveScales : Array ℕ := #[
    14, 14, 14, 10, 18, 19,
    14, 18, 13, 13, 14, 14,
    19, 14, 14, 10, 6, 8,
    9, 10, 6, 9, 10, 6,
    8, 6, 24, 24, 31, 33,
    30, 28, 34, 31, 29, 21,
    30, 34, 29, 21, 23, 30,
    30, 23, 18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    1773, 655, 3, 7, 109, 4063,
    5493, 231, 1
  ]
def negativeCoefficients : Array ℕ := #[
    280943064275581341106706847891456, 51894446446843141123771287470080, 950737950171172051122527404032, 1109194275199700726309615304704, 69086957712438502381570324692992, 643808048590912007285138140430336,
    435200296690854006401336919195648, 18301705540795061984108652527616, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    10, 9, 1, 2, 6, 11,
    12, 7, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14909939947780247, 14484634113369768, 14564804462053633, 10940313596599942, 18684026023749686, 19538986477897971,
    14484634113369768, 18684026023749686, 13603278609868012, 13603278609868012, 14564804462053633, 14564804462053633,
    19538986477897971, 14564804462053633, 14909939947780247, 10940313596599942, 6539158811107971, 8154818109052103,
    9719388820935039, 10877284133344468, 6539158811107971, 9874981347482478, 10900112062706946, 6539158811107971,
    8154818109052103, 6539158811107971, 24807354479769974, 24807355364252177, 31283008498413458, 33130527146581751,
    30283324426411859, 28644661844522915, 34952356784610259, 31952356816681160, 29644670987144122, 21319000044629489,
    30795551843908118, 34167201861361956, 29795552550649256, 21319000044629489, 23224027737099393, 30844435934870817,
    30844435945346978, 23224025675644122, 18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10791976821446750, 9355351096424814, 1584962500724866, 2807354922807594, 6768184325109843, 11988329668863380,
    12423378576518511, 7851749043206919, 0
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 119949352301 / 250000000000
noncomputable def negativeCeiling : ℝ := 207737754313 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 280943064275581341106706847891456, coefficient := (-280943064275581341106706847891456) }, { argument := 595468501709381746293274050560, coefficient := 595468501709381746293274050560 }, { argument := 443433990634645981282225356800, coefficient := 443433990634645981282225356800 }, { argument := 468773075813768608784066805760, coefficient := 468773075813768608784066805760 }, { argument := 608138044298943060044194775040, coefficient := 608138044298943060044194775040 }, { argument := 8146515885087924741842025840640, coefficient := 8146515885087924741842025840640 }, { argument := 14734678031659807892320802570240, coefficient := 14734678031659807892320802570240 }, { argument := 443433990634645981282225356800, coefficient := 443433990634645981282225356800 }, { argument := 8146515885087924741842025840640, coefficient := 8146515885087924741842025840640 }, { argument := 481442618403329922534987530240, coefficient := 481442618403329922534987530240 }, { argument := 481442618403329922534987530240, coefficient := 481442618403329922534987530240 }, { argument := 468773075813768608784066805760, coefficient := 468773075813768608784066805760 }, { argument := 468773075813768608784066805760, coefficient := 468773075813768608784066805760 }, { argument := 14734678031659807892320802570240, coefficient := 14734678031659807892320802570240 }, { argument := 468773075813768608784066805760, coefficient := 468773075813768608784066805760 }, { argument := 595468501709381746293274050560, coefficient := 595468501709381746293274050560 }, { argument := 608138044298943060044194775040, coefficient := 608138044298943060044194775040 }, { argument := 51894446446843141123771287470080, coefficient := (-51894446446843141123771287470080) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 147856463442147606583264149504, coefficient := 147856463442147606583264149504 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 554596967594656979847579959296, coefficient := 554596967594656979847579959296 }, { argument := 554597307605043746462035345408, coefficient := 554597307605043746462035345408 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 12339103311009886660537568198656, coefficient := 12339103311009886660537568198656 }, { argument := 44406048720921273388891295973376, coefficient := 44406048720921273388891295973376 }, { argument := 12341805680507342332141460520960, coefficient := 12341805680507342332141460520960 }, { argument := 69086957712438502381570324692992, coefficient := (-69086957712438502381570324692992) }, { argument := 7927241883288985807541443231744, coefficient := 7927241883288985807541443231744 }, { argument := 313976753804070864610716922413056, coefficient := 313976753804070864610716922413056 }, { argument := 313976760783728526292052548255744, coefficient := 313976760783728526292052548255744 }, { argument := 7927292119823630574827226529792, coefficient := 7927292119823630574827226529792 }, { argument := 643808048590912007285138140430336, coefficient := (-643808048590912007285138140430336) }, { argument := 197668816239957609354887168000, coefficient := 197668816239957609354887168000 }, { argument := 35205013661702763834668241387520, coefficient := 35205013661702763834668241387520 }, { argument := 364394914488886168073346341666816, coefficient := 364394914488886168073346341666816 }, { argument := 35205030907785159274612561805312, coefficient := 35205030907785159274612561805312 }, { argument := 197668816239957609354887168000, coefficient := 197668816239957609354887168000 }, { argument := 435200296690854006401336919195648, coefficient := (-435200296690854006401336919195648) }, { argument := 46268844827158555701557592064, coefficient := 46268844827158555701557592064 }, { argument := 9104583925570372436352768671744, coefficient := 9104583925570372436352768671744 }, { argument := 9104583991683503196527801663488, coefficient := 9104583991683503196527801663488 }, { argument := 46268778714027795526524600320, coefficient := 46268778714027795526524600320 }, { argument := 18301705540795061984108652527616, coefficient := (-18301705540795061984108652527616) }, { argument := 3356875324881955821574946816, coefficient := 3356875324881955821574946816 }, { argument := 151724657720328756109997244416, coefficient := 151724657720328756109997244416 }, { argument := 3374791983317963255515709440, coefficient := 3374791983317963255515709440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard8


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
