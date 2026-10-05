import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    121, 239, 243, 257, 579, 1545,
    2319, 2969, 3083, 5901, 30947, 31009,
    36249, 40871, 145809
  ]
def positiveCoefficients : Array ℕ := #[
    695781723200269412746502971850752, 1677180972264461762517731884662784, 693801019137412804306664373092352, 96499901942373963188936531509248, 5466743213484239293954532573184, 352723779513504830966457666895872,
    5704427701027032306735164424192, 1254974094225947107481736173322240, 352723779513504830966457666895872, 1256717113801260922908794140229632, 195852017735261442531240645230592, 196485843035375557231988996833280,
    1416916458405103413522940007809024, 6476268460240995483571469588365312, 1417391827380188999548501271511040
  ]
def positiveScales : Array ℕ := #[
    6, 7, 7, 8, 9, 10,
    11, 11, 11, 12, 14, 14,
    15, 15, 17
  ]
def negativeArguments : Array ℕ := #[
    7, 9, 13, 19, 27, 35,
    67, 81, 131, 327, 495, 511,
    659, 661, 1023, 1069, 1075, 1113,
    1365, 2733, 4865, 4879, 7931, 9549,
    9561, 1733927750201
  ]
def negativeCoefficients : Array ℕ := #[
    9982748476797306536786537742336, 2852213850513516153367582212096, 2059932225370872777432142708736, 3010670175542044828554670112768, 2139160387885137115025686659072, 5545971375998503631548076523520,
    15924860665367131856302334017536, 25669924654621645380308239908864, 10378889289368628224754257494016, 25907609142164438393088871759872, 1254974094225947107481736173322240, 80971182089578153020601917243392,
    52211359096900198474145463271424, 52369815421928727149332551172096, 81050410252092417358195461193728, 84694905727748576887498482909184, 85170274702834162913059746611200, 705447559027009661932915333791744,
    216292883663941641630374984417280, 216530568151484434643155616268288, 385445010631896002392591318384640, 386554204907095703118900933689344, 1256717113801260922908794140229632, 756549723848710159680751181758464,
    757500461798881331731873709162496, 3238134230120497741785734794182656
  ]
def negativeScales : Array ℕ := #[
    2, 3, 3, 4, 4, 5,
    6, 6, 7, 8, 8, 8,
    9, 9, 9, 10, 10, 10,
    10, 11, 12, 12, 12, 13,
    13, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6918863236897629, 7900866807706560, 7924812503187618, 8005624549193878, 9177419537989236, 10593391122791443,
    11179287104646003, 11535761377986601, 11590119174106907, 12526743742999645, 14917511940643520, 14920399380820494,
    15145653575644180, 15318789922085690, 17153720246602593
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 3169925001442313, 3700439718214233, 4247927513443586, 4754887502413606, 5129283016944967,
    6066089190457773, 6339850002884626, 7033423001537451, 8353146825498084, 8951284725619456, 8997179503571248,
    9364134655008054, 9368506461507694, 9998590452895137, 10062046137720491, 10070120944476823, 10120237877341960,
    10414685235807227, 11416269744523220, 12248224089668474, 12252369767926028, 12953287078895944, 13221133942357078,
    13222945804499010, 40657180923855142
  ]

abbrev PositiveTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 2567863729173 / 1000000000000
noncomputable def negativeCeiling : ℝ := 494431417829 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7, coefficient := (-9982748476797306536786537742336) }, { argument := 9, coefficient := (-2852213850513516153367582212096) }, { argument := 13, coefficient := (-2059932225370872777432142708736) }, { argument := 19, coefficient := (-3010670175542044828554670112768) }, { argument := 27, coefficient := (-2139160387885137115025686659072) }, { argument := 35, coefficient := (-5545971375998503631548076523520) }, { argument := 67, coefficient := (-15924860665367131856302334017536) }, { argument := 81, coefficient := (-25669924654621645380308239908864) }, { argument := 121, coefficient := 695781723200269412746502971850752 }, { argument := 131, coefficient := (-10378889289368628224754257494016) }, { argument := 239, coefficient := 1677180972264461762517731884662784 }, { argument := 243, coefficient := 693801019137412804306664373092352 }, { argument := 257, coefficient := 96499901942373963188936531509248 }, { argument := 327, coefficient := (-25907609142164438393088871759872) }, { argument := 495, coefficient := (-1254974094225947107481736173322240) }, { argument := 511, coefficient := (-80971182089578153020601917243392) }, { argument := 579, coefficient := 5466743213484239293954532573184 }, { argument := 659, coefficient := (-52211359096900198474145463271424) }, { argument := 661, coefficient := (-52369815421928727149332551172096) }, { argument := 1023, coefficient := (-81050410252092417358195461193728) }, { argument := 1069, coefficient := (-84694905727748576887498482909184) }, { argument := 1075, coefficient := (-85170274702834162913059746611200) }, { argument := 1113, coefficient := (-705447559027009661932915333791744) }, { argument := 1365, coefficient := (-216292883663941641630374984417280) }, { argument := 1545, coefficient := 352723779513504830966457666895872 }, { argument := 2319, coefficient := 5704427701027032306735164424192 }, { argument := 2733, coefficient := (-216530568151484434643155616268288) }, { argument := 2969, coefficient := 1254974094225947107481736173322240 }, { argument := 3083, coefficient := 352723779513504830966457666895872 }, { argument := 4865, coefficient := (-385445010631896002392591318384640) }, { argument := 4879, coefficient := (-386554204907095703118900933689344) }, { argument := 5901, coefficient := 1256717113801260922908794140229632 }, { argument := 7931, coefficient := (-1256717113801260922908794140229632) }, { argument := 9549, coefficient := (-756549723848710159680751181758464) }, { argument := 9561, coefficient := (-757500461798881331731873709162496) }, { argument := 30947, coefficient := 195852017735261442531240645230592 }, { argument := 31009, coefficient := 196485843035375557231988996833280 }, { argument := 36249, coefficient := 1416916458405103413522940007809024 }, { argument := 40871, coefficient := 6476268460240995483571469588365312 }, { argument := 145809, coefficient := 1417391827380188999548501271511040 }, { argument := 1733927750201, coefficient := (-3238134230120497741785734794182656) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk12
