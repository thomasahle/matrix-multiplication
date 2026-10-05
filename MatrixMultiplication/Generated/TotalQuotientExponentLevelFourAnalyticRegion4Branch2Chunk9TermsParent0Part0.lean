import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 9, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9

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
def constantNumerator : ℤ := (-5445173305972582715985064099840)
def positiveArguments : Array ℕ := #[
    9, 67108939, 67108789, 30139741, 53746907, 30138605,
    867157, 32687293, 65374569, 1734259
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 633826008469087131195133657088, 633824591759142270301569548288, 569323610803088174010748370944, 2030500737397695315388112306176, 569302152369790014342897336320,
    16380132608743171738291929088, 617445507515758295624515059712, 617445346955297878056577794048, 16379613148430056077318422528
  ]
def positiveScales : Array ℕ := #[
    3, 26, 25, 24, 25, 24,
    19, 24, 25, 20
  ]
def negativeArguments : Array ℕ := #[
    14548498681247, 548402385875203, 548402243269487, 14548037307887, 22708287275407, 323998311350683,
    90829484488745, 14548498681247, 14548461908577, 14548461908577, 548401164357373, 548401021750417,
    14548000535057, 323998311350683, 288865510841293, 323986581425969, 548402385875203, 548401164357373,
    90829484488745, 323986581425969, 45412910054483, 548402243269487, 548401021750417, 14548037307887,
    14548000535057, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4095038327479008853892268032, 154361548792290949356656263168, 154361508652350359450232553472, 4094908462423247936785743872, 51134517055872570537789095936, 182394834283450737919677956096,
    51132454062220778547907133440, 4095038327479008853892268032, 4095027976892577015253696512, 4095027976892577015253696512, 154361204965588198455601266688, 154361164825298579578056343552,
    4094898111791780101873467392, 182394834283450737919677956096, 650467303492517563651183345664, 182388230922879356123194851328, 154361548792290949356656263168, 154361204965588198455601266688,
    51132454062220778547907133440, 182388230922879356123194851328, 51130391199794872500346683392, 154361508652350359450232553472, 154361164825298579578056343552, 4094908462423247936785743872,
    4094898111791780101873467392, 1267650600228229401496703205376, 3169126500570573503741758013440, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    43, 48, 48, 43, 44, 48,
    46, 43, 43, 43, 48, 48,
    43, 48, 48, 48, 48, 48,
    46, 48, 45, 48, 48, 43,
    43, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 26000001612336450, 25999998386202203, 24845163683583685, 25679678397810312, 24845109305795563,
    19725933693499541, 24962226568603458, 25962226193445158, 20725887940835698
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    43725935516912829, 48962228188927815, 48962227813771479, 43725889764314598, 44368284131458229, 48202979622359072,
    46368225925555020, 43725935516912829, 43725931870363655, 43725931870363655, 48962224975447898, 48962224600287464,
    43725886117633911, 48202979622359072, 48037391291728486, 48202927390572790, 48962228188927815, 48962224975447898,
    46368225925555020, 48202927390572790, 45368167721006052, 48962227813771479, 48962224600287464, 43725889764314598,
    43725886117633911, 0, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 37203623 / 20000000000
noncomputable def negativeCeiling : ℝ := 13635567 / 7812500000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4095038327479008853892268032, coefficient := (-4095038327479008853892268032) }, { argument := 154361548792290949356656263168, coefficient := (-154361548792290949356656263168) }, { argument := 154361508652350359450232553472, coefficient := (-154361508652350359450232553472) }, { argument := 4094908462423247936785743872, coefficient := (-4094908462423247936785743872) }, { argument := 51134517055872570537789095936, coefficient := (-51134517055872570537789095936) }, { argument := 182394834283450737919677956096, coefficient := (-182394834283450737919677956096) }, { argument := 51132454062220778547907133440, coefficient := (-51132454062220778547907133440) }, { argument := 4095038327479008853892268032, coefficient := (-4095038327479008853892268032) }, { argument := 4095027976892577015253696512, coefficient := (-4095027976892577015253696512) }, { argument := 4095027976892577015253696512, coefficient := (-4095027976892577015253696512) }, { argument := 154361204965588198455601266688, coefficient := (-154361204965588198455601266688) }, { argument := 154361164825298579578056343552, coefficient := (-154361164825298579578056343552) }, { argument := 4094898111791780101873467392, coefficient := (-4094898111791780101873467392) }, { argument := 182394834283450737919677956096, coefficient := (-182394834283450737919677956096) }, { argument := 650467303492517563651183345664, coefficient := (-650467303492517563651183345664) }, { argument := 182388230922879356123194851328, coefficient := (-182388230922879356123194851328) }, { argument := 154361548792290949356656263168, coefficient := (-154361548792290949356656263168) }, { argument := 154361204965588198455601266688, coefficient := (-154361204965588198455601266688) }, { argument := 51132454062220778547907133440, coefficient := (-51132454062220778547907133440) }, { argument := 182388230922879356123194851328, coefficient := (-182388230922879356123194851328) }, { argument := 51130391199794872500346683392, coefficient := (-51130391199794872500346683392) }, { argument := 154361508652350359450232553472, coefficient := (-154361508652350359450232553472) }, { argument := 154361164825298579578056343552, coefficient := (-154361164825298579578056343552) }, { argument := 4094908462423247936785743872, coefficient := (-4094908462423247936785743872) }, { argument := 4094898111791780101873467392, coefficient := (-4094898111791780101873467392) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 633826008469087131195133657088, coefficient := 633826008469087131195133657088 }, { argument := 633824591759142270301569548288, coefficient := 633824591759142270301569548288 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 569323610803088174010748370944, coefficient := 569323610803088174010748370944 }, { argument := 2030500737397695315388112306176, coefficient := 2030500737397695315388112306176 }, { argument := 569302152369790014342897336320, coefficient := 569302152369790014342897336320 }, { argument := 3169126500570573503741758013440, coefficient := (-3169126500570573503741758013440) }, { argument := 16380132608743171738291929088, coefficient := 16380132608743171738291929088 }, { argument := 617445507515758295624515059712, coefficient := 617445507515758295624515059712 }, { argument := 617445346955297878056577794048, coefficient := 617445346955297878056577794048 }, { argument := 16379613148430056077318422528, coefficient := 16379613148430056077318422528 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9
