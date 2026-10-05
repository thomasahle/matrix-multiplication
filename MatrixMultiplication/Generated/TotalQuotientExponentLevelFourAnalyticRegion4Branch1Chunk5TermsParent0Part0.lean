import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5

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
def constantNumerator : ℤ := (-6062546053204405809746376916992)
def positiveArguments : Array ℕ := #[
    9, 16777231, 16777201, 31499451, 209605255, 62940163,
    909663, 65289555, 32644365, 1820117
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 633825866798092645105777246208, 633824733430136756390925959168, 595007806524778915184806723584, 1979665661690690233552559144960, 594453032355104355004392144896,
    17183048247626600296105377792, 616642412426948518020183490560, 616634620522251783105580892160, 17190519031402500074833444864
  ]
def positiveScales : Array ℕ := #[
    3, 24, 23, 24, 27, 25,
    19, 25, 24, 20
  ]
def negativeArguments : Array ℕ := #[
    7630812359005, 547688974625777, 273841027020961, 15268260089875, 12399721467721, 660337202567409,
    198213440565887, 7630812359005, 7630800279203, 7630800279203, 547687992153103, 273840535766879,
    15268235964397, 660337202567409, 1098269749999045, 659715935304581, 547688974625777, 547687992153103,
    198213440565887, 659715935304581, 49507833463935, 273841027020961, 273840535766879, 15268260089875,
    15268235964397, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4295765462068636693362114560, 154160741377473646008008179712, 154158793406294235741088120832, 4297633153209804110430208000, 55843380981526235344971759616, 185868398713841181684928610304,
    55792123567022040562502991872, 4295765462068636693362114560, 4295758661744663454690574336, 4295758661744663454690574336, 154160464836000613002083565568, 154158516854831655811702325248,
    4297626362491445926986514432, 185868398713841181684928610304, 618270904605998357706482647040, 185693527525505577384868315136, 154160741377473646008008179712, 154160464836000613002083565568,
    55792123567022040562502991872, 185693527525505577384868315136, 55740865085024559554824765440, 154158793406294235741088120832, 154158516854831655811702325248, 4297633153209804110430208000,
    4297626362491445926986514432, 1267650600228229401496703205376, 3169126500570573503741758013440, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    42, 48, 47, 43, 43, 49,
    47, 42, 42, 42, 48, 47,
    43, 49, 49, 49, 48, 48,
    47, 49, 45, 47, 47, 43,
    43, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 24000001289869304, 23999998708669990, 24908823348175508, 27643099646142059, 25907477578780082,
    19794972647980185, 25960348871833507, 24960330641797884, 20795599761411807
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    42794973790514158, 48960350178991471, 47960331949014939, 43795600901845255, 43495372947563352, 49230196256287338,
    47494048121322628, 42794973790514158, 42794971506683339, 42794971506683339, 48960347591007990, 47960329360905269,
    43795598622231521, 49230196256287338, 49964153879927516, 49228838281764024, 48960350178991471, 48960347591007990,
    47494048121322628, 49228838281764024, 45492722049747178, 47960331949014939, 47960329360905269, 43795600901845255,
    43795598622231521, 0, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 1883896737 / 1000000000000
noncomputable def negativeCeiling : ℝ := 176163681 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4295765462068636693362114560, coefficient := (-4295765462068636693362114560) }, { argument := 154160741377473646008008179712, coefficient := (-154160741377473646008008179712) }, { argument := 154158793406294235741088120832, coefficient := (-154158793406294235741088120832) }, { argument := 4297633153209804110430208000, coefficient := (-4297633153209804110430208000) }, { argument := 55843380981526235344971759616, coefficient := (-55843380981526235344971759616) }, { argument := 185868398713841181684928610304, coefficient := (-185868398713841181684928610304) }, { argument := 55792123567022040562502991872, coefficient := (-55792123567022040562502991872) }, { argument := 4295765462068636693362114560, coefficient := (-4295765462068636693362114560) }, { argument := 4295758661744663454690574336, coefficient := (-4295758661744663454690574336) }, { argument := 4295758661744663454690574336, coefficient := (-4295758661744663454690574336) }, { argument := 154160464836000613002083565568, coefficient := (-154160464836000613002083565568) }, { argument := 154158516854831655811702325248, coefficient := (-154158516854831655811702325248) }, { argument := 4297626362491445926986514432, coefficient := (-4297626362491445926986514432) }, { argument := 185868398713841181684928610304, coefficient := (-185868398713841181684928610304) }, { argument := 618270904605998357706482647040, coefficient := (-618270904605998357706482647040) }, { argument := 185693527525505577384868315136, coefficient := (-185693527525505577384868315136) }, { argument := 154160741377473646008008179712, coefficient := (-154160741377473646008008179712) }, { argument := 154160464836000613002083565568, coefficient := (-154160464836000613002083565568) }, { argument := 55792123567022040562502991872, coefficient := (-55792123567022040562502991872) }, { argument := 185693527525505577384868315136, coefficient := (-185693527525505577384868315136) }, { argument := 55740865085024559554824765440, coefficient := (-55740865085024559554824765440) }, { argument := 154158793406294235741088120832, coefficient := (-154158793406294235741088120832) }, { argument := 154158516854831655811702325248, coefficient := (-154158516854831655811702325248) }, { argument := 4297633153209804110430208000, coefficient := (-4297633153209804110430208000) }, { argument := 4297626362491445926986514432, coefficient := (-4297626362491445926986514432) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 633825866798092645105777246208, coefficient := 633825866798092645105777246208 }, { argument := 633824733430136756390925959168, coefficient := 633824733430136756390925959168 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 595007806524778915184806723584, coefficient := 595007806524778915184806723584 }, { argument := 1979665661690690233552559144960, coefficient := 1979665661690690233552559144960 }, { argument := 594453032355104355004392144896, coefficient := 594453032355104355004392144896 }, { argument := 3169126500570573503741758013440, coefficient := (-3169126500570573503741758013440) }, { argument := 17183048247626600296105377792, coefficient := 17183048247626600296105377792 }, { argument := 616642412426948518020183490560, coefficient := 616642412426948518020183490560 }, { argument := 616634620522251783105580892160, coefficient := 616634620522251783105580892160 }, { argument := 17190519031402500074833444864, coefficient := 17190519031402500074833444864 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5
