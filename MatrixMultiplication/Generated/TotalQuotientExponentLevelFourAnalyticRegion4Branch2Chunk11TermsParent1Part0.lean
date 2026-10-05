import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11

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
def constantNumerator : ℤ := 225061635762129647029247279104
def positiveArguments : Array ℕ := #[
    1, 1048581, 1048571, 2955129, 21734553, 5909621,
    89091, 8210441, 2052607, 178165
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 79228540303582967165161046016, 79227784724945708021926854656, 55820808568624367162816987136, 205277049214707791976544075776, 55814792273725191234814738432,
    1682881409301358246933561344, 77545422775957465435966799872, 77545299994428910825191243776, 1682720848840940678996295680
  ]
def positiveScales : Array ℕ := #[
    0, 20, 19, 21, 24, 22,
    16, 22, 20, 17
  ]
def negativeArguments : Array ℕ := #[
    93419129871, 8609312434221, 2152324700667, 186820433865, 8726194941005, 64254715134307,
    17450570065411, 93419129871, 93418238961, 93418238961, 8609230329811, 2152304174597,
    186818652215, 64254715134307, 59035726858723, 64247667775249, 8609312434221, 8609230329811,
    17450570065411, 64247667775249, 4362187538619, 2152324700667, 2152304174597, 186820433865,
    186818652215, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    420722358476311572057686016, 19386448135336936727598071808, 19386417439808431087014641664, 420682218169804195910123520, 4912411035584053165749698560, 18086094445978898440118075392,
    4911898802749231975540719616, 420722358476311572057686016, 420718346174367551409094656, 420718346174367551409094656, 19386263252641795990385328128, 19386232557406024325580980224,
    420678206250666143588024320, 18086094445978898440118075392, 66468319370622821288642609152, 18084110790752176259511353344, 19386448135336936727598071808, 19386263252641795990385328128,
    4911898802749231975540719616, 18084110790752176259511353344, 4911386543361187382355296256, 19386417439808431087014641664, 19386232557406024325580980224, 420682218169804195910123520,
    420678206250666143588024320, 158456325028528675187087900672, 316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    36, 42, 40, 37, 42, 45,
    43, 36, 36, 36, 42, 40,
    37, 45, 45, 45, 42, 42,
    43, 45, 41, 40, 40, 37,
    37, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 20000006879289633, 19999993119218142, 21494789678947997, 24373487089189637, 22494634178753463,
    16442992077164403, 22969028282700040, 20969025998407381, 17442854425854227
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36442998956454075, 42969035177198367, 40969032892905134, 37442861305143899, 42988489861851073, 45868867561929965,
    43988339419526249, 36442998956454075, 36442985197842006, 36442985197842006, 42969021418583043, 40969019134289810,
    37442847546531830, 45868867561929965, 45746653533346992, 45868709320655179, 42969035177198367, 42969021418583043,
    43988339419526249, 45868709320655179, 41988188953712097, 40969032892905134, 40969019134289810, 37442861305143899,
    37442847546531830, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 84813437 / 500000000000
noncomputable def negativeCeiling : ℝ := 16661391 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 420722358476311572057686016, coefficient := (-420722358476311572057686016) }, { argument := 19386448135336936727598071808, coefficient := (-19386448135336936727598071808) }, { argument := 19386417439808431087014641664, coefficient := (-19386417439808431087014641664) }, { argument := 420682218169804195910123520, coefficient := (-420682218169804195910123520) }, { argument := 4912411035584053165749698560, coefficient := (-4912411035584053165749698560) }, { argument := 18086094445978898440118075392, coefficient := (-18086094445978898440118075392) }, { argument := 4911898802749231975540719616, coefficient := (-4911898802749231975540719616) }, { argument := 420722358476311572057686016, coefficient := (-420722358476311572057686016) }, { argument := 420718346174367551409094656, coefficient := (-420718346174367551409094656) }, { argument := 420718346174367551409094656, coefficient := (-420718346174367551409094656) }, { argument := 19386263252641795990385328128, coefficient := (-19386263252641795990385328128) }, { argument := 19386232557406024325580980224, coefficient := (-19386232557406024325580980224) }, { argument := 420678206250666143588024320, coefficient := (-420678206250666143588024320) }, { argument := 18086094445978898440118075392, coefficient := (-18086094445978898440118075392) }, { argument := 66468319370622821288642609152, coefficient := (-66468319370622821288642609152) }, { argument := 18084110790752176259511353344, coefficient := (-18084110790752176259511353344) }, { argument := 19386448135336936727598071808, coefficient := (-19386448135336936727598071808) }, { argument := 19386263252641795990385328128, coefficient := (-19386263252641795990385328128) }, { argument := 4911898802749231975540719616, coefficient := (-4911898802749231975540719616) }, { argument := 18084110790752176259511353344, coefficient := (-18084110790752176259511353344) }, { argument := 4911386543361187382355296256, coefficient := (-4911386543361187382355296256) }, { argument := 19386417439808431087014641664, coefficient := (-19386417439808431087014641664) }, { argument := 19386232557406024325580980224, coefficient := (-19386232557406024325580980224) }, { argument := 420682218169804195910123520, coefficient := (-420682218169804195910123520) }, { argument := 420678206250666143588024320, coefficient := (-420678206250666143588024320) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 79228540303582967165161046016, coefficient := 79228540303582967165161046016 }, { argument := 79227784724945708021926854656, coefficient := 79227784724945708021926854656 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 55820808568624367162816987136, coefficient := 55820808568624367162816987136 }, { argument := 205277049214707791976544075776, coefficient := 205277049214707791976544075776 }, { argument := 55814792273725191234814738432, coefficient := 55814792273725191234814738432 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1682881409301358246933561344, coefficient := 1682881409301358246933561344 }, { argument := 77545422775957465435966799872, coefficient := 77545422775957465435966799872 }, { argument := 77545299994428910825191243776, coefficient := 77545299994428910825191243776 }, { argument := 1682720848840940678996295680, coefficient := 1682720848840940678996295680 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11
