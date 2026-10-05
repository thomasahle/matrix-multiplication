import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    1, 8447, 720307, 13828403, 720313, 33785
  ]
def positiveCoefficients : Array ℕ := #[
    79228162514264337593543950336, 319118637446399144960720896, 13606214536705542139766898688, 130605573677628100964018814976, 13606327873501131011252027392, 319090303247501927089438720
  ]
def positiveScales : Array ℕ := #[
    0, 13, 19, 23, 19, 15
  ]
def negativeArguments : Array ℕ := #[
    71351809, 6084433229, 116808520141, 6084483911, 285381895, 6084433229,
    518842174249, 9960695479721, 518846496091, 24335571995, 116808520141, 9960695479721,
    191224729530409, 9960778450139, 467192595355, 6084483911, 518846496091, 9960778450139,
    518850817969, 24335774705, 285381895, 24335571995, 467192595355, 24335774705,
    1141426225, 1
  ]
def negativeCoefficients : Array ℕ := #[
    321339980424610802827264, 13700925611442531878305792, 131514701945176669221289984, 13701039737160689074044928, 321311448995071503892480, 13700925611442531878305792,
    584164355652973588828389376, 5607373056352809937065213952, 584169221614478777368182784, 13699709121066234743357440, 131514701945176669221289984, 5607373056352809937065213952,
    53824976291073365934346338304, 5607419764545758383851962368, 131503024896939557524602880, 13701039737160689074044928, 584169221614478777368182784, 5607419764545758383851962368,
    584174087616516362554310656, 13699823236651292777512960, 321311448995071503892480, 13699709121066234743357440, 131503024896939557524602880, 13699823236651292777512960,
    321282920098806995353600, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    26, 32, 36, 32, 28, 32,
    38, 43, 38, 34, 36, 43,
    47, 43, 38, 32, 38, 43,
    38, 34, 28, 34, 38, 34,
    30, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 13044223335689607, 19458252399018136, 23721131217871558, 19458264416302702, 15044095234669214
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    26088446671379216, 32502475734708044, 36765354553881901, 32502487751992610, 28088318570358823, 32502475734708044,
    38916504803890489, 43179383616897029, 38916516821176291, 34502347633687650, 36765354553881901, 43179383616897029,
    47442262435757809, 43179395634181594, 38765226452860651, 32502487751992610, 38916516821176291, 43179395634181594,
    38916528838462093, 34502359650972215, 28088318570358823, 34502347633687650, 38765226452860651, 34502359650972215,
    30088190469338430, 0
  ]

abbrev PositiveTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 5471723 / 125000000000
noncomputable def negativeCeiling : ℝ := 8754757 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 321339980424610802827264, coefficient := (-321339980424610802827264) }, { argument := 13700925611442531878305792, coefficient := (-13700925611442531878305792) }, { argument := 131514701945176669221289984, coefficient := (-131514701945176669221289984) }, { argument := 13701039737160689074044928, coefficient := (-13701039737160689074044928) }, { argument := 321311448995071503892480, coefficient := (-321311448995071503892480) }, { argument := 13700925611442531878305792, coefficient := (-13700925611442531878305792) }, { argument := 584164355652973588828389376, coefficient := (-584164355652973588828389376) }, { argument := 5607373056352809937065213952, coefficient := (-5607373056352809937065213952) }, { argument := 584169221614478777368182784, coefficient := (-584169221614478777368182784) }, { argument := 13699709121066234743357440, coefficient := (-13699709121066234743357440) }, { argument := 131514701945176669221289984, coefficient := (-131514701945176669221289984) }, { argument := 5607373056352809937065213952, coefficient := (-5607373056352809937065213952) }, { argument := 53824976291073365934346338304, coefficient := (-53824976291073365934346338304) }, { argument := 5607419764545758383851962368, coefficient := (-5607419764545758383851962368) }, { argument := 131503024896939557524602880, coefficient := (-131503024896939557524602880) }, { argument := 13701039737160689074044928, coefficient := (-13701039737160689074044928) }, { argument := 584169221614478777368182784, coefficient := (-584169221614478777368182784) }, { argument := 5607419764545758383851962368, coefficient := (-5607419764545758383851962368) }, { argument := 584174087616516362554310656, coefficient := (-584174087616516362554310656) }, { argument := 13699823236651292777512960, coefficient := (-13699823236651292777512960) }, { argument := 321311448995071503892480, coefficient := (-321311448995071503892480) }, { argument := 13699709121066234743357440, coefficient := (-13699709121066234743357440) }, { argument := 131503024896939557524602880, coefficient := (-131503024896939557524602880) }, { argument := 13699823236651292777512960, coefficient := (-13699823236651292777512960) }, { argument := 321282920098806995353600, coefficient := (-321282920098806995353600) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 319118637446399144960720896, coefficient := 319118637446399144960720896 }, { argument := 13606214536705542139766898688, coefficient := 13606214536705542139766898688 }, { argument := 130605573677628100964018814976, coefficient := 130605573677628100964018814976 }, { argument := 13606327873501131011252027392, coefficient := 13606327873501131011252027392 }, { argument := 319090303247501927089438720, coefficient := 319090303247501927089438720 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0
