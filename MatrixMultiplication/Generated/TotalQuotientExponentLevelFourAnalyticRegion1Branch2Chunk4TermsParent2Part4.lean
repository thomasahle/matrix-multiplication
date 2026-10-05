import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

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
def constantNumerator : ℤ := (-66756057180939753957436906486628352)
def positiveArguments : Array ℕ := #[
    136521, 154251, 75196503, 153554797, 2032951443, 31955,
    28303, 1324763, 360635, 1016476035, 1324763, 31955,
    31955, 13695, 31955, 360635, 13695, 76777085,
    28303, 2152459, 3507, 19009525, 5649, 175,
    5649, 3773, 2181131, 3507, 21
  ]
def positiveCoefficients : Array ℕ := #[
    10562800756454962531843958636544, 5967296531244037274483275333632, 710210890792413449841253810176, 725142026636652348251110899712, 9600341755724680018081326563328, 618099593052567604443773665280,
    547459639560845592507342389248, 25624643129122159829940445380608, 6975695407307548678722588508160, 9600344716648464777348875550720, 25624643129122159829940445380608, 618099593052567604443773665280,
    618099593052567604443773665280, 529799651187915089523234570240, 618099593052567604443773665280, 6975695407307548678722588508160, 529799651187915089523234570240, 725139065712867588983561912320,
    547459639560845592507342389248, 20329400474702227334053756928, 135670491180432144502225895424, 359079774861090369723537817600, 218535102560097286653286023168, 6769984589841923378354585600,
    218535102560097286653286023168, 145960867756991868037324865536, 20600199858295904269187940352, 135670491180432144502225895424, 6499185206248246443220402176
  ]
def positiveScales : Array ℕ := #[
    17, 17, 26, 27, 30, 14,
    14, 20, 18, 29, 20, 14,
    14, 13, 14, 18, 13, 26,
    14, 21, 11, 24, 12, 7,
    12, 11, 21, 11, 4
  ]
def negativeArguments : Array ℕ := #[
    8781, 571, 1
  ]
def negativeCoefficients : Array ℕ := #[
    695702495037755148408909427900416, 90478561591289873531827191283712, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    13, 9, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17058763361593589, 17234920316747416, 26164162235398132, 27194178341422528, 30920928610450640, 14963754066119267,
    14788667360339376, 20337302854050966, 18460179893048682, 29920929055404527, 20337302854050966, 14963754066119267,
    14963754066119267, 13741361645581203, 14963754066119267, 18460179893048682, 13741361645581203, 26194172450550637,
    14788667360339376, 21037554326779035, 11776021715228447, 24180219147344447, 12463779785335379, 7451211111832325,
    12463779785335379, 11881496384617007, 21056644991010644, 11776021715228447, 4392317422778759
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13100169531129907, 9157346935362843, 0
  ]

abbrev PositiveTerm := Fin 29
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 5565936937 / 200000000000
noncomputable def negativeCeiling : ℝ := 119676855901 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10562800756454962531843958636544, coefficient := 10562800756454962531843958636544 }, { argument := 5967296531244037274483275333632, coefficient := 5967296531244037274483275333632 }, { argument := 710210890792413449841253810176, coefficient := 710210890792413449841253810176 }, { argument := 695702495037755148408909427900416, coefficient := (-695702495037755148408909427900416) }, { argument := 725142026636652348251110899712, coefficient := 725142026636652348251110899712 }, { argument := 9600341755724680018081326563328, coefficient := 9600341755724680018081326563328 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 547459639560845592507342389248, coefficient := 547459639560845592507342389248 }, { argument := 25624643129122159829940445380608, coefficient := 25624643129122159829940445380608 }, { argument := 6975695407307548678722588508160, coefficient := 6975695407307548678722588508160 }, { argument := 9600344716648464777348875550720, coefficient := 9600344716648464777348875550720 }, { argument := 25624643129122159829940445380608, coefficient := 25624643129122159829940445380608 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 529799651187915089523234570240, coefficient := 529799651187915089523234570240 }, { argument := 618099593052567604443773665280, coefficient := 618099593052567604443773665280 }, { argument := 6975695407307548678722588508160, coefficient := 6975695407307548678722588508160 }, { argument := 529799651187915089523234570240, coefficient := 529799651187915089523234570240 }, { argument := 725139065712867588983561912320, coefficient := 725139065712867588983561912320 }, { argument := 547459639560845592507342389248, coefficient := 547459639560845592507342389248 }, { argument := 90478561591289873531827191283712, coefficient := (-90478561591289873531827191283712) }, { argument := 20329400474702227334053756928, coefficient := 20329400474702227334053756928 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 359079774861090369723537817600, coefficient := 359079774861090369723537817600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 20600199858295904269187940352, coefficient := 20600199858295904269187940352 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
