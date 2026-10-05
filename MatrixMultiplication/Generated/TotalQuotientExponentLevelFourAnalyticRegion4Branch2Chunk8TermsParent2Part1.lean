import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 2,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 80773714589618438258931580010496
def positiveArguments : Array ℕ := #[
    5, 1, 135, 17, 17, 29,
    17, 135, 135, 29, 2451, 29,
    135, 135, 17, 29, 17, 135,
    135, 1, 14986063, 26957997, 14984023, 2034635,
    40925765, 81851465, 1017265, 17141, 1184085, 14339665,
    4736425, 140311
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 618970019642690137449562112, 5222559540735198034730680320, 5261245166962866168321277952, 657655645870358271040159744, 4487532642409503496509325312,
    657655645870358271040159744, 5222559540735198034730680320, 5222559540735198034730680320, 4487532642409503496509325312, 94818469884014595430554796032, 4487532642409503496509325312,
    5222559540735198034730680320, 5222559540735198034730680320, 657655645870358271040159744, 4487532642409503496509325312, 657655645870358271040159744, 5222559540735198034730680320,
    5222559540735198034730680320, 618970019642690137449562112, 141539363242745847920193437696, 509222165912401788247524507648, 141520095987495739767721558016, 19216584257746961178736721920,
    773065843687198502596389109760, 773065229779555729542511329280, 19215592560785558553241845760, 1295137342125897417727410176, 44733466534949630822873825280, 541737226972631608266032414720,
    44734269337251718662560153600, 1325199927155845579157798912
  ]
def positiveScales : Array ℕ := #[
    2, 0, 7, 4, 4, 4,
    4, 7, 7, 4, 11, 4,
    7, 7, 4, 4, 4, 7,
    7, 0, 23, 24, 23, 20,
    25, 26, 19, 14, 20, 23,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    2220367731507, 154137868855, 1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    624977955515024919433838592, 173543812184765095236075520, 158456325028528675187087900672, 792281625142643375935439503360, 1584563250285286751870879006720, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    41, 37, 0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 7076815597050830, 4087462841250339, 4087462841250339, 4857980995002857,
    4087462841250339, 7076815597050830, 7076815597050830, 4857980995002857, 11259154768866839, 4857980995002857,
    7076815597050830, 7076815597050830, 4087462841250339, 4857980995002857, 4087462841250339, 7076815597050830,
    7076815597050830, 0, 23837118085679484, 24684209971354392, 23836921683314593, 20956338576407083,
    25286506048568660, 26286504902894109, 19956264122322516, 14065163657783812, 20175341218430295, 23773507984707740,
    22175367109303441, 17098268591187674
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41013935770398085, 37165430392943814, 0, 2321928094887363, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 32
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 240476157 / 250000000000
noncomputable def negativeCeiling : ℝ := 66817077 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 624977955515024919433838592, coefficient := (-624977955515024919433838592) }, { argument := 173543812184765095236075520, coefficient := (-173543812184765095236075520) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 141539363242745847920193437696, coefficient := 141539363242745847920193437696 }, { argument := 509222165912401788247524507648, coefficient := 509222165912401788247524507648 }, { argument := 141520095987495739767721558016, coefficient := 141520095987495739767721558016 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 19216584257746961178736721920, coefficient := 19216584257746961178736721920 }, { argument := 773065843687198502596389109760, coefficient := 773065843687198502596389109760 }, { argument := 773065229779555729542511329280, coefficient := 773065229779555729542511329280 }, { argument := 19215592560785558553241845760, coefficient := 19215592560785558553241845760 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 1295137342125897417727410176, coefficient := 1295137342125897417727410176 }, { argument := 44733466534949630822873825280, coefficient := 44733466534949630822873825280 }, { argument := 541737226972631608266032414720, coefficient := 541737226972631608266032414720 }, { argument := 44734269337251718662560153600, coefficient := 44734269337251718662560153600 }, { argument := 1325199927155845579157798912, coefficient := 1325199927155845579157798912 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end TermShard2


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8
