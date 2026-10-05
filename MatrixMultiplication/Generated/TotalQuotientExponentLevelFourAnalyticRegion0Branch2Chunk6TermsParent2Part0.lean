import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6

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
def constantNumerator : ℤ := (-5204641056640460852020534837248)
def positiveArguments : Array ℕ := #[
    7, 12582621, 12583203, 48007725, 86196853, 48034025,
    42855, 48961551, 48973005, 339345
  ]
def positiveCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 475357981416413905027206217728, 475379968754758146095321186304, 453420142917646276533367603200, 1628212518144167306588430794752, 453668539394645219871608012800,
    12952128999896233320508293120, 462428774783425520964565204992, 462536954754815098797120552960, 12820091633035198040333352960
  ]
def positiveScales : Array ℕ := #[
    2, 23, 23, 25, 26, 25,
    15, 25, 25, 18
  ]
def negativeArguments : Array ℕ := #[
    5751771199533, 410709752614863, 410805836008047, 1423283803821, 72027510078573, 517247890336011,
    144133061500443, 5751771199533, 5752030267347, 5752030267347, 410728764207153, 410824847046033,
    1423348377939, 517247890336011, 464376407975053, 517532920366273, 410709752614863, 410728764207153,
    144133061500443, 517532920366273, 36052807726921, 410805836008047, 410824847046033, 1423283803821,
    1423348377939, 3, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    3237959328867146199566647296, 115604518052107850122556080128, 115631563122966597326006648832, 3204950204265358865473732608, 40547883443785750983292747776, 145592337885964644915364233216,
    40569850129072742368026820608, 3237959328867146199566647296, 3238105171080970460687499264, 3238105171080970460687499264, 115609869339604910359726522368, 115636914254440952072553627648,
    3205095612252240154692943872, 145592337885964644915364233216, 522841354479024529438589059072, 145672566707094478940262105088, 115604518052107850122556080128, 115609869339604910359726522368,
    40569850129072742368026820608, 145672566707094478940262105088, 40591852861155388627515080704, 115631563122966597326006648832, 115636914254440952072553627648, 3204950204265358865473732608,
    3205095612252240154692943872, 950737950171172051122527404032, 2535301200456458802993406410752, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    42, 48, 48, 40, 46, 48,
    47, 42, 42, 42, 48, 48,
    40, 48, 48, 48, 48, 48,
    47, 48, 45, 48, 48, 40,
    40, 1, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 23584929135700846, 23584995864969392, 25516763235096913, 26361131862479829, 25517553368148919,
    15387175916544889, 25545145924541181, 25545483387225417, 18372393230663408
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    42387143426410205, 48545112534036891, 48545450005504055, 40372360503633531, 46033613266113637, 48877849187217777,
    47034394629874855, 42387143426410205, 42387208405947909, 42387208405947909, 48545179314275120, 48545516768176862,
    40372425956950908, 48877849187217777, 48722288008409363, 48878643967019620, 48545112534036891, 48545179314275120,
    47034394629874855, 48878643967019620, 45035176851835947, 48545450005504055, 48545516768176862, 40372360503633531,
    40372425956950908, 1584962500724866, 0, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 1429788079 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1329386971 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3237959328867146199566647296, coefficient := (-3237959328867146199566647296) }, { argument := 115604518052107850122556080128, coefficient := (-115604518052107850122556080128) }, { argument := 115631563122966597326006648832, coefficient := (-115631563122966597326006648832) }, { argument := 3204950204265358865473732608, coefficient := (-3204950204265358865473732608) }, { argument := 40547883443785750983292747776, coefficient := (-40547883443785750983292747776) }, { argument := 145592337885964644915364233216, coefficient := (-145592337885964644915364233216) }, { argument := 40569850129072742368026820608, coefficient := (-40569850129072742368026820608) }, { argument := 3237959328867146199566647296, coefficient := (-3237959328867146199566647296) }, { argument := 3238105171080970460687499264, coefficient := (-3238105171080970460687499264) }, { argument := 3238105171080970460687499264, coefficient := (-3238105171080970460687499264) }, { argument := 115609869339604910359726522368, coefficient := (-115609869339604910359726522368) }, { argument := 115636914254440952072553627648, coefficient := (-115636914254440952072553627648) }, { argument := 3205095612252240154692943872, coefficient := (-3205095612252240154692943872) }, { argument := 145592337885964644915364233216, coefficient := (-145592337885964644915364233216) }, { argument := 522841354479024529438589059072, coefficient := (-522841354479024529438589059072) }, { argument := 145672566707094478940262105088, coefficient := (-145672566707094478940262105088) }, { argument := 115604518052107850122556080128, coefficient := (-115604518052107850122556080128) }, { argument := 115609869339604910359726522368, coefficient := (-115609869339604910359726522368) }, { argument := 40569850129072742368026820608, coefficient := (-40569850129072742368026820608) }, { argument := 145672566707094478940262105088, coefficient := (-145672566707094478940262105088) }, { argument := 40591852861155388627515080704, coefficient := (-40591852861155388627515080704) }, { argument := 115631563122966597326006648832, coefficient := (-115631563122966597326006648832) }, { argument := 115636914254440952072553627648, coefficient := (-115636914254440952072553627648) }, { argument := 3204950204265358865473732608, coefficient := (-3204950204265358865473732608) }, { argument := 3205095612252240154692943872, coefficient := (-3205095612252240154692943872) }, { argument := 2218388550399401452619230609408, coefficient := 2218388550399401452619230609408 }, { argument := 475357981416413905027206217728, coefficient := 475357981416413905027206217728 }, { argument := 475379968754758146095321186304, coefficient := 475379968754758146095321186304 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 453420142917646276533367603200, coefficient := 453420142917646276533367603200 }, { argument := 1628212518144167306588430794752, coefficient := 1628212518144167306588430794752 }, { argument := 453668539394645219871608012800, coefficient := 453668539394645219871608012800 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 12952128999896233320508293120, coefficient := 12952128999896233320508293120 }, { argument := 462428774783425520964565204992, coefficient := 462428774783425520964565204992 }, { argument := 462536954754815098797120552960, coefficient := 462536954754815098797120552960 }, { argument := 12820091633035198040333352960, coefficient := 12820091633035198040333352960 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6
