import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13

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
    65, 257, 907, 1037, 1043, 1663,
    2885, 3051, 3063, 5757, 21975, 22111,
    41373, 131313, 132081
  ]
def positiveCoefficients : Array ℕ := #[
    82714201664891968447659884150784, 10299661126854363887160713543680, 10299661126854363887160713543680, 752667543885511207138667528192000, 753380597348139586177009423745024, 1587653148623343061037027220783104,
    1266462177790515436432800046120960, 362072702690188022802495853035520, 362944212477844930516024836489216, 1265986808815429850407238782418944, 157030218103271917110404109565952, 157188674428300445785591197466624,
    6555813535405316878515387714502656, 1475782983153201816354943162908672, 1477288318240972838769220497965056
  ]
def positiveScales : Array ℕ := #[
    6, 8, 9, 10, 10, 10,
    11, 11, 11, 12, 14, 14,
    15, 17, 17
  ]
def negativeArguments : Array ℕ := #[
    3, 7, 13, 33, 55, 67,
    307, 309, 369, 739, 751, 771,
    881, 1159, 1519, 1523, 2285, 4581,
    4639, 5491, 5493, 15979, 15985, 2875307207895
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 4436777100798802905238461218816, 4119864450741745554864285417472, 10458117451882892562347801444352, 4357548938284538567644917268480, 5308286888455710618767444672512,
    24323045891879151641217992753152, 24481502216907680316405080653824, 58470383935527081144035435347968, 58549612098041345481628979298304, 59500350048212517532751506702336, 61084913298497804284622385709056,
    139600022350133762839824440492032, 734603522832258938167339507515392, 240695157718335057609186521120768, 241328983018449172309934872723456, 362072702690188022802495853035520, 362944212477844930516024836489216,
    735078891807344524192900771217408, 435041840365825477726149831294976, 435200296690854006401336919195648, 1265986808815429850407238782418944, 1266462177790515436432800046120960, 3277906767702658439257693857251328
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 5, 5, 6,
    8, 8, 8, 9, 9, 9,
    9, 10, 10, 10, 11, 12,
    12, 12, 12, 13, 13, 41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6022367813028454, 8005624549193878, 9824958740462537, 10018200178813225, 10026523442519765, 10699572453282819,
    11494355603532830, 11575066464578481, 11580729651598752, 12491101496916523, 14423575544918127, 14432476654021382,
    15336401952259115, 17002650224689894, 17011063422647224
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2807354922807594, 3700439718214233, 5044394119358454, 5781359713964302, 6066089190457773,
    8262094845370180, 8271463027904375, 8527477006061059, 9529430554146856, 9552669097515714, 9590587049919383,
    9782998209375365, 10178664851006472, 10568906154504419, 10572700226489900, 11157978449945433, 12161446847518008,
    12179598130849837, 12422853195944281, 12423378576518511, 13963889516853203, 13964431136941229, 41386853245532803
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 1365163452823 / 500000000000
noncomputable def negativeCeiling : ℝ := 1299615983849 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-950737950171172051122527404032) }, { argument := 7, coefficient := (-4436777100798802905238461218816) }, { argument := 13, coefficient := (-4119864450741745554864285417472) }, { argument := 33, coefficient := (-10458117451882892562347801444352) }, { argument := 55, coefficient := (-4357548938284538567644917268480) }, { argument := 65, coefficient := 82714201664891968447659884150784 }, { argument := 67, coefficient := (-5308286888455710618767444672512) }, { argument := 257, coefficient := 10299661126854363887160713543680 }, { argument := 307, coefficient := (-24323045891879151641217992753152) }, { argument := 309, coefficient := (-24481502216907680316405080653824) }, { argument := 369, coefficient := (-58470383935527081144035435347968) }, { argument := 739, coefficient := (-58549612098041345481628979298304) }, { argument := 751, coefficient := (-59500350048212517532751506702336) }, { argument := 771, coefficient := (-61084913298497804284622385709056) }, { argument := 881, coefficient := (-139600022350133762839824440492032) }, { argument := 907, coefficient := 10299661126854363887160713543680 }, { argument := 1037, coefficient := 752667543885511207138667528192000 }, { argument := 1043, coefficient := 753380597348139586177009423745024 }, { argument := 1159, coefficient := (-734603522832258938167339507515392) }, { argument := 1519, coefficient := (-240695157718335057609186521120768) }, { argument := 1523, coefficient := (-241328983018449172309934872723456) }, { argument := 1663, coefficient := 1587653148623343061037027220783104 }, { argument := 2285, coefficient := (-362072702690188022802495853035520) }, { argument := 2885, coefficient := 1266462177790515436432800046120960 }, { argument := 3051, coefficient := 362072702690188022802495853035520 }, { argument := 3063, coefficient := 362944212477844930516024836489216 }, { argument := 4581, coefficient := (-362944212477844930516024836489216) }, { argument := 4639, coefficient := (-735078891807344524192900771217408) }, { argument := 5491, coefficient := (-435041840365825477726149831294976) }, { argument := 5493, coefficient := (-435200296690854006401336919195648) }, { argument := 5757, coefficient := 1265986808815429850407238782418944 }, { argument := 15979, coefficient := (-1265986808815429850407238782418944) }, { argument := 15985, coefficient := (-1266462177790515436432800046120960) }, { argument := 21975, coefficient := 157030218103271917110404109565952 }, { argument := 22111, coefficient := 157188674428300445785591197466624 }, { argument := 41373, coefficient := 6555813535405316878515387714502656 }, { argument := 131313, coefficient := 1475782983153201816354943162908672 }, { argument := 132081, coefficient := 1477288318240972838769220497965056 }, { argument := 2875307207895, coefficient := (-3277906767702658439257693857251328) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13
