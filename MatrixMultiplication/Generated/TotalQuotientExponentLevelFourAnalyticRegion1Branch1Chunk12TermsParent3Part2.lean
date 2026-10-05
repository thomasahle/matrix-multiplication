import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-17934168255496837163429498183483392)
def positiveArguments : Array ℕ := #[
    685, 20961, 685, 411, 335787, 21509,
    11919, 20961, 685, 21509, 685, 20961,
    685, 411, 3, 45, 79, 3,
    25, 3, 79, 157, 25, 2423,
    155, 45, 79, 3, 155, 3,
    79, 79, 3, 9, 41, 1,
    429, 19, 1, 19, 37, 699,
    37, 429, 699, 9, 37, 37,
    41, 2163, 147111007671, 147111029321, 125765754679, 458542501455,
    62885316925, 3618450817, 8909563743, 35638259493
  ]
def positiveCoefficients : Array ℕ := #[
    13249826982976335754779688960, 405444705679075874096258482176, 423994463455242744152950046720, 254396678073145646491770028032, 6495065187054999786993003528192, 416044567265456942700082233344,
    230546989503788242133166587904, 405444705679075874096258482176, 13249826982976335754779688960, 416044567265456942700082233344, 13249826982976335754779688960, 405444705679075874096258482176,
    423994463455242744152950046720, 15899792379571602905735626752, 232113757366008801543585792, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792,
    3868562622766813359059763200, 232113757366008801543585792, 6112328943971565107314425856, 6073643317743896973723828224, 3868562622766813359059763200, 93735272349639887690018062336,
    5996272065288560706542632960, 3481706360490132023153786880, 6112328943971565107314425856, 232113757366008801543585792, 5996272065288560706542632960, 232113757366008801543585792,
    6112328943971565107314425856, 6112328943971565107314425856, 232113757366008801543585792, 1392682544196052809261514752, 1586110675334393477214502912, 1237940039285380274899124224,
    16596133651669629310366384128, 1470053796651389076442710016, 1237940039285380274899124224, 1470053796651389076442710016, 1431368170423720942852112384, 54082505466280050759655489536,
    1431368170423720942852112384, 16596133651669629310366384128, 54082505466280050759655489536, 1392682544196052809261514752, 1431368170423720942852112384, 1431368170423720942852112384,
    1586110675334393477214502912, 171370515518353762214835564576768, 694712091886709667125080690262016, 694712194125944021252899566780416, 593911984588915855881457666883584, 2165405739842297522976531865927680,
    593935025822510445451164621209600, 17087650858113084227998430789632, 673187603150941145459509897986048, 673187688550216621674173942464512
  ]
def positiveScales : Array ℕ := #[
    9, 14, 9, 8, 18, 14,
    13, 14, 9, 14, 9, 14,
    9, 8, 1, 5, 6, 1,
    4, 1, 6, 7, 4, 11,
    7, 5, 6, 1, 7, 1,
    6, 6, 1, 3, 5, 0,
    8, 4, 0, 4, 5, 9,
    5, 8, 9, 3, 5, 5,
    5, 11, 37, 37, 36, 38,
    35, 31, 33, 35
  ]
def negativeArguments : Array ℕ := #[
    137, 1, 1, 2163, 17537, 10581
  ]
def negativeCoefficients : Array ℕ := #[
    10854258264454214250315521196032, 158456325028528675187087900672, 158456325028528675187087900672, 171370515518353762214835564576768, 1389424286012653688377980257042432, 3353252750253723824309154154020864
  ]
def negativeScales : Array ℕ := #[
    7, 0, 0, 11, 14, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9419960177847887, 14355419925653178, 9419960177847887, 8682994583678684, 18357186851827365, 14392652831852153,
    13540975578809191, 14355419925653178, 9419960177847887, 14392652831852153, 9419960177847887, 14355419925653178,
    9419960177847887, 8682994583678684, 1584962500720924, 5491853096329661, 6303780748177102, 1584962500720924,
    4643856189773592, 1584962500720924, 6303780748177102, 7294620748891626, 4643856189773592, 11242578689451346,
    7276124405274237, 5491853096329661, 6303780748177102, 1584962500720924, 7276124405274237, 1584962500720924,
    6303780748177102, 6303780748177102, 1584962500720924, 3169925001442312, 5357552004618083, 0,
    8744833837487090, 4247927513443585, 0, 4247927513443585, 5209453365628949, 9449148645375433,
    5209453365628949, 8744833837487090, 9449148645375433, 3169925001442312, 5209453365628949, 5209453365628949,
    5357552004618083, 11078817949961978, 37098114244930252, 37098114457248459, 36871948181391759, 38738264504498805,
    35872004150675775, 31752725016196215, 33052707645865989, 35052707828883476
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7098032082960527, 0, 0, 11078817949961979, 14098114351089360, 13369188361147410
  ]

abbrev PositiveTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 2733467962769 / 1000000000000
noncomputable def negativeCeiling : ℝ := 799190591043 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13249826982976335754779688960, coefficient := 13249826982976335754779688960 }, { argument := 405444705679075874096258482176, coefficient := 405444705679075874096258482176 }, { argument := 423994463455242744152950046720, coefficient := 423994463455242744152950046720 }, { argument := 254396678073145646491770028032, coefficient := 254396678073145646491770028032 }, { argument := 6495065187054999786993003528192, coefficient := 6495065187054999786993003528192 }, { argument := 416044567265456942700082233344, coefficient := 416044567265456942700082233344 }, { argument := 230546989503788242133166587904, coefficient := 230546989503788242133166587904 }, { argument := 405444705679075874096258482176, coefficient := 405444705679075874096258482176 }, { argument := 13249826982976335754779688960, coefficient := 13249826982976335754779688960 }, { argument := 416044567265456942700082233344, coefficient := 416044567265456942700082233344 }, { argument := 13249826982976335754779688960, coefficient := 13249826982976335754779688960 }, { argument := 405444705679075874096258482176, coefficient := 405444705679075874096258482176 }, { argument := 423994463455242744152950046720, coefficient := 423994463455242744152950046720 }, { argument := 15899792379571602905735626752, coefficient := 15899792379571602905735626752 }, { argument := 10854258264454214250315521196032, coefficient := (-10854258264454214250315521196032) }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3868562622766813359059763200, coefficient := 3868562622766813359059763200 }, { argument := 93735272349639887690018062336, coefficient := 93735272349639887690018062336 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 6112328943971565107314425856, coefficient := 6112328943971565107314425856 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1586110675334393477214502912, coefficient := 1586110675334393477214502912 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 16596133651669629310366384128, coefficient := 16596133651669629310366384128 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 54082505466280050759655489536, coefficient := 54082505466280050759655489536 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 16596133651669629310366384128, coefficient := 16596133651669629310366384128 }, { argument := 54082505466280050759655489536, coefficient := 54082505466280050759655489536 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1586110675334393477214502912, coefficient := 1586110675334393477214502912 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 171370515518353762214835564576768, coefficient := 171370515518353762214835564576768 }, { argument := 171370515518353762214835564576768, coefficient := (-171370515518353762214835564576768) }, { argument := 694712091886709667125080690262016, coefficient := 694712091886709667125080690262016 }, { argument := 694712194125944021252899566780416, coefficient := 694712194125944021252899566780416 }, { argument := 1389424286012653688377980257042432, coefficient := (-1389424286012653688377980257042432) }, { argument := 593911984588915855881457666883584, coefficient := 593911984588915855881457666883584 }, { argument := 2165405739842297522976531865927680, coefficient := 2165405739842297522976531865927680 }, { argument := 593935025822510445451164621209600, coefficient := 593935025822510445451164621209600 }, { argument := 3353252750253723824309154154020864, coefficient := (-3353252750253723824309154154020864) }, { argument := 17087650858113084227998430789632, coefficient := 17087650858113084227998430789632 }, { argument := 673187603150941145459509897986048, coefficient := 673187603150941145459509897986048 }, { argument := 673187688550216621674173942464512, coefficient := 673187688550216621674173942464512 }] }

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

end TermShard4


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-135580035670902835563483871662047232)
def positiveArguments : Array ℕ := #[
    3618480123, 1789461, 171288453, 28447220655, 2740617905, 1789461
  ]
def positiveCoefficients : Array ℕ := #[
    17087789251785231205821063364608, 67603925190419185549965262848, 12942189589596680469005476036608, 134338201351969074995574740090880, 12942202136924425453652808826880, 67603925190419185549965262848
  ]
def positiveScales : Array ℕ := #[
    31, 20, 27, 34, 31, 20
  ]
def negativeArguments : Array ℕ := #[
    17425, 253
  ]
def negativeCoefficients : Array ℕ := #[
    1380550731811056082567503334604800, 160357800928871019289332955480064
  ]
def negativeScales : Array ℕ := #[
    14, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    31752736700602549, 20771093670910820, 27351852657974803, 34727568654362842, 31351854056653026, 20771093670910820
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14088871035643148, 7982993592700323
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 4491619581 / 62500000000
noncomputable def negativeCeiling : ℝ := 249534756497 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17087789251785231205821063364608, coefficient := 17087789251785231205821063364608 }, { argument := 1380550731811056082567503334604800, coefficient := (-1380550731811056082567503334604800) }, { argument := 67603925190419185549965262848, coefficient := 67603925190419185549965262848 }, { argument := 12942189589596680469005476036608, coefficient := 12942189589596680469005476036608 }, { argument := 134338201351969074995574740090880, coefficient := 134338201351969074995574740090880 }, { argument := 12942202136924425453652808826880, coefficient := 12942202136924425453652808826880 }, { argument := 67603925190419185549965262848, coefficient := 67603925190419185549965262848 }, { argument := 160357800928871019289332955480064, coefficient := (-160357800928871019289332955480064) }] }

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

end TermShard5


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12
