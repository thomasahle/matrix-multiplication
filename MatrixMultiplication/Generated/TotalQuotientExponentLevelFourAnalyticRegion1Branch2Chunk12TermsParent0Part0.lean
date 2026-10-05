import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 12, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

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
def constantNumerator : ℤ := (-42644480479219069154746976698368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3008053, 15963, 15779, 15963, 15779, 10165,
    9291, 10165, 9291, 39559209, 21947247, 51663965,
    9524277, 1833867, 38037951, 19107711, 39559209, 21947247,
    1833867, 10761111, 4099235, 4097901, 4099235, 4097901,
    159965, 146211, 159965, 146211, 594260109, 3503816379,
    8161796775, 1520524089, 292771719, 6072652107, 3050492427, 594260109,
    3503816379, 292771719, 4815, 4401, 4815, 4401,
    653224845, 3163591795, 653224845, 113127435, 4707994005, 3204045,
    30118023, 355648995, 24991551, 294249555, 355648995, 3204045,
    24991551, 24991551, 24991551, 24991551, 24991551, 7070535,
    30118023, 752013, 2049617, 1024475
  ]
def negativeCoefficients : Array ℕ := #[
    14205128665895484893993893888, 1206130178656770344739667968, 1192227531731202109230546944, 1206130178656770344739667968, 1192227531731202109230546944, 192011421193479774388879360,
    175502027969367494721798144, 192011421193479774388879360, 175502027969367494721798144, 91217325522673444709203968, 202427624265744867787800576, 953031940188087694854717440,
    175691900306118187136581632, 8457218803555378573344768, 175419086796326078150344704, 176237527325702405109055488, 91217325522673444709203968, 202427624265744867787800576,
    8457218803555378573344768, 50817909904839850675201376256, 38716179938812300195130245120, 38703580665036003981700104192, 38716179938812300195130245120, 38703580665036003981700104192,
    1510826708864485593217761280, 1380923851653707392679411712, 1510826708864485593217761280, 1380923851653707392679411712, 2740541035984435544416321536, 32317002012342355120443359232,
    37639644072513245166541209600, 28048718727693364821516877824, 1350171243103252033333886976, 28005164816625517981731913728, 28135826549829058501086806016, 2740541035984435544416321536,
    32317002012342355120443359232, 1350171243103252033333886976, 181905556920138733631569920, 166265079128874468683808768, 181905556920138733631569920, 166265079128874468683808768,
    3012467884575897607345274880, 29178984098026206352753295360, 3012467884575897607345274880, 521708210290053127329546240, 21711790127698461779841515520, 236416792462594881229946880,
    277789731143548985445187584, 3280282995418503977065512960, 7376203924832960294374342656, 21711784939551691049030123520, 3280282995418503977065512960, 236416792462594881229946880,
    230506372651030009199198208, 230506372651030009199198208, 230506372651030009199198208, 7376203924832960294374342656, 230506372651030009199198208, 521713398436823858140938240,
    277789731143548985445187584, 14205123943529002024348680192, 38716170494079334455839817728, 38703571220303038242409676800
  ]
def negativeScales : Array ℕ := #[
    21, 13, 13, 13, 13, 13,
    13, 13, 13, 25, 24, 25,
    23, 20, 25, 24, 25, 24,
    20, 23, 21, 21, 21, 21,
    17, 17, 17, 17, 29, 31,
    32, 30, 28, 32, 31, 29,
    31, 28, 12, 12, 12, 12,
    29, 31, 29, 26, 32, 21,
    24, 28, 24, 28, 28, 21,
    24, 24, 24, 24, 24, 22,
    24, 19, 20, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21520398555942497, 13962444201746204, 13945718166157771, 13962444201746204, 13945718166157771, 13311322594732096,
    13181618168395820, 13311322594732096, 13181618168395820, 25237510243413052, 24387536647774499, 25622655032926207,
    23183178149268309, 20806457582277085, 25180936198481639, 24187651625847616, 25237510243413052, 24387536647774499,
    20806457582277085, 23359323696701575, 21966923281989994, 21966453714170030, 21966923281989994, 21966453714170030,
    17287396755486615, 17157692329150339, 17287396755486615, 17157692329150339, 29146519299260924, 31706280025114397,
    32926239649523466, 30501921526524646, 28125200958796615, 32499679575737956, 31506395003104000, 29146519299260924,
    31706280025114397, 28125200958796615, 12233320082730822, 12103615656394547, 12233320082730822, 12103615656394547,
    29283004423049081, 31558916311787948, 29283004423049081, 26753373605014064, 32132465337284820, 21611462979507046,
    24844123737837260, 28405878845849419, 24574937103476973, 28132464992545189, 28405878845849419, 21611462979507046,
    24574937103476973, 24574937103476973, 24574937103476973, 24574937103476973, 24574937103476973, 22753387951877488,
    24844123737837260, 19520398076331506, 20966922930047363, 19966453362112831
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 194956171 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14205128665895484893993893888, coefficient := (-14205128665895484893993893888) }, { argument := 1206130178656770344739667968, coefficient := (-1206130178656770344739667968) }, { argument := 1192227531731202109230546944, coefficient := (-1192227531731202109230546944) }, { argument := 1206130178656770344739667968, coefficient := (-1206130178656770344739667968) }, { argument := 1192227531731202109230546944, coefficient := (-1192227531731202109230546944) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 91217325522673444709203968, coefficient := (-91217325522673444709203968) }, { argument := 202427624265744867787800576, coefficient := (-202427624265744867787800576) }, { argument := 953031940188087694854717440, coefficient := (-953031940188087694854717440) }, { argument := 175691900306118187136581632, coefficient := (-175691900306118187136581632) }, { argument := 8457218803555378573344768, coefficient := (-8457218803555378573344768) }, { argument := 175419086796326078150344704, coefficient := (-175419086796326078150344704) }, { argument := 176237527325702405109055488, coefficient := (-176237527325702405109055488) }, { argument := 91217325522673444709203968, coefficient := (-91217325522673444709203968) }, { argument := 202427624265744867787800576, coefficient := (-202427624265744867787800576) }, { argument := 8457218803555378573344768, coefficient := (-8457218803555378573344768) }, { argument := 50817909904839850675201376256, coefficient := (-50817909904839850675201376256) }, { argument := 38716179938812300195130245120, coefficient := (-38716179938812300195130245120) }, { argument := 38703580665036003981700104192, coefficient := (-38703580665036003981700104192) }, { argument := 38716179938812300195130245120, coefficient := (-38716179938812300195130245120) }, { argument := 38703580665036003981700104192, coefficient := (-38703580665036003981700104192) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 37639644072513245166541209600, coefficient := (-37639644072513245166541209600) }, { argument := 28048718727693364821516877824, coefficient := (-28048718727693364821516877824) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 28005164816625517981731913728, coefficient := (-28005164816625517981731913728) }, { argument := 28135826549829058501086806016, coefficient := (-28135826549829058501086806016) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 521708210290053127329546240, coefficient := (-521708210290053127329546240) }, { argument := 21711790127698461779841515520, coefficient := (-21711790127698461779841515520) }, { argument := 236416792462594881229946880, coefficient := (-236416792462594881229946880) }, { argument := 277789731143548985445187584, coefficient := (-277789731143548985445187584) }, { argument := 3280282995418503977065512960, coefficient := (-3280282995418503977065512960) }, { argument := 7376203924832960294374342656, coefficient := (-7376203924832960294374342656) }, { argument := 21711784939551691049030123520, coefficient := (-21711784939551691049030123520) }, { argument := 3280282995418503977065512960, coefficient := (-3280282995418503977065512960) }, { argument := 236416792462594881229946880, coefficient := (-236416792462594881229946880) }, { argument := 230506372651030009199198208, coefficient := (-230506372651030009199198208) }, { argument := 230506372651030009199198208, coefficient := (-230506372651030009199198208) }, { argument := 230506372651030009199198208, coefficient := (-230506372651030009199198208) }, { argument := 7376203924832960294374342656, coefficient := (-7376203924832960294374342656) }, { argument := 230506372651030009199198208, coefficient := (-230506372651030009199198208) }, { argument := 521713398436823858140938240, coefficient := (-521713398436823858140938240) }, { argument := 277789731143548985445187584, coefficient := (-277789731143548985445187584) }, { argument := 14205123943529002024348680192, coefficient := (-14205123943529002024348680192) }, { argument := 38716170494079334455839817728, coefficient := (-38716170494079334455839817728) }, { argument := 38703571220303038242409676800, coefficient := (-38703571220303038242409676800) }] }

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

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-260097762496286424182366954061824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2049617, 1024475, 11771825481, 139851273681, 210045827985, 60690175371,
    11685685941, 242383743873, 121757308353, 11771825481, 139851273681, 11685685941,
    4815, 4401, 4815, 4401, 21534885, 104294235,
    21534885, 4892794245, 7398844635, 269425715, 2532601721, 29906254365,
    2101520577, 462427735, 29906254365, 269425715, 2101520577, 2101520577,
    2101520577, 2101520577, 2101520577, 305799695, 2532601721, 50248065,
    243353215, 50248065, 6161625, 518126375, 259063125, 3080875,
    39559209, 594260109, 653224845, 11771825481, 21534885, 50248065,
    653224845, 653224845, 21534885, 8061225285, 323023275, 594260109,
    653224845, 50248065, 323023275, 50248065, 653224845, 653224845,
    93474171, 4815, 4401, 4815
  ]
def negativeCoefficients : Array ℕ := #[
    38716170494079334455839817728, 38703571220303038242409676800, 13571990745523740119144595456, 322475081746964917494126477312, 242166352036857164974113423360, 279884033214346909523204112384,
    13472678617460798439781564416, 279449430678299786992888578048, 280753238286441154583835181056, 13571990745523740119144595456, 322475081746964917494126477312, 13472678617460798439781564416,
    181905556920138733631569920, 166265079128874468683808768, 181905556920138733631569920, 166265079128874468683808768, 1588994049007066869808496640, 15391112491266570383869870080,
    1588994049007066869808496640, 22564030810708487487073812480, 34121148355745990130574295040, 19880108845924834585880821760, 23359127893961680638409965568, 275836510237207079879096401920,
    620259395992854839079481638912, 34121144320520724006609879040, 275836510237207079879096401920, 19880108845924834585880821760, 19383106124776713721233801216, 19383106124776713721233801216,
    19383106124776713721233801216, 620259395992854839079481638912, 19383106124776713721233801216, 22564034845933753611038228480, 23359127893961680638409965568, 115864149406765292590202880,
    1122268619154854090490511360, 115864149406765292590202880, 227323838906341231951872000, 19115489274927725563346944000, 19115484663241707135959040000, 227328450592359659339776000,
    91217325522673444709203968, 2740541035984435544416321536, 3012467884575897607345274880, 13571990745523740119144595456, 1588994049007066869808496640, 115864149406765292590202880,
    3012467884575897607345274880, 3012467884575897607345274880, 1588994049007066869808496640, 37175839938227835308227952640, 2979363841888250380890931200, 2740541035984435544416321536,
    3012467884575897607345274880, 115864149406765292590202880, 2979363841888250380890931200, 115864149406765292590202880, 3012467884575897607345274880, 3012467884575897607345274880,
    107768381871197702005456896, 181905556920138733631569920, 166265079128874468683808768, 181905556920138733631569920
  ]
def negativeScales : Array ℕ := #[
    20, 19, 33, 37, 37, 35,
    33, 37, 36, 33, 37, 33,
    12, 12, 12, 12, 24, 26,
    24, 32, 32, 28, 31, 34,
    30, 28, 34, 28, 30, 30,
    30, 30, 30, 28, 31, 25,
    27, 25, 22, 28, 27, 21,
    25, 29, 29, 33, 24, 25,
    29, 29, 24, 32, 28, 29,
    29, 25, 28, 25, 29, 29,
    26, 12, 12, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20966922930047363, 19966453362112831, 33454619008262403, 37025102436830685, 37611913174486726, 35820743939304874,
    33444023370596794, 37818501988475512, 36825217415974843, 33454619008262403, 37025102436830685, 33444023370596794,
    12233320082730822, 12103615656394547, 12233320082730822, 12103615656394547, 24360172283571542, 26636084172323563,
    24360172283571542, 32188011468872575, 32784652859051247, 28005312312692326, 31237973069482601, 34799728179684895,
    30968786450933422, 28784652688435657, 34799728179684895, 28005312312692326, 30968786450933422, 30968786450933422,
    30968786450933422, 30968786450933422, 30968786450933422, 28188011726876077, 31237973069482601, 25582564704911453,
    27858476595679667, 25582564704911453, 22554879451134478, 28948728794528472, 27948728446472589, 21554908718584365,
    25237510243413052, 29146519299260924, 29283004423049081, 33454619008262403, 24360172283571542, 25582564704911453,
    29283004423049081, 29283004423049081, 24360172283571542, 32908352000320225, 28267062879180059, 29146519299260924,
    29283004423049081, 25582564704911453, 28267062879180059, 25582564704911453, 29283004423049081, 29283004423049081,
    26478064435435603, 12233320082730822, 12103615656394547, 12233320082730822
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 1656665201 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 38716170494079334455839817728, coefficient := (-38716170494079334455839817728) }, { argument := 38703571220303038242409676800, coefficient := (-38703571220303038242409676800) }, { argument := 13571990745523740119144595456, coefficient := (-13571990745523740119144595456) }, { argument := 322475081746964917494126477312, coefficient := (-322475081746964917494126477312) }, { argument := 242166352036857164974113423360, coefficient := (-242166352036857164974113423360) }, { argument := 279884033214346909523204112384, coefficient := (-279884033214346909523204112384) }, { argument := 13472678617460798439781564416, coefficient := (-13472678617460798439781564416) }, { argument := 279449430678299786992888578048, coefficient := (-279449430678299786992888578048) }, { argument := 280753238286441154583835181056, coefficient := (-280753238286441154583835181056) }, { argument := 13571990745523740119144595456, coefficient := (-13571990745523740119144595456) }, { argument := 322475081746964917494126477312, coefficient := (-322475081746964917494126477312) }, { argument := 13472678617460798439781564416, coefficient := (-13472678617460798439781564416) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 15391112491266570383869870080, coefficient := (-15391112491266570383869870080) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 22564030810708487487073812480, coefficient := (-22564030810708487487073812480) }, { argument := 34121148355745990130574295040, coefficient := (-34121148355745990130574295040) }, { argument := 19880108845924834585880821760, coefficient := (-19880108845924834585880821760) }, { argument := 23359127893961680638409965568, coefficient := (-23359127893961680638409965568) }, { argument := 275836510237207079879096401920, coefficient := (-275836510237207079879096401920) }, { argument := 620259395992854839079481638912, coefficient := (-620259395992854839079481638912) }, { argument := 34121144320520724006609879040, coefficient := (-34121144320520724006609879040) }, { argument := 275836510237207079879096401920, coefficient := (-275836510237207079879096401920) }, { argument := 19880108845924834585880821760, coefficient := (-19880108845924834585880821760) }, { argument := 19383106124776713721233801216, coefficient := (-19383106124776713721233801216) }, { argument := 19383106124776713721233801216, coefficient := (-19383106124776713721233801216) }, { argument := 19383106124776713721233801216, coefficient := (-19383106124776713721233801216) }, { argument := 620259395992854839079481638912, coefficient := (-620259395992854839079481638912) }, { argument := 19383106124776713721233801216, coefficient := (-19383106124776713721233801216) }, { argument := 22564034845933753611038228480, coefficient := (-22564034845933753611038228480) }, { argument := 23359127893961680638409965568, coefficient := (-23359127893961680638409965568) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 1122268619154854090490511360, coefficient := (-1122268619154854090490511360) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 227323838906341231951872000, coefficient := (-227323838906341231951872000) }, { argument := 19115489274927725563346944000, coefficient := (-19115489274927725563346944000) }, { argument := 19115484663241707135959040000, coefficient := (-19115484663241707135959040000) }, { argument := 227328450592359659339776000, coefficient := (-227328450592359659339776000) }, { argument := 91217325522673444709203968, coefficient := (-91217325522673444709203968) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 13571990745523740119144595456, coefficient := (-13571990745523740119144595456) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 37175839938227835308227952640, coefficient := (-37175839938227835308227952640) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 107768381871197702005456896, coefficient := (-107768381871197702005456896) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }] }

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

end TermShard1


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
