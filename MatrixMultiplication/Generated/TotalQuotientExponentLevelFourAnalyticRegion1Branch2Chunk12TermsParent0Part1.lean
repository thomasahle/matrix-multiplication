import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-195678095862094820467503695659008)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4401, 412485, 377019, 412485, 377019, 653224845,
    3163591795, 653224845, 4815, 4401, 4815, 4401,
    653224845, 3163591795, 653224845, 57919275, 4870387925, 2435193375,
    28960225, 159965, 146211, 159965, 146211, 21534885,
    104294235, 21534885, 412485, 377019, 412485, 377019,
    8061225285, 39040808635, 8061225285, 683940375, 57512027625, 28756006875,
    341977125, 323023275, 1564413525, 323023275, 48060675, 4041385725,
    2020692375, 24030825, 21947247, 3503816379, 139851273681, 3503816379,
    87778971, 127705, 126233, 127705, 126233, 594260109,
    3503816379, 8161796775, 1520524089, 292771719, 6072652107, 3050492427,
    594260109, 3503816379, 292771719, 4892793075
  ]
def negativeCoefficients : Array ℕ := #[
    166265079128874468683808768, 7791621354745942423885578240, 7121687556020123075289808896, 7791621354745942423885578240, 7121687556020123075289808896, 3012467884575897607345274880,
    29178984098026206352753295360, 3012467884575897607345274880, 181905556920138733631569920, 166265079128874468683808768, 181905556920138733631569920, 166265079128874468683808768,
    3012467884575897607345274880, 29178984098026206352753295360, 3012467884575897607345274880, 267105510714950947543449600, 22460699898040077536932659200, 22460694479309005884751872000,
    267110929446022599724236800, 1510826708864485593217761280, 1380923851653707392679411712, 1510826708864485593217761280, 1380923851653707392679411712, 1588994049007066869808496640,
    15391112491266570383869870080, 1588994049007066869808496640, 7791621354745942423885578240, 7121687556020123075289808896, 7791621354745942423885578240, 7121687556020123075289808896,
    37175839938227835308227952640, 360087902660257469605955502080, 37175839938227835308227952640, 3154118264825484593332224000, 265227413689622192191438848000, 265227349702478686511431680000,
    3154182251968990273339392000, 2979363841888250380890931200, 28858335921124819469756006400, 2979363841888250380890931200, 7092503773877846436898406400, 596403265377745037576424652800,
    596403121493141262641922048000, 7092647658481621371401011200, 202427624265744867787800576, 32317002012342355120443359232, 322475081746964917494126477312, 32317002012342355120443359232,
    202404526636321574215483392, 1206139623389736084030095360, 1192236976464167848520974336, 1206139623389736084030095360, 1192236976464167848520974336, 2740541035984435544416321536,
    32317002012342355120443359232, 37639644072513245166541209600, 28048718727693364821516877824, 1350171243103252033333886976, 28005164816625517981731913728, 28135826549829058501086806016,
    2740541035984435544416321536, 32317002012342355120443359232, 1350171243103252033333886976, 22564025415035845927029964800
  ]
def negativeScales : Array ℕ := #[
    12, 18, 18, 18, 18, 29,
    31, 29, 12, 12, 12, 12,
    29, 31, 29, 25, 32, 31,
    24, 17, 17, 17, 17, 24,
    26, 24, 18, 18, 18, 18,
    32, 35, 32, 29, 35, 34,
    28, 28, 30, 28, 25, 31,
    30, 24, 24, 31, 37, 31,
    26, 16, 16, 16, 16, 29,
    31, 32, 30, 28, 32, 31,
    29, 31, 28, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12103615656394547, 18653982131227114, 18524277704867867, 18653982131227114, 18524277704867867, 29283004423049081,
    31558916311787948, 29283004423049081, 12233320082730822, 12103615656394547, 12233320082730822, 12103615656394547,
    29283004423049081, 31558916311787948, 29283004423049081, 25787540208423241, 32181389541116234, 31181389193060411,
    24787569475873430, 17287396755486615, 17157692329150339, 17287396755486615, 17157692329150339, 24360172283571542,
    26636084172323563, 24360172283571542, 18653982131227114, 18524277704867867, 18653982131227114, 18524277704867867,
    32908352000320225, 35184263883988115, 32908352000320225, 29349295317483044, 35743144650869513, 34743144302813688,
    28349324584932930, 28267062879180059, 30542974767918262, 28267062879180059, 25518353575108318, 31912202913727760,
    30912202565671903, 24518382842558204, 24387536647774499, 31706280025114397, 37025102436830685, 31706280025114397,
    26387372022334611, 16962455498884122, 16945729595031304, 16962455498884122, 16945729595031304, 29146519299260924,
    31706280025114397, 32926239649523466, 30501921526524646, 28125200958796615, 32499679575737956, 31506395003104000,
    29146519299260924, 31706280025114397, 28125200958796615, 32188011123884964
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
noncomputable def negativeCeiling : ℝ := 596964273 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 267105510714950947543449600, coefficient := (-267105510714950947543449600) }, { argument := 22460699898040077536932659200, coefficient := (-22460699898040077536932659200) }, { argument := 22460694479309005884751872000, coefficient := (-22460694479309005884751872000) }, { argument := 267110929446022599724236800, coefficient := (-267110929446022599724236800) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 15391112491266570383869870080, coefficient := (-15391112491266570383869870080) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 37175839938227835308227952640, coefficient := (-37175839938227835308227952640) }, { argument := 360087902660257469605955502080, coefficient := (-360087902660257469605955502080) }, { argument := 37175839938227835308227952640, coefficient := (-37175839938227835308227952640) }, { argument := 3154118264825484593332224000, coefficient := (-3154118264825484593332224000) }, { argument := 265227413689622192191438848000, coefficient := (-265227413689622192191438848000) }, { argument := 265227349702478686511431680000, coefficient := (-265227349702478686511431680000) }, { argument := 3154182251968990273339392000, coefficient := (-3154182251968990273339392000) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 28858335921124819469756006400, coefficient := (-28858335921124819469756006400) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 7092503773877846436898406400, coefficient := (-7092503773877846436898406400) }, { argument := 596403265377745037576424652800, coefficient := (-596403265377745037576424652800) }, { argument := 596403121493141262641922048000, coefficient := (-596403121493141262641922048000) }, { argument := 7092647658481621371401011200, coefficient := (-7092647658481621371401011200) }, { argument := 202427624265744867787800576, coefficient := (-202427624265744867787800576) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 322475081746964917494126477312, coefficient := (-322475081746964917494126477312) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 202404526636321574215483392, coefficient := (-202404526636321574215483392) }, { argument := 1206139623389736084030095360, coefficient := (-1206139623389736084030095360) }, { argument := 1192236976464167848520974336, coefficient := (-1192236976464167848520974336) }, { argument := 1206139623389736084030095360, coefficient := (-1206139623389736084030095360) }, { argument := 1192236976464167848520974336, coefficient := (-1192236976464167848520974336) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 37639644072513245166541209600, coefficient := (-37639644072513245166541209600) }, { argument := 28048718727693364821516877824, coefficient := (-28048718727693364821516877824) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 28005164816625517981731913728, coefficient := (-28005164816625517981731913728) }, { argument := 28135826549829058501086806016, coefficient := (-28135826549829058501086806016) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 22564025415035845927029964800, coefficient := (-22564025415035845927029964800) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-262796556168982759368674504605696)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7398843725, 134712825, 1266300555, 14953123575, 1050760035, 3699421425,
    14953123575, 134712825, 1050760035, 1050760035, 1050760035, 1050760035,
    1050760035, 2446396975, 1266300555, 653224845, 3163591795, 653224845,
    683940375, 57512027625, 28756006875, 341977125, 51663965, 8161796775,
    3163591795, 210045827985, 104294235, 243353215, 3163591795, 3163591795,
    104294235, 39040808635, 1564413525, 8161796775, 3163591795, 243353215,
    1564413525, 243353215, 3163591795, 3163591795, 965667435, 6161625,
    518126375, 259063125, 3080875, 9524277, 1520524089, 60690175371,
    1520524089, 38092761, 15963, 10165, 4099235, 159965,
    4815, 2049617, 4815, 4815, 412485, 4815,
    159965, 412485, 127705, 4815
  ]
def negativeCoefficients : Array ℕ := #[
    34121144159111713361651302400, 19880104049771375421397401600, 23359122258481366120141946880, 275836443690577833971888947200, 620259246352866913147598929920, 34121140123886447237686886400,
    275836443690577833971888947200, 19880104049771375421397401600, 19383101448527091035862466560, 19383101448527091035862466560, 19383101448527091035862466560, 620259246352866913147598929920,
    19383101448527091035862466560, 22564029450261112050994380800, 23359122258481366120141946880, 3012467884575897607345274880, 29178984098026206352753295360, 3012467884575897607345274880,
    3154118264825484593332224000, 265227413689622192191438848000, 265227349702478686511431680000, 3154182251968990273339392000, 953031940188087694854717440, 37639644072513245166541209600,
    29178984098026206352753295360, 242166352036857164974113423360, 15391112491266570383869870080, 1122268619154854090490511360, 29178984098026206352753295360, 29178984098026206352753295360,
    15391112491266570383869870080, 360087902660257469605955502080, 28858335921124819469756006400, 37639644072513245166541209600, 29178984098026206352753295360, 1122268619154854090490511360,
    28858335921124819469756006400, 1122268619154854090490511360, 29178984098026206352753295360, 29178984098026206352753295360, 1113338752110034602751426560, 227323838906341231951872000,
    19115489274927725563346944000, 19115484663241707135959040000, 227328450592359659339776000, 175691900306118187136581632, 28048718727693364821516877824, 279884033214346909523204112384,
    28048718727693364821516877824, 175671853306996083281362944, 1206130178656770344739667968, 192011421193479774388879360, 38716179938812300195130245120, 1510826708864485593217761280,
    181905556920138733631569920, 38716170494079334455839817728, 181905556920138733631569920, 181905556920138733631569920, 7791621354745942423885578240, 181905556920138733631569920,
    1510826708864485593217761280, 7791621354745942423885578240, 1206139623389736084030095360, 181905556920138733631569920
  ]
def negativeScales : Array ℕ := #[
    32, 27, 30, 33, 29, 31,
    33, 27, 29, 29, 29, 29,
    29, 31, 30, 29, 31, 29,
    29, 35, 34, 28, 25, 32,
    31, 37, 26, 27, 31, 31,
    26, 35, 30, 32, 31, 27,
    30, 27, 31, 31, 29, 22,
    28, 27, 21, 23, 30, 35,
    30, 25, 13, 13, 21, 17,
    12, 20, 12, 12, 18, 12,
    17, 18, 16, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32784652681611033, 27005311964636503, 30237972721426778, 33799727831629067, 29968786102877517, 31784652510995421,
    33799727831629067, 27005311964636503, 29968786102877517, 29968786102877517, 29968786102877517, 29968786102877517,
    29968786102877517, 31188011381888527, 30237972721426778, 29283004423049081, 31558916311787948, 29283004423049081,
    29349295317483044, 35743144650869513, 34743144302813688, 28349324584932930, 25622655032926207, 32926239649523466,
    31558916311787948, 37611913174486726, 26636084172323563, 27858476595679667, 31558916311787948, 31558916311787948,
    26636084172323563, 35184263883988115, 30542974767918262, 32926239649523466, 31558916311787948, 27858476595679667,
    30542974767918262, 27858476595679667, 31558916311787948, 31558916311787948, 29846951187388257, 22554879451134478,
    28948728794528472, 27948728446472589, 21554908718584365, 23183178149268309, 30501921526524646, 35820743939304874,
    30501921526524646, 25183013523828421, 13962444201746204, 13311322594732096, 21966923281989994, 17287396755486615,
    12233320082730822, 20966922930047363, 12233320082730822, 12233320082730822, 18653982131227114, 12233320082730822,
    17287396755486615, 18653982131227114, 16962455498884122, 12233320082730822
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
noncomputable def negativeCeiling : ℝ := 31520023 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 34121144159111713361651302400, coefficient := (-34121144159111713361651302400) }, { argument := 19880104049771375421397401600, coefficient := (-19880104049771375421397401600) }, { argument := 23359122258481366120141946880, coefficient := (-23359122258481366120141946880) }, { argument := 275836443690577833971888947200, coefficient := (-275836443690577833971888947200) }, { argument := 620259246352866913147598929920, coefficient := (-620259246352866913147598929920) }, { argument := 34121140123886447237686886400, coefficient := (-34121140123886447237686886400) }, { argument := 275836443690577833971888947200, coefficient := (-275836443690577833971888947200) }, { argument := 19880104049771375421397401600, coefficient := (-19880104049771375421397401600) }, { argument := 19383101448527091035862466560, coefficient := (-19383101448527091035862466560) }, { argument := 19383101448527091035862466560, coefficient := (-19383101448527091035862466560) }, { argument := 19383101448527091035862466560, coefficient := (-19383101448527091035862466560) }, { argument := 620259246352866913147598929920, coefficient := (-620259246352866913147598929920) }, { argument := 19383101448527091035862466560, coefficient := (-19383101448527091035862466560) }, { argument := 22564029450261112050994380800, coefficient := (-22564029450261112050994380800) }, { argument := 23359122258481366120141946880, coefficient := (-23359122258481366120141946880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 3154118264825484593332224000, coefficient := (-3154118264825484593332224000) }, { argument := 265227413689622192191438848000, coefficient := (-265227413689622192191438848000) }, { argument := 265227349702478686511431680000, coefficient := (-265227349702478686511431680000) }, { argument := 3154182251968990273339392000, coefficient := (-3154182251968990273339392000) }, { argument := 953031940188087694854717440, coefficient := (-953031940188087694854717440) }, { argument := 37639644072513245166541209600, coefficient := (-37639644072513245166541209600) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 242166352036857164974113423360, coefficient := (-242166352036857164974113423360) }, { argument := 15391112491266570383869870080, coefficient := (-15391112491266570383869870080) }, { argument := 1122268619154854090490511360, coefficient := (-1122268619154854090490511360) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 15391112491266570383869870080, coefficient := (-15391112491266570383869870080) }, { argument := 360087902660257469605955502080, coefficient := (-360087902660257469605955502080) }, { argument := 28858335921124819469756006400, coefficient := (-28858335921124819469756006400) }, { argument := 37639644072513245166541209600, coefficient := (-37639644072513245166541209600) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 1122268619154854090490511360, coefficient := (-1122268619154854090490511360) }, { argument := 28858335921124819469756006400, coefficient := (-28858335921124819469756006400) }, { argument := 1122268619154854090490511360, coefficient := (-1122268619154854090490511360) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 1113338752110034602751426560, coefficient := (-1113338752110034602751426560) }, { argument := 227323838906341231951872000, coefficient := (-227323838906341231951872000) }, { argument := 19115489274927725563346944000, coefficient := (-19115489274927725563346944000) }, { argument := 19115484663241707135959040000, coefficient := (-19115484663241707135959040000) }, { argument := 227328450592359659339776000, coefficient := (-227328450592359659339776000) }, { argument := 175691900306118187136581632, coefficient := (-175691900306118187136581632) }, { argument := 28048718727693364821516877824, coefficient := (-28048718727693364821516877824) }, { argument := 279884033214346909523204112384, coefficient := (-279884033214346909523204112384) }, { argument := 28048718727693364821516877824, coefficient := (-28048718727693364821516877824) }, { argument := 175671853306996083281362944, coefficient := (-175671853306996083281362944) }, { argument := 1206130178656770344739667968, coefficient := (-1206130178656770344739667968) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 38716179938812300195130245120, coefficient := (-38716179938812300195130245120) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 38716170494079334455839817728, coefficient := (-38716170494079334455839817728) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 1206139623389736084030095360, coefficient := (-1206139623389736084030095360) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }] }

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

end TermShard3


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
