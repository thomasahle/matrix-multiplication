import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-139832388494736160118993808523264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4815, 10165, 4815, 4401, 4815, 4401,
    50248065, 243353215, 50248065, 4815, 4401, 4815,
    4401, 323023275, 1564413525, 323023275, 48060675, 4041385725,
    2020692375, 24030825, 50248065, 243353215, 50248065, 48060675,
    4041385725, 2020692375, 24030825, 1833867, 292771719, 11685685941,
    292771719, 7334631, 10165, 9291, 10165, 9291,
    653224845, 3163591795, 653224845, 48060675, 4041385725, 2020692375,
    24030825, 653224845, 3163591795, 653224845, 48060675, 4041385725,
    2020692375, 24030825, 38037951, 6072652107, 242383743873, 6072652107,
    152134443, 48060675, 4041385725, 2020692375, 24030825, 19107711,
    3050492427, 121757308353, 3050492427, 76422123
  ]
def negativeCoefficients : Array ℕ := #[
    181905556920138733631569920, 192011421193479774388879360, 181905556920138733631569920, 166265079128874468683808768, 181905556920138733631569920, 166265079128874468683808768,
    115864149406765292590202880, 1122268619154854090490511360, 115864149406765292590202880, 181905556920138733631569920, 166265079128874468683808768, 181905556920138733631569920,
    166265079128874468683808768, 2979363841888250380890931200, 28858335921124819469756006400, 2979363841888250380890931200, 221640742933682701153075200, 18637602043054532424263270400,
    18637597546660664457560064000, 221645239327550667856281600, 115864149406765292590202880, 1122268619154854090490511360, 115864149406765292590202880, 221640742933682701153075200,
    18637602043054532424263270400, 18637597546660664457560064000, 221645239327550667856281600, 8457218803555378573344768, 1350171243103252033333886976, 13472678617460798439781564416,
    1350171243103252033333886976, 8456253808256022642425856, 192011421193479774388879360, 175502027969367494721798144, 192011421193479774388879360, 175502027969367494721798144,
    3012467884575897607345274880, 29178984098026206352753295360, 3012467884575897607345274880, 221640742933682701153075200, 18637602043054532424263270400, 18637597546660664457560064000,
    221645239327550667856281600, 3012467884575897607345274880, 29178984098026206352753295360, 3012467884575897607345274880, 7092503773877846436898406400, 596403265377745037576424652800,
    596403121493141262641922048000, 7092647658481621371401011200, 175419086796326078150344704, 28005164816625517981731913728, 279449430678299786992888578048, 28005164816625517981731913728,
    175399070926084598679994368, 221640742933682701153075200, 18637602043054532424263270400, 18637597546660664457560064000, 221645239327550667856281600, 176237527325702405109055488,
    28135826549829058501086806016, 280753238286441154583835181056, 28135826549829058501086806016, 176217418068819052484100096
  ]
def negativeScales : Array ℕ := #[
    12, 13, 12, 12, 12, 12,
    25, 27, 25, 12, 12, 12,
    12, 28, 30, 28, 25, 31,
    30, 24, 25, 27, 25, 25,
    31, 30, 24, 20, 28, 33,
    28, 22, 13, 13, 13, 13,
    29, 31, 29, 25, 31, 30,
    24, 29, 31, 29, 25, 31,
    30, 24, 25, 32, 37, 32,
    27, 25, 31, 30, 24, 24,
    31, 36, 31, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12233320082730822, 13311322594732096, 12233320082730822, 12103615656394547, 12233320082730822, 12103615656394547,
    25582564704911453, 27858476595679667, 25582564704911453, 12233320082730822, 12103615656394547, 12233320082730822,
    12103615656394547, 28267062879180059, 30542974767918262, 28267062879180059, 25518353575108318, 31912202913727760,
    30912202565671903, 24518382842558204, 25582564704911453, 27858476595679667, 25582564704911453, 25518353575108318,
    31912202913727760, 30912202565671903, 24518382842558204, 20806457582277085, 28125200958796615, 33444023370596794,
    28125200958796615, 22806292956834750, 13311322594732096, 13181618168395820, 13311322594732096, 13181618168395820,
    29283004423049081, 31558916311787948, 29283004423049081, 25518353575108318, 31912202913727760, 30912202565671903,
    24518382842558204, 29283004423049081, 31558916311787948, 29283004423049081, 25518353575108318, 31912202913727760,
    30912202565671903, 24518382842558204, 25180936198481639, 32499679575737956, 37818501988475512, 32499679575737956,
    27180771573041751, 25518353575108318, 31912202913727760, 30912202565671903, 24518382842558204, 24187651625847616,
    31506395003104000, 36825217415974843, 31506395003104000, 26187487000407729
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
noncomputable def negativeCeiling : ℝ := 426997599 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 1122268619154854090490511360, coefficient := (-1122268619154854090490511360) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 28858335921124819469756006400, coefficient := (-28858335921124819469756006400) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 221640742933682701153075200, coefficient := (-221640742933682701153075200) }, { argument := 18637602043054532424263270400, coefficient := (-18637602043054532424263270400) }, { argument := 18637597546660664457560064000, coefficient := (-18637597546660664457560064000) }, { argument := 221645239327550667856281600, coefficient := (-221645239327550667856281600) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 1122268619154854090490511360, coefficient := (-1122268619154854090490511360) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 221640742933682701153075200, coefficient := (-221640742933682701153075200) }, { argument := 18637602043054532424263270400, coefficient := (-18637602043054532424263270400) }, { argument := 18637597546660664457560064000, coefficient := (-18637597546660664457560064000) }, { argument := 221645239327550667856281600, coefficient := (-221645239327550667856281600) }, { argument := 8457218803555378573344768, coefficient := (-8457218803555378573344768) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 13472678617460798439781564416, coefficient := (-13472678617460798439781564416) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 8456253808256022642425856, coefficient := (-8456253808256022642425856) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 221640742933682701153075200, coefficient := (-221640742933682701153075200) }, { argument := 18637602043054532424263270400, coefficient := (-18637602043054532424263270400) }, { argument := 18637597546660664457560064000, coefficient := (-18637597546660664457560064000) }, { argument := 221645239327550667856281600, coefficient := (-221645239327550667856281600) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 29178984098026206352753295360, coefficient := (-29178984098026206352753295360) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 7092503773877846436898406400, coefficient := (-7092503773877846436898406400) }, { argument := 596403265377745037576424652800, coefficient := (-596403265377745037576424652800) }, { argument := 596403121493141262641922048000, coefficient := (-596403121493141262641922048000) }, { argument := 7092647658481621371401011200, coefficient := (-7092647658481621371401011200) }, { argument := 175419086796326078150344704, coefficient := (-175419086796326078150344704) }, { argument := 28005164816625517981731913728, coefficient := (-28005164816625517981731913728) }, { argument := 279449430678299786992888578048, coefficient := (-279449430678299786992888578048) }, { argument := 28005164816625517981731913728, coefficient := (-28005164816625517981731913728) }, { argument := 175399070926084598679994368, coefficient := (-175399070926084598679994368) }, { argument := 221640742933682701153075200, coefficient := (-221640742933682701153075200) }, { argument := 18637602043054532424263270400, coefficient := (-18637602043054532424263270400) }, { argument := 18637597546660664457560064000, coefficient := (-18637597546660664457560064000) }, { argument := 221645239327550667856281600, coefficient := (-221645239327550667856281600) }, { argument := 176237527325702405109055488, coefficient := (-176237527325702405109055488) }, { argument := 28135826549829058501086806016, coefficient := (-28135826549829058501086806016) }, { argument := 280753238286441154583835181056, coefficient := (-280753238286441154583835181056) }, { argument := 28135826549829058501086806016, coefficient := (-28135826549829058501086806016) }, { argument := 176217418068819052484100096, coefficient := (-176217418068819052484100096) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-19765269604022130632564831944704)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15779, 9291, 4097901, 146211, 4401, 1024475,
    4401, 4401, 377019, 4401, 146211, 377019,
    126233, 4401, 4401, 9291, 93474171, 87778971,
    965667435, 38092761, 7334631, 152134443, 76422123, 93474171,
    87778971, 7334631, 113128605, 4707994915, 1602055, 15059317,
    177828105, 12496029, 2353996895, 177828105, 1602055, 12496029,
    12496029, 12496029, 12496029, 12496029, 56564865, 15059317,
    39559209, 594260109, 653224845, 11771825481, 21534885, 50248065,
    653224845, 653224845, 21534885, 8061225285, 323023275, 594260109,
    653224845, 50248065, 323023275, 50248065, 653224845, 653224845,
    93474171, 57919275, 4870387925, 2435193375
  ]
def negativeCoefficients : Array ℕ := #[
    1192227531731202109230546944, 175502027969367494721798144, 38703580665036003981700104192, 1380923851653707392679411712, 166265079128874468683808768, 38703571220303038242409676800,
    166265079128874468683808768, 166265079128874468683808768, 7121687556020123075289808896, 166265079128874468683808768, 1380923851653707392679411712, 7121687556020123075289808896,
    1192236976464167848520974336, 166265079128874468683808768, 166265079128874468683808768, 175502027969367494721798144, 107768381871197702005456896, 202404526636321574215483392,
    1113338752110034602751426560, 175671853306996083281362944, 8456253808256022642425856, 175399070926084598679994368, 176217418068819052484100096, 107768381871197702005456896,
    202404526636321574215483392, 8456253808256022642425856, 521713605962694687373393920, 21711794324332738548764508160, 236421588616054045713367040, 277795366623863503713206272,
    3280349542047749884272967680, 7376353564820886226257051648, 21711789136185967817953116160, 3280349542047749884272967680, 236421588616054045713367040, 230511048900652694570532864,
    230511048900652694570532864, 230511048900652694570532864, 7376353564820886226257051648, 230511048900652694570532864, 521718794109465418184785920, 277795366623863503713206272,
    91217325522673444709203968, 2740541035984435544416321536, 3012467884575897607345274880, 13571990745523740119144595456, 1588994049007066869808496640, 115864149406765292590202880,
    3012467884575897607345274880, 3012467884575897607345274880, 1588994049007066869808496640, 37175839938227835308227952640, 2979363841888250380890931200, 2740541035984435544416321536,
    3012467884575897607345274880, 115864149406765292590202880, 2979363841888250380890931200, 115864149406765292590202880, 3012467884575897607345274880, 3012467884575897607345274880,
    107768381871197702005456896, 267105510714950947543449600, 22460699898040077536932659200, 22460694479309005884751872000
  ]
def negativeScales : Array ℕ := #[
    13, 13, 21, 17, 12, 19,
    12, 12, 18, 12, 17, 18,
    16, 12, 12, 13, 26, 26,
    29, 25, 22, 27, 26, 26,
    26, 22, 26, 32, 20, 23,
    27, 23, 31, 27, 20, 23,
    23, 23, 23, 23, 25, 23,
    25, 29, 29, 33, 24, 25,
    29, 29, 24, 32, 28, 29,
    29, 25, 28, 25, 29, 29,
    26, 25, 32, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13945718166157771, 13181618168395820, 21966453714170030, 17157692329150339, 12103615656394547, 19966453362112831,
    12103615656394547, 12103615656394547, 18524277704867867, 12103615656394547, 17157692329150339, 18524277704867867,
    16945729595031304, 12103615656394547, 12103615656394547, 13181618168395820, 26478064435435603, 26387372022334611,
    29846951187388257, 25183013523828421, 22806292956834750, 27180771573041751, 26187487000407729, 26478064435435603,
    26387372022334611, 22806292956834750, 26753388525749058, 32132465616140817, 20611492246956938, 23844153005288017,
    27405908113299305, 23574966370926861, 31132465271401253, 27405908113299305, 20611492246956938, 23574966370926861,
    23574966370926861, 23574966370926861, 23574966370926861, 23574966370926861, 25753402872464104, 23844153005288017,
    25237510243413052, 29146519299260924, 29283004423049081, 33454619008262403, 24360172283571542, 25582564704911453,
    29283004423049081, 29283004423049081, 24360172283571542, 32908352000320225, 28267062879180059, 29146519299260924,
    29283004423049081, 25582564704911453, 28267062879180059, 25582564704911453, 29283004423049081, 29283004423049081,
    26478064435435603, 25787540208423241, 32181389541116234, 31181389193060411
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
noncomputable def negativeCeiling : ℝ := 97274951 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1192227531731202109230546944, coefficient := (-1192227531731202109230546944) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 38703580665036003981700104192, coefficient := (-38703580665036003981700104192) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 38703571220303038242409676800, coefficient := (-38703571220303038242409676800) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 1192236976464167848520974336, coefficient := (-1192236976464167848520974336) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 107768381871197702005456896, coefficient := (-107768381871197702005456896) }, { argument := 202404526636321574215483392, coefficient := (-202404526636321574215483392) }, { argument := 1113338752110034602751426560, coefficient := (-1113338752110034602751426560) }, { argument := 175671853306996083281362944, coefficient := (-175671853306996083281362944) }, { argument := 8456253808256022642425856, coefficient := (-8456253808256022642425856) }, { argument := 175399070926084598679994368, coefficient := (-175399070926084598679994368) }, { argument := 176217418068819052484100096, coefficient := (-176217418068819052484100096) }, { argument := 107768381871197702005456896, coefficient := (-107768381871197702005456896) }, { argument := 202404526636321574215483392, coefficient := (-202404526636321574215483392) }, { argument := 8456253808256022642425856, coefficient := (-8456253808256022642425856) }, { argument := 521713605962694687373393920, coefficient := (-521713605962694687373393920) }, { argument := 21711794324332738548764508160, coefficient := (-21711794324332738548764508160) }, { argument := 236421588616054045713367040, coefficient := (-236421588616054045713367040) }, { argument := 277795366623863503713206272, coefficient := (-277795366623863503713206272) }, { argument := 3280349542047749884272967680, coefficient := (-3280349542047749884272967680) }, { argument := 7376353564820886226257051648, coefficient := (-7376353564820886226257051648) }, { argument := 21711789136185967817953116160, coefficient := (-21711789136185967817953116160) }, { argument := 3280349542047749884272967680, coefficient := (-3280349542047749884272967680) }, { argument := 236421588616054045713367040, coefficient := (-236421588616054045713367040) }, { argument := 230511048900652694570532864, coefficient := (-230511048900652694570532864) }, { argument := 230511048900652694570532864, coefficient := (-230511048900652694570532864) }, { argument := 230511048900652694570532864, coefficient := (-230511048900652694570532864) }, { argument := 7376353564820886226257051648, coefficient := (-7376353564820886226257051648) }, { argument := 230511048900652694570532864, coefficient := (-230511048900652694570532864) }, { argument := 521718794109465418184785920, coefficient := (-521718794109465418184785920) }, { argument := 277795366623863503713206272, coefficient := (-277795366623863503713206272) }, { argument := 91217325522673444709203968, coefficient := (-91217325522673444709203968) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 13571990745523740119144595456, coefficient := (-13571990745523740119144595456) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 1588994049007066869808496640, coefficient := (-1588994049007066869808496640) }, { argument := 37175839938227835308227952640, coefficient := (-37175839938227835308227952640) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 2740541035984435544416321536, coefficient := (-2740541035984435544416321536) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 2979363841888250380890931200, coefficient := (-2979363841888250380890931200) }, { argument := 115864149406765292590202880, coefficient := (-115864149406765292590202880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 3012467884575897607345274880, coefficient := (-3012467884575897607345274880) }, { argument := 107768381871197702005456896, coefficient := (-107768381871197702005456896) }, { argument := 267105510714950947543449600, coefficient := (-267105510714950947543449600) }, { argument := 22460699898040077536932659200, coefficient := (-22460699898040077536932659200) }, { argument := 22460694479309005884751872000, coefficient := (-22460694479309005884751872000) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
