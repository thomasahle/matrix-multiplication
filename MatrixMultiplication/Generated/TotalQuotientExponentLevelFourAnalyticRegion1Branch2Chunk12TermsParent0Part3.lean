import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1780547723999796769486844733685760
def positiveArguments : Array ℕ := #[
    47, 1, 1, 1, 1, 1,
    837, 10017, 14985, 4347, 837, 17361,
    8721, 837, 10017, 837
  ]
def positiveCoefficients : Array ℕ := #[
    14894894552681695467586262663168, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672,
    32379869152558227815330217984, 775027835845103388354032959488, 579704109021606981855105515520, 672665668846693506873311625216, 32379869152558227815330217984, 671621156938546467266365489152,
    674754692662987586087203897344, 32379869152558227815330217984, 775027835845103388354032959488, 32379869152558227815330217984
  ]
def positiveScales : Array ℕ := #[
    5, 0, 0, 0, 0, 0,
    9, 13, 13, 12, 9, 14,
    13, 9, 13, 9
  ]
def negativeArguments : Array ℕ := #[
    28960225, 21947247, 3503816379, 139851273681, 3503816379, 87778971,
    15963, 10165, 4099235, 159965, 4815, 2049617,
    4815, 4815, 412485, 4815, 159965, 412485,
    127705, 4815, 4815, 10165, 1833867, 292771719,
    11685685941, 292771719, 7334631, 15779, 9291, 4097901,
    146211, 4401, 1024475, 4401, 4401, 377019,
    4401, 146211, 377019, 126233, 4401, 4401,
    9291, 3008053, 10761111, 752013, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    267110929446022599724236800, 202427624265744867787800576, 32317002012342355120443359232, 322475081746964917494126477312, 32317002012342355120443359232, 202404526636321574215483392,
    1206130178656770344739667968, 192011421193479774388879360, 38716179938812300195130245120, 1510826708864485593217761280, 181905556920138733631569920, 38716170494079334455839817728,
    181905556920138733631569920, 181905556920138733631569920, 7791621354745942423885578240, 181905556920138733631569920, 1510826708864485593217761280, 7791621354745942423885578240,
    1206139623389736084030095360, 181905556920138733631569920, 181905556920138733631569920, 192011421193479774388879360, 8457218803555378573344768, 1350171243103252033333886976,
    13472678617460798439781564416, 1350171243103252033333886976, 8456253808256022642425856, 1192227531731202109230546944, 175502027969367494721798144, 38703580665036003981700104192,
    1380923851653707392679411712, 166265079128874468683808768, 38703571220303038242409676800, 166265079128874468683808768, 166265079128874468683808768, 7121687556020123075289808896,
    166265079128874468683808768, 1380923851653707392679411712, 7121687556020123075289808896, 1192236976464167848520974336, 166265079128874468683808768, 166265079128874468683808768,
    175502027969367494721798144, 14205128665895484893993893888, 50817909904839850675201376256, 14205123943529002024348680192, 158456325028528675187087900672, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    24, 24, 31, 37, 31, 26,
    13, 13, 21, 17, 12, 20,
    12, 12, 18, 12, 17, 18,
    16, 12, 12, 13, 20, 28,
    33, 28, 22, 13, 13, 21,
    17, 12, 19, 12, 12, 18,
    12, 17, 18, 16, 12, 12,
    13, 21, 23, 19, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5554588851677541, 0, 0, 0, 0, 0,
    9709083812544787, 13290162878784271, 13871231463241128, 12085804380278085, 9709083812544787, 14083562429491415,
    13090277856857393, 9709083812544787, 13290162878784271, 9709083812544787
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24787569475873430, 24387536647774499, 31706280025114397, 37025102436830685, 31706280025114397, 26387372022334611,
    13962444201746204, 13311322594732096, 21966923281989994, 17287396755486615, 12233320082730822, 20966922930047363,
    12233320082730822, 12233320082730822, 18653982131227114, 12233320082730822, 17287396755486615, 18653982131227114,
    16962455498884122, 12233320082730822, 12233320082730822, 13311322594732096, 20806457582277085, 28125200958796615,
    33444023370596794, 28125200958796615, 22806292956834750, 13945718166157771, 13181618168395820, 21966453714170030,
    17157692329150339, 12103615656394547, 19966453362112831, 12103615656394547, 12103615656394547, 18524277704867867,
    12103615656394547, 17157692329150339, 18524277704867867, 16945729595031304, 12103615656394547, 12103615656394547,
    13181618168395820, 21520398555942497, 23359323696701575, 19520398076331506, 0, 0
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 1673819497 / 1000000000000
noncomputable def negativeCeiling : ℝ := 244972001 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 267110929446022599724236800, coefficient := (-267110929446022599724236800) }, { argument := 202427624265744867787800576, coefficient := (-202427624265744867787800576) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 322475081746964917494126477312, coefficient := (-322475081746964917494126477312) }, { argument := 32317002012342355120443359232, coefficient := (-32317002012342355120443359232) }, { argument := 202404526636321574215483392, coefficient := (-202404526636321574215483392) }, { argument := 1206130178656770344739667968, coefficient := (-1206130178656770344739667968) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 38716179938812300195130245120, coefficient := (-38716179938812300195130245120) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 38716170494079334455839817728, coefficient := (-38716170494079334455839817728) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 1510826708864485593217761280, coefficient := (-1510826708864485593217761280) }, { argument := 7791621354745942423885578240, coefficient := (-7791621354745942423885578240) }, { argument := 1206139623389736084030095360, coefficient := (-1206139623389736084030095360) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 8457218803555378573344768, coefficient := (-8457218803555378573344768) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 13472678617460798439781564416, coefficient := (-13472678617460798439781564416) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 8456253808256022642425856, coefficient := (-8456253808256022642425856) }, { argument := 1192227531731202109230546944, coefficient := (-1192227531731202109230546944) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 38703580665036003981700104192, coefficient := (-38703580665036003981700104192) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 38703571220303038242409676800, coefficient := (-38703571220303038242409676800) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 1380923851653707392679411712, coefficient := (-1380923851653707392679411712) }, { argument := 7121687556020123075289808896, coefficient := (-7121687556020123075289808896) }, { argument := 1192236976464167848520974336, coefficient := (-1192236976464167848520974336) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 166265079128874468683808768, coefficient := (-166265079128874468683808768) }, { argument := 175502027969367494721798144, coefficient := (-175502027969367494721798144) }, { argument := 14205128665895484893993893888, coefficient := (-14205128665895484893993893888) }, { argument := 50817909904839850675201376256, coefficient := (-50817909904839850675201376256) }, { argument := 14205123943529002024348680192, coefficient := (-14205123943529002024348680192) }, { argument := 14894894552681695467586262663168, coefficient := 14894894552681695467586262663168 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 775027835845103388354032959488, coefficient := 775027835845103388354032959488 }, { argument := 579704109021606981855105515520, coefficient := 579704109021606981855105515520 }, { argument := 672665668846693506873311625216, coefficient := 672665668846693506873311625216 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 671621156938546467266365489152, coefficient := 671621156938546467266365489152 }, { argument := 674754692662987586087203897344, coefficient := 674754692662987586087203897344 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 775027835845103388354032959488, coefficient := 775027835845103388354032959488 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }] }

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

end TermShard6


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-522938648008713791506688501612544)
def positiveArguments : Array ℕ := #[
    2295, 1785, 255, 2397, 28305, 1989,
    1785, 28305, 255, 1989, 1989, 1989,
    1989, 1989, 2295, 2397, 25, 105,
    455, 15, 15, 35, 455, 455,
    15, 5615, 225, 105, 455, 35,
    225, 35, 455, 455, 15, 1,
    19, 29, 299, 9, 29, 9,
    9, 771, 9, 299, 771, 1,
    9, 9, 19, 3008053, 10761111, 752013,
    13823, 510465, 4083719, 110585
  ]
def positiveCoefficients : Array ℕ := #[
    88783512192498366590421565440, 69053842816387618459216773120, 78918677504442992524819169280, 92729446067720516216662523904, 1094996650374146521281865973760, 2462262738138621366774358081536,
    69053842816387618459216773120, 1094996650374146521281865973760, 78918677504442992524819169280, 76945710566831917711698690048, 76945710566831917711698690048, 76945710566831917711698690048,
    2462262738138621366774358081536, 76945710566831917711698690048, 88783512192498366590421565440, 92729446067720516216662523904, 1934281311383406679529881600, 32495926031241232216102010880,
    70407839734356003134887690240, 2321137573660088015435857920, 37138201178561408246973726720, 2707993835936769351341834240, 70407839734356003134887690240, 70407839734356003134887690240,
    37138201178561408246973726720, 868879165073426280444822814720, 69634127209802640463075737600, 32495926031241232216102010880, 70407839734356003134887690240, 2707993835936769351341834240,
    69634127209802640463075737600, 2707993835936769351341834240, 70407839734356003134887690240, 70407839734356003134887690240, 2321137573660088015435857920, 1237940039285380274899124224,
    1470053796651389076442710016, 1121883160602375874127331328, 11567002242072771943588691968, 1392682544196052809261514752, 1121883160602375874127331328, 1392682544196052809261514752,
    1392682544196052809261514752, 59653235643064261996701548544, 1392682544196052809261514752, 11567002242072771943588691968, 59653235643064261996701548544, 1237940039285380274899124224,
    1392682544196052809261514752, 1392682544196052809261514752, 1470053796651389076442710016, 28410257331790969787987787776, 101635819809679701350402752512, 28410247887058004048697360384,
    8355490802266509540981735424, 308557159254790840833194065920, 308557083696927114918870646784, 8355566360130235455305154560
  ]
def positiveScales : Array ℕ := #[
    11, 10, 7, 11, 14, 10,
    10, 14, 7, 10, 10, 10,
    10, 10, 11, 11, 4, 6,
    8, 3, 3, 5, 8, 8,
    3, 12, 7, 6, 8, 5,
    7, 5, 8, 8, 3, 0,
    4, 4, 8, 3, 4, 3,
    3, 9, 3, 8, 9, 0,
    3, 3, 4, 21, 23, 19,
    13, 18, 21, 16
  ]
def negativeArguments : Array ℕ := #[
    27, 51, 5, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4278320775770274230051373318144, 8081272576454962434541482934272, 1584563250285286751870879006720, 158456325028528675187087900672, 158456325028528675187087900672, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    4, 5, 2, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11164278438301170, 10801708358875019, 7994353435525111, 11227014193649132, 14788769303177175, 10957827560099917,
    10801708358875019, 14788769303177175, 7994353435525111, 10957827560099917, 10957827560099917, 10957827560099917,
    10957827560099917, 10957827560099917, 11164278438301170, 11227014193649132, 4643856189773592, 6714245517659862,
    8829722735013603, 3906890595303263, 3906890595303263, 5129283016944966, 8829722735013603, 8829722735013603,
    3906890595303263, 12455070307287959, 7813781191164178, 6714245517659862, 8829722735013603, 5129283016944966,
    7813781191164178, 5129283016944966, 8829722735013603, 8829722735013603, 3906890595303263, 0,
    4247927513443585, 4857980995002857, 8224001674198104, 3169925001442312, 4857980995002857, 3169925001442312,
    3169925001442312, 9590587049914763, 3169925001442312, 8224001674198104, 9590587049914763, 0,
    3169925001442312, 3169925001442312, 4247927513443585, 21520398555941934, 23359323696701572, 19520398076330943,
    13754783136752719, 18961452519858368, 21961452166578712, 16754796182840014
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4754887502413606, 5672425342008812, 2321928094887363, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 1574234157 / 1000000000000
noncomputable def negativeCeiling : ℝ := 420470177 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 88783512192498366590421565440, coefficient := 88783512192498366590421565440 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 78918677504442992524819169280, coefficient := 78918677504442992524819169280 }, { argument := 92729446067720516216662523904, coefficient := 92729446067720516216662523904 }, { argument := 1094996650374146521281865973760, coefficient := 1094996650374146521281865973760 }, { argument := 2462262738138621366774358081536, coefficient := 2462262738138621366774358081536 }, { argument := 69053842816387618459216773120, coefficient := 69053842816387618459216773120 }, { argument := 1094996650374146521281865973760, coefficient := 1094996650374146521281865973760 }, { argument := 78918677504442992524819169280, coefficient := 78918677504442992524819169280 }, { argument := 76945710566831917711698690048, coefficient := 76945710566831917711698690048 }, { argument := 76945710566831917711698690048, coefficient := 76945710566831917711698690048 }, { argument := 76945710566831917711698690048, coefficient := 76945710566831917711698690048 }, { argument := 2462262738138621366774358081536, coefficient := 2462262738138621366774358081536 }, { argument := 76945710566831917711698690048, coefficient := 76945710566831917711698690048 }, { argument := 88783512192498366590421565440, coefficient := 88783512192498366590421565440 }, { argument := 92729446067720516216662523904, coefficient := 92729446067720516216662523904 }, { argument := 8081272576454962434541482934272, coefficient := (-8081272576454962434541482934272) }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 2707993835936769351341834240, coefficient := 2707993835936769351341834240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 868879165073426280444822814720, coefficient := 868879165073426280444822814720 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2707993835936769351341834240, coefficient := 2707993835936769351341834240 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 2707993835936769351341834240, coefficient := 2707993835936769351341834240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28410257331790969787987787776, coefficient := 28410257331790969787987787776 }, { argument := 101635819809679701350402752512, coefficient := 101635819809679701350402752512 }, { argument := 28410247887058004048697360384, coefficient := 28410247887058004048697360384 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 8355490802266509540981735424, coefficient := 8355490802266509540981735424 }, { argument := 308557159254790840833194065920, coefficient := 308557159254790840833194065920 }, { argument := 308557083696927114918870646784, coefficient := 308557083696927114918870646784 }, { argument := 8355566360130235455305154560, coefficient := 8355566360130235455305154560 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end TermShard7


end Parent0

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-321535849903880213937914283819008)
def positiveArguments : Array ℕ := #[
    59157, 9444249, 376957611, 9444249, 236601, 2513943,
    211395561, 105697755, 1256997, 7178295, 34764745, 7178295,
    535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    2234888272216956815252914176, 356793639467801311518425874432, 3560263975298027768344857280512, 356793639467801311518425874432, 2234633264426881854411374592, 47487040652179057989818253312,
    3993149247575302159280923213824, 3993148284212539653873299619840, 47488004014941563397441847296, 135594158848603039556991713280, 1313374932588080672756895580160, 135594158848603039556991713280,
    41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    15, 23, 28, 23, 17, 21,
    27, 26, 20, 22, 25, 22,
    9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    27, 51, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4278320775770274230051373318144, 8081272576454962434541482934272, 1584563250285286751870879006720, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    4, 5, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15852261271041780, 23171004648409739, 28489827060209868, 23171004648409739, 17852096645602242, 21261520508442344,
    27655369841633849, 26655369493578026, 20261549775892230, 22775209782826431, 25051121671587513, 22775209782826431,
    9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4754887502413606, 5672425342008812, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 4542643693 / 1000000000000
noncomputable def negativeCeiling : ℝ := 420470177 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2234888272216956815252914176, coefficient := 2234888272216956815252914176 }, { argument := 356793639467801311518425874432, coefficient := 356793639467801311518425874432 }, { argument := 3560263975298027768344857280512, coefficient := 3560263975298027768344857280512 }, { argument := 356793639467801311518425874432, coefficient := 356793639467801311518425874432 }, { argument := 2234633264426881854411374592, coefficient := 2234633264426881854411374592 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 47487040652179057989818253312, coefficient := 47487040652179057989818253312 }, { argument := 3993149247575302159280923213824, coefficient := 3993149247575302159280923213824 }, { argument := 3993148284212539653873299619840, coefficient := 3993148284212539653873299619840 }, { argument := 47488004014941563397441847296, coefficient := 47488004014941563397441847296 }, { argument := 8081272576454962434541482934272, coefficient := (-8081272576454962434541482934272) }, { argument := 135594158848603039556991713280, coefficient := 135594158848603039556991713280 }, { argument := 1313374932588080672756895580160, coefficient := 1313374932588080672756895580160 }, { argument := 135594158848603039556991713280, coefficient := 135594158848603039556991713280 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
