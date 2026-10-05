import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 12, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-263502599666871281170282729963520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    728595, 8505, 282555, 728595, 699125735, 8505,
    8505, 17955, 158193690277, 545508542663, 39548421157, 5289985,
    5289983, 7875, 2025, 7875, 6975, 326475,
    88875, 2025, 326475, 7875, 7875, 3375,
    7875, 88875, 3375, 7875, 6975, 31420039,
    3294334421, 35509632375, 1647168467, 31420039, 7875, 2025,
    7875, 6975, 326475, 88875, 2025, 326475,
    7875, 7875, 3375, 7875, 88875, 3375,
    7875, 6975, 201985965, 21177864135, 228276208125, 10588940145,
    201985965, 682043541, 17955, 24170410347, 282555, 8505,
    193363353795, 8505, 8505, 728595
  ]
def negativeCoefficients : Array ℕ := #[
    6881385215172818308945674240, 160654907747225330169937920, 1334328261567232603355873280, 6881385215172818308945674240, 6448296754444542225028218880, 160654907747225330169937920,
    160654907747225330169937920, 169580180399848959623823360, 182384907413468379174878052352, 628928529782914334649208537088, 182384900900614799650799484928, 49962495717766360271547269120,
    49962476828300428792966414336, 148754544210393824231424000, 153004674044976504923750400, 148754544210393824231424000, 131754024872063101462118400, 6166938389979469684565606400,
    1678801284660158873468928000, 153004674044976504923750400, 6166938389979469684565606400, 148754544210393824231424000, 148754544210393824231424000, 127503895037480420769792000,
    148754544210393824231424000, 1678801284660158873468928000, 127503895037480420769792000, 148754544210393824231424000, 131754024872063101462118400, 72449677277371623305904128,
    7596217994674892130633121792, 81879637571642010051280896000, 7596223789258374284646023168, 72449677277371623305904128, 148754544210393824231424000, 153004674044976504923750400,
    148754544210393824231424000, 131754024872063101462118400, 6166938389979469684565606400, 1678801284660158873468928000, 153004674044976504923750400, 6166938389979469684565606400,
    148754544210393824231424000, 148754544210393824231424000, 127503895037480420769792000, 148754544210393824231424000, 1678801284660158873468928000, 127503895037480420769792000,
    148754544210393824231424000, 131754024872063101462118400, 1862991701418127456437534720, 195331319863068654787708846080, 2105476394699365972747223040000, 195331468866643910176612024320,
    1862991701418127456437534720, 6290741323976813794849456128, 169580180399848959623823360, 222932686913825138526048485376, 1334328261567232603355873280, 160654907747225330169937920,
    222932768793157474199713873920, 160654907747225330169937920, 160654907747225330169937920, 6881385215172818308945674240
  ]
def negativeScales : Array ℕ := #[
    19, 13, 18, 19, 29, 13,
    13, 14, 37, 38, 35, 22,
    22, 12, 10, 12, 12, 18,
    16, 10, 18, 12, 12, 11,
    12, 16, 11, 12, 12, 24,
    31, 35, 30, 24, 12, 10,
    12, 12, 18, 16, 10, 18,
    12, 12, 11, 12, 16, 11,
    12, 12, 27, 34, 37, 33,
    27, 29, 14, 34, 18, 13,
    37, 13, 13, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19474757569023584, 13054095520550748, 18108172193306541, 19474757569023584, 29380976701034661, 13054095520550748,
    13054095520550748, 14132098032552021, 37202901101298489, 38988810852874516, 35202901049780730, 22334832200839980,
    22334831655395971, 12943064217429565, 10983706210875052, 12943064217429565, 12767977501935366, 18316612995283782,
    16439490034281534, 10983706210875052, 18316612995283782, 12943064217429565, 12943064217429565, 11720671786942400,
    12943064217429565, 16439490034281534, 11720671786942400, 12943064217429565, 12767977501935366, 24905181640375697,
    31617339870209827, 35047491373340934, 30617340970732965, 24905181640375697, 12943064217429565, 10983706210875052,
    12943064217429565, 12767977501935366, 18316612995283782, 16439490034281534, 10983706210875052, 18316612995283782,
    12943064217429565, 12943064217429565, 11720671786942400, 12943064217429565, 16439490034281534, 11720671786942400,
    12943064217429565, 12767977501935366, 27589679809860620, 34301838044472825, 37731989547763934, 33301839144995963,
    27589679809860620, 29345288601544336, 14132098032552021, 34492522915173714, 18108172193306541, 13054095520550748,
    37492523445050632, 13054095520550748, 13054095520550748, 19474757569023584
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
noncomputable def negativeCeiling : ℝ := 184830119 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 6448296754444542225028218880, coefficient := (-6448296754444542225028218880) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 182384907413468379174878052352, coefficient := (-182384907413468379174878052352) }, { argument := 628928529782914334649208537088, coefficient := (-628928529782914334649208537088) }, { argument := 182384900900614799650799484928, coefficient := (-182384900900614799650799484928) }, { argument := 49962495717766360271547269120, coefficient := (-49962495717766360271547269120) }, { argument := 49962476828300428792966414336, coefficient := (-49962476828300428792966414336) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 72449677277371623305904128, coefficient := (-72449677277371623305904128) }, { argument := 7596217994674892130633121792, coefficient := (-7596217994674892130633121792) }, { argument := 81879637571642010051280896000, coefficient := (-81879637571642010051280896000) }, { argument := 7596223789258374284646023168, coefficient := (-7596223789258374284646023168) }, { argument := 72449677277371623305904128, coefficient := (-72449677277371623305904128) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 1862991701418127456437534720, coefficient := (-1862991701418127456437534720) }, { argument := 195331319863068654787708846080, coefficient := (-195331319863068654787708846080) }, { argument := 2105476394699365972747223040000, coefficient := (-2105476394699365972747223040000) }, { argument := 195331468866643910176612024320, coefficient := (-195331468866643910176612024320) }, { argument := 1862991701418127456437534720, coefficient := (-1862991701418127456437534720) }, { argument := 6290741323976813794849456128, coefficient := (-6290741323976813794849456128) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 222932686913825138526048485376, coefficient := (-222932686913825138526048485376) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 222932768793157474199713873920, coefficient := (-222932768793157474199713873920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }] }

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

namespace Parent2

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-226376650788731432541636849041408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8505, 282555, 728595, 5456277309, 8505, 8505,
    17955, 31420039, 3294334421, 35509632375, 1647168467, 31420039,
    679831701, 7695, 24168405867, 121095, 3645, 193347317955,
    3645, 3645, 312255, 3645, 121095, 312255,
    5438582589, 3645, 3645, 7695, 7323361395, 25215942601,
    1830840305, 16625, 4275, 16625, 14725, 689225,
    187625, 4275, 689225, 16625, 16625, 7125,
    16625, 187625, 7125, 16625, 14725, 408460507,
    42826347473, 461625220875, 21413190071, 408460507, 682043541, 17955,
    24170410347, 282555, 8505, 193363353795, 8505, 8505,
    728595, 8505, 282555, 728595
  ]
def negativeCoefficients : Array ℕ := #[
    160654907747225330169937920, 1334328261567232603355873280, 6881385215172818308945674240, 6290659444644478121184067584, 160654907747225330169937920, 160654907747225330169937920,
    169580180399848959623823360, 72449677277371623305904128, 7596217994674892130633121792, 81879637571642010051280896000, 7596223789258374284646023168, 72449677277371623305904128,
    6270340700770816927526289408, 145354440342727679677562880, 222914198849044703865036865536, 1143709938486199374305034240, 137704206640478854431375360, 222914280728377039538702254080,
    137704206640478854431375360, 137704206640478854431375360, 5898330184433844264810577920, 137704206640478854431375360, 1143709938486199374305034240, 5898330184433844264810577920,
    6270258821438481253860900864, 137704206640478854431375360, 137704206640478854431375360, 145354440342727679677562880, 8443260838303097796710891520, 29072002483624810418406424576,
    8443260636541834490512670720, 157018685555415703355392000, 161504933714141866308403200, 157018685555415703355392000, 139073692920511051543347200, 6509546078311662444819251200,
    1772068022696834366439424000, 161504933714141866308403200, 6509546078311662444819251200, 157018685555415703355392000, 157018685555415703355392000, 134587444761784888590336000,
    157018685555415703355392000, 1772068022696834366439424000, 134587444761784888590336000, 157018685555415703355392000, 139073692920511051543347200, 1883691609211662205953507328,
    197501667861547195396461166592, 2128870576862692261333303296000, 197501818520717731400796602368, 1883691609211662205953507328, 6290741323976813794849456128, 169580180399848959623823360,
    222932686913825138526048485376, 1334328261567232603355873280, 160654907747225330169937920, 222932768793157474199713873920, 160654907747225330169937920, 160654907747225330169937920,
    6881385215172818308945674240, 160654907747225330169937920, 1334328261567232603355873280, 6881385215172818308945674240
  ]
def negativeScales : Array ℕ := #[
    13, 18, 19, 32, 13, 13,
    14, 24, 31, 35, 30, 24,
    29, 12, 34, 16, 11, 37,
    11, 11, 18, 11, 16, 18,
    32, 11, 11, 12, 32, 34,
    30, 14, 12, 14, 13, 19,
    17, 12, 19, 14, 14, 12,
    14, 17, 12, 14, 13, 28,
    35, 38, 34, 28, 29, 14,
    34, 18, 13, 37, 13, 13,
    19, 13, 18, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13054095520550748, 18108172193306541, 19474757569023584, 32345269823522892, 13054095520550748, 13054095520550748,
    14132098032552021, 24905181640375697, 31617339870209827, 35047491373340934, 30617340970732965, 24905181640375697,
    29340602396367056, 12909705616407956, 34492403265849062, 16885779775347245, 11831703100430750, 37492403795769927,
    11831703100430750, 11831703100430750, 18252365147687022, 11831703100430750, 16885779775347245, 18252365147687022,
    32340583557250712, 11831703100430750, 11831703100430750, 12909705616407956, 32769858846390160, 34553617104781919,
    30769858811915330, 14021066720163277, 12061708704660623, 14021066720163277, 13845980015209050, 19394615507285060,
    17517492546283257, 12061708704660623, 19394615507285060, 14021066720163277, 14021066720163277, 12798674299455620,
    14021066720163277, 17517492546283257, 12798674299455620, 14021066720163277, 13845980015209050, 28605621353732004,
    35317779588341847, 38747931091696951, 34317780688864985, 28605621353732004, 29345288601544336, 14132098032552021,
    34492522915173714, 18108172193306541, 13054095520550748, 37492523445050632, 13054095520550748, 13054095520550748,
    19474757569023584, 13054095520550748, 18108172193306541, 19474757569023584
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
noncomputable def negativeCeiling : ℝ := 1627493331 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 6290659444644478121184067584, coefficient := (-6290659444644478121184067584) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 72449677277371623305904128, coefficient := (-72449677277371623305904128) }, { argument := 7596217994674892130633121792, coefficient := (-7596217994674892130633121792) }, { argument := 81879637571642010051280896000, coefficient := (-81879637571642010051280896000) }, { argument := 7596223789258374284646023168, coefficient := (-7596223789258374284646023168) }, { argument := 72449677277371623305904128, coefficient := (-72449677277371623305904128) }, { argument := 6270340700770816927526289408, coefficient := (-6270340700770816927526289408) }, { argument := 145354440342727679677562880, coefficient := (-145354440342727679677562880) }, { argument := 222914198849044703865036865536, coefficient := (-222914198849044703865036865536) }, { argument := 1143709938486199374305034240, coefficient := (-1143709938486199374305034240) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 222914280728377039538702254080, coefficient := (-222914280728377039538702254080) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 5898330184433844264810577920, coefficient := (-5898330184433844264810577920) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 1143709938486199374305034240, coefficient := (-1143709938486199374305034240) }, { argument := 5898330184433844264810577920, coefficient := (-5898330184433844264810577920) }, { argument := 6270258821438481253860900864, coefficient := (-6270258821438481253860900864) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 137704206640478854431375360, coefficient := (-137704206640478854431375360) }, { argument := 145354440342727679677562880, coefficient := (-145354440342727679677562880) }, { argument := 8443260838303097796710891520, coefficient := (-8443260838303097796710891520) }, { argument := 29072002483624810418406424576, coefficient := (-29072002483624810418406424576) }, { argument := 8443260636541834490512670720, coefficient := (-8443260636541834490512670720) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 161504933714141866308403200, coefficient := (-161504933714141866308403200) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 139073692920511051543347200, coefficient := (-139073692920511051543347200) }, { argument := 6509546078311662444819251200, coefficient := (-6509546078311662444819251200) }, { argument := 1772068022696834366439424000, coefficient := (-1772068022696834366439424000) }, { argument := 161504933714141866308403200, coefficient := (-161504933714141866308403200) }, { argument := 6509546078311662444819251200, coefficient := (-6509546078311662444819251200) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 134587444761784888590336000, coefficient := (-134587444761784888590336000) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 1772068022696834366439424000, coefficient := (-1772068022696834366439424000) }, { argument := 134587444761784888590336000, coefficient := (-134587444761784888590336000) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 139073692920511051543347200, coefficient := (-139073692920511051543347200) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 197501667861547195396461166592, coefficient := (-197501667861547195396461166592) }, { argument := 2128870576862692261333303296000, coefficient := (-2128870576862692261333303296000) }, { argument := 197501818520717731400796602368, coefficient := (-197501818520717731400796602368) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 6290741323976813794849456128, coefficient := (-6290741323976813794849456128) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 222932686913825138526048485376, coefficient := (-222932686913825138526048485376) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 222932768793157474199713873920, coefficient := (-222932768793157474199713873920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }] }

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

end TermShard9


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
