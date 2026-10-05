import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-268116129237333265720684075548672)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3098725585, 282555, 8505, 24789813785, 8505, 8505,
    728595, 8505, 282555, 728595, 699125735, 8505,
    8505, 17955, 147453210171597, 266704756941619, 147453209813197, 7875,
    2025, 7875, 6975, 326475, 88875, 2025,
    326475, 7875, 7875, 3375, 7875, 88875,
    3375, 7875, 6975, 674625, 173475, 674625,
    597525, 27968025, 7613625, 173475, 27968025, 674625,
    674625, 289125, 674625, 7613625, 289125, 674625,
    597525, 408460507, 42826347473, 461625220875, 21413190071, 408460507,
    7875, 2025, 7875, 6975, 326475, 88875,
    2025, 326475, 7875, 7875
  ]
def negativeCoefficients : Array ℕ := #[
    228645591284603653805509181440, 1334328261567232603355873280, 160654907747225330169937920, 228645675263406049368242913280, 160654907747225330169937920, 160654907747225330169937920,
    6881385215172818308945674240, 160654907747225330169937920, 1334328261567232603355873280, 6881385215172818308945674240, 6448296754444542225028218880, 160654907747225330169937920,
    160654907747225330169937920, 169580180399848959623823360, 83008777797923459968756875264, 300282860995053508700988768256, 83008777596162196662558654464, 148754544210393824231424000,
    153004674044976504923750400, 148754544210393824231424000, 131754024872063101462118400, 6166938389979469684565606400, 1678801284660158873468928000, 153004674044976504923750400,
    6166938389979469684565606400, 148754544210393824231424000, 148754544210393824231424000, 127503895037480420769792000, 148754544210393824231424000, 1678801284660158873468928000,
    127503895037480420769792000, 148754544210393824231424000, 131754024872063101462118400, 6371652977011868804579328000, 6553700204926493627567308800, 6371652977011868804579328000,
    5643464065353369512627404800, 264150527704120618155560140800, 71908655026276805080252416000, 6553700204926493627567308800, 264150527704120618155560140800, 6371652977011868804579328000,
    6371652977011868804579328000, 5461416837438744689639424000, 6371652977011868804579328000, 71908655026276805080252416000, 5461416837438744689639424000, 6371652977011868804579328000,
    5643464065353369512627404800, 1883691609211662205953507328, 197501667861547195396461166592, 2128870576862692261333303296000, 197501818520717731400796602368, 1883691609211662205953507328,
    148754544210393824231424000, 153004674044976504923750400, 148754544210393824231424000, 131754024872063101462118400, 6166938389979469684565606400, 1678801284660158873468928000,
    153004674044976504923750400, 6166938389979469684565606400, 148754544210393824231424000, 148754544210393824231424000
  ]
def negativeScales : Array ℕ := #[
    31, 18, 13, 34, 13, 13,
    19, 13, 18, 19, 29, 13,
    13, 14, 47, 47, 47, 12,
    10, 12, 12, 18, 16, 10,
    18, 12, 12, 11, 12, 16,
    11, 12, 12, 19, 17, 19,
    19, 24, 22, 17, 24, 19,
    19, 18, 19, 22, 18, 19,
    19, 28, 35, 38, 34, 28,
    12, 10, 12, 12, 18, 16,
    10, 18, 12, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31529027853283808, 18108172193306541, 13054095520550748, 34529028383168416, 13054095520550748, 13054095520550748,
    19474757569023584, 13054095520550748, 18108172193306541, 19474757569023584, 29380976701034661, 13054095520550748,
    13054095520550748, 14132098032552021, 47067250559762903, 47922236891898540, 47067250556256286, 12943064217429565,
    10983706210875052, 12943064217429565, 12767977501935366, 18316612995283782, 16439490034281534, 10983706210875052,
    18316612995283782, 12943064217429565, 12943064217429565, 11720671786942400, 12943064217429565, 16439490034281534,
    11720671786942400, 12943064217429565, 12767977501935366, 19363726256634727, 17404368241132080, 19363726256634727,
    19188639550076635, 24737275043926354, 22860152084854098, 17404368241132080, 24737275043926354, 19363726256634727,
    19363726256634727, 18141333835298278, 19363726256634727, 22860152084854098, 18141333835298278, 19363726256634727,
    19188639550076635, 28605621353732004, 35317779588341847, 38747931091696951, 34317780688864985, 28605621353732004,
    12943064217429565, 10983706210875052, 12943064217429565, 12767977501935366, 18316612995283782, 16439490034281534,
    10983706210875052, 18316612995283782, 12943064217429565, 12943064217429565
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
noncomputable def negativeCeiling : ℝ := 1835499349 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 228645591284603653805509181440, coefficient := (-228645591284603653805509181440) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 228645675263406049368242913280, coefficient := (-228645675263406049368242913280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 6448296754444542225028218880, coefficient := (-6448296754444542225028218880) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 83008777797923459968756875264, coefficient := (-83008777797923459968756875264) }, { argument := 300282860995053508700988768256, coefficient := (-300282860995053508700988768256) }, { argument := 83008777596162196662558654464, coefficient := (-83008777596162196662558654464) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 6553700204926493627567308800, coefficient := (-6553700204926493627567308800) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 5643464065353369512627404800, coefficient := (-5643464065353369512627404800) }, { argument := 264150527704120618155560140800, coefficient := (-264150527704120618155560140800) }, { argument := 71908655026276805080252416000, coefficient := (-71908655026276805080252416000) }, { argument := 6553700204926493627567308800, coefficient := (-6553700204926493627567308800) }, { argument := 264150527704120618155560140800, coefficient := (-264150527704120618155560140800) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 5461416837438744689639424000, coefficient := (-5461416837438744689639424000) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 71908655026276805080252416000, coefficient := (-71908655026276805080252416000) }, { argument := 5461416837438744689639424000, coefficient := (-5461416837438744689639424000) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 5643464065353369512627404800, coefficient := (-5643464065353369512627404800) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 197501667861547195396461166592, coefficient := (-197501667861547195396461166592) }, { argument := 2128870576862692261333303296000, coefficient := (-2128870576862692261333303296000) }, { argument := 197501818520717731400796602368, coefficient := (-197501818520717731400796602368) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-345186466206637003580282412990464)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3375, 7875, 88875, 3375, 7875, 6975,
    408460507, 42826347473, 461625220875, 21413190071, 408460507, 817004461,
    15903, 29123961427, 250263, 7533, 232991777003, 7533,
    7533, 645327, 7533, 250263, 645327, 6535950101,
    7533, 7533, 15903, 261625, 67275, 261625,
    231725, 10846225, 2952625, 67275, 10846225, 261625,
    261625, 112125, 261625, 2952625, 112125, 261625,
    231725, 13465731, 1411857609, 15218413875, 705929343, 13465731,
    674625, 173475, 674625, 597525, 27968025, 7613625,
    173475, 27968025, 674625, 674625, 289125, 674625,
    7613625, 289125, 674625, 597525
  ]
def negativeCoefficients : Array ℕ := #[
    127503895037480420769792000, 148754544210393824231424000, 1678801284660158873468928000, 127503895037480420769792000, 148754544210393824231424000, 131754024872063101462118400,
    1883691609211662205953507328, 197501667861547195396461166592, 2128870576862692261333303296000, 197501818520717731400796602368, 1883691609211662205953507328, 7535536099573008244290879488,
    150199588354151935666814976, 268621131428228913032924758016, 1181833603102406020115202048, 142294346861828149579087872, 268621230103321727819136892928, 142294346861828149579087872,
    142294346861828149579087872, 6094941190581639073637597184, 142294346861828149579087872, 1181833603102406020115202048, 6094941190581639073637597184, 7535437424480193458078744576,
    142294346861828149579087872, 142294346861828149579087872, 150199588354151935666814976, 1235489131080770929033216000, 1270788820540221527005593600, 1235489131080770929033216000,
    1094290373242968537143705600, 51219849405662817657919897600, 13943377336482986199089152000, 1270788820540221527005593600, 51219849405662817657919897600, 1235489131080770929033216000,
    1235489131080770929033216000, 1058990683783517939171328000, 1235489131080770929033216000, 13943377336482986199089152000, 1058990683783517939171328000, 1235489131080770929033216000,
    1094290373242968537143705600, 993595574089667976766685184, 104176703926969949220111384576, 1122920743839661852131852288000, 104176783395543418760859746304, 993595574089667976766685184,
    6371652977011868804579328000, 6553700204926493627567308800, 6371652977011868804579328000, 5643464065353369512627404800, 264150527704120618155560140800, 71908655026276805080252416000,
    6553700204926493627567308800, 264150527704120618155560140800, 6371652977011868804579328000, 6371652977011868804579328000, 5461416837438744689639424000, 6371652977011868804579328000,
    71908655026276805080252416000, 5461416837438744689639424000, 6371652977011868804579328000, 5643464065353369512627404800
  ]
def negativeScales : Array ℕ := #[
    11, 12, 16, 11, 12, 12,
    28, 35, 38, 34, 28, 29,
    13, 34, 17, 12, 37, 12,
    12, 19, 12, 17, 19, 32,
    12, 12, 13, 17, 16, 17,
    17, 23, 21, 16, 23, 17,
    17, 16, 17, 21, 16, 17,
    17, 23, 30, 33, 29, 23,
    19, 17, 19, 19, 24, 22,
    17, 24, 19, 19, 18, 19,
    22, 18, 19, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11720671786942400, 12943064217429565, 16439490034281534, 11720671786942400, 12943064217429565, 12767977501935366,
    28605621353732004, 35317779588341847, 38747931091696951, 34317780688864985, 28605621353732004, 29605768714887755,
    13957011337722461, 34761487552720179, 17933085494560247, 12879008816975791, 37761488082678641, 12879008816975791,
    12879008816975791, 19299670862465379, 12879008816975791, 17933085494560247, 19299670862465379, 32605749823199456,
    12879008816975791, 12879008816975791, 13957011337722461, 17997140903537453, 16037782865415143, 17997140903537453,
    17822054175365864, 23370689668039577, 21493566707037514, 16037782865415143, 23370689668039577, 17997140903537453,
    17997140903537453, 16774748459963978, 17997140903537453, 21493566707037514, 16774748459963978, 17997140903537453,
    17822054175365864, 23682789214295891, 30394947448864312, 33825098953073024, 29394948549387450, 23682789214295891,
    19363726256634727, 17404368241132080, 19363726256634727, 19188639550076635, 24737275043926354, 22860152084854098,
    17404368241132080, 24737275043926354, 19363726256634727, 19363726256634727, 18141333835298278, 19363726256634727,
    22860152084854098, 18141333835298278, 19363726256634727, 19188639550076635
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
noncomputable def negativeCeiling : ℝ := 43783517 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 197501667861547195396461166592, coefficient := (-197501667861547195396461166592) }, { argument := 2128870576862692261333303296000, coefficient := (-2128870576862692261333303296000) }, { argument := 197501818520717731400796602368, coefficient := (-197501818520717731400796602368) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 7535536099573008244290879488, coefficient := (-7535536099573008244290879488) }, { argument := 150199588354151935666814976, coefficient := (-150199588354151935666814976) }, { argument := 268621131428228913032924758016, coefficient := (-268621131428228913032924758016) }, { argument := 1181833603102406020115202048, coefficient := (-1181833603102406020115202048) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 268621230103321727819136892928, coefficient := (-268621230103321727819136892928) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 6094941190581639073637597184, coefficient := (-6094941190581639073637597184) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 1181833603102406020115202048, coefficient := (-1181833603102406020115202048) }, { argument := 6094941190581639073637597184, coefficient := (-6094941190581639073637597184) }, { argument := 7535437424480193458078744576, coefficient := (-7535437424480193458078744576) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 142294346861828149579087872, coefficient := (-142294346861828149579087872) }, { argument := 150199588354151935666814976, coefficient := (-150199588354151935666814976) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1270788820540221527005593600, coefficient := (-1270788820540221527005593600) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1094290373242968537143705600, coefficient := (-1094290373242968537143705600) }, { argument := 51219849405662817657919897600, coefficient := (-51219849405662817657919897600) }, { argument := 13943377336482986199089152000, coefficient := (-13943377336482986199089152000) }, { argument := 1270788820540221527005593600, coefficient := (-1270788820540221527005593600) }, { argument := 51219849405662817657919897600, coefficient := (-51219849405662817657919897600) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1058990683783517939171328000, coefficient := (-1058990683783517939171328000) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 13943377336482986199089152000, coefficient := (-13943377336482986199089152000) }, { argument := 1058990683783517939171328000, coefficient := (-1058990683783517939171328000) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1094290373242968537143705600, coefficient := (-1094290373242968537143705600) }, { argument := 993595574089667976766685184, coefficient := (-993595574089667976766685184) }, { argument := 104176703926969949220111384576, coefficient := (-104176703926969949220111384576) }, { argument := 1122920743839661852131852288000, coefficient := (-1122920743839661852131852288000) }, { argument := 104176783395543418760859746304, coefficient := (-104176783395543418760859746304) }, { argument := 993595574089667976766685184, coefficient := (-993595574089667976766685184) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 6553700204926493627567308800, coefficient := (-6553700204926493627567308800) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 5643464065353369512627404800, coefficient := (-5643464065353369512627404800) }, { argument := 264150527704120618155560140800, coefficient := (-264150527704120618155560140800) }, { argument := 71908655026276805080252416000, coefficient := (-71908655026276805080252416000) }, { argument := 6553700204926493627567308800, coefficient := (-6553700204926493627567308800) }, { argument := 264150527704120618155560140800, coefficient := (-264150527704120618155560140800) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 5461416837438744689639424000, coefficient := (-5461416837438744689639424000) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 71908655026276805080252416000, coefficient := (-71908655026276805080252416000) }, { argument := 5461416837438744689639424000, coefficient := (-5461416837438744689639424000) }, { argument := 6371652977011868804579328000, coefficient := (-6371652977011868804579328000) }, { argument := 5643464065353369512627404800, coefficient := (-5643464065353369512627404800) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
