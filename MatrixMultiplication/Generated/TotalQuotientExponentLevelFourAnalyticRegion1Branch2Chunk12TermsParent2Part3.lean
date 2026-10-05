import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3975906214526893045119869559767040)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5040671971, 528505364969, 5696759593875, 264252884063, 5040671971, 10127546913,
    744363, 344345554911, 11713923, 352593, 2754765449943, 352593,
    352593, 30205467, 352593, 11713923, 30205467, 81019364649,
    352593, 352593, 744363, 201985965, 21177864135, 228276208125,
    10588940145, 201985965, 672021141, 202635, 24161327547, 3188835,
    95985, 193290691395, 95985, 95985, 8222715, 95985,
    3188835, 8222715, 5376098109, 95985, 95985, 202635,
    173237579711, 596219833909, 43309394051, 8516628424075, 451683306388085, 688968735,
    6443128509, 79638870385, 5302583333, 112920820721975, 79638870385, 688968735,
    5376823333, 5360439333, 5376823333, 5302583333, 5360439333, 2129162981065,
    6443128509, 3431408504267, 439400174527967, 42886026911
  ]
def negativeCoefficients : Array ℕ := #[
    23245996452139523706437238784, 2437300802291401103628855934976, 26271666569415422082168127488000, 2437302661524901234759281147904, 23245996452139523706437238784, 93410132999299106963617480704,
    7030309764576595440404791296, 3176027162181358118726258393088, 55317437358115843070553489408, 6660293461177827259330854912, 3176028327387241357159188922368, 6660293461177827259330854912,
    6660293461177827259330854912, 285282569920450267608004952064, 6660293461177827259330854912, 55317437358115843070553489408, 285282569920450267608004952064, 93408967793415868530686951424,
    6660293461177827259330854912, 6660293461177827259330854912, 7030309764576595440404791296, 1862991701418127456437534720, 195331319863068654787708846080, 2105476394699365972747223040000,
    195331468866643910176612024320, 1862991701418127456437534720, 198345632002388495673323421696, 1913833464512581115754577920, 7131165211849241406986866655232, 15058847523401625095016284160,
    1813105387432971583346442240, 7131167831987876148544159088640, 1813105387432971583346442240, 1813105387432971583346442240, 77661347428378949486672609280, 1813105387432971583346442240,
    15058847523401625095016284160, 77661347428378949486672609280, 198343011863753754116030988288, 1813105387432971583346442240, 1813105387432971583346442240, 1913833464512581115754577920,
    199729331054854706721179303936, 687394667986808682374898909184, 199729327011558990064966959104, 19177742298558572292315545600, 1017100385169426590763927470080, 6354614964666208267146362880,
    7428421414971550587666038784, 91817366269463866705193205760, 195630795346737583763809632256, 1017100332251714386195067699200, 91817366269463866705193205760, 6354614964666208267146362880,
    6199055247087561812117291008, 6180165781156083231262507008, 6199055247087561812117291008, 195630795346737583763809632256, 6180165781156083231262507008, 19177795216270776861175316480,
    7428421414971550587666038784, 30907380122345624467211812864, 3957764924541366178660445323264, 197776890691359399550379884544
  ]
def negativeScales : Array ℕ := #[
    32, 38, 42, 37, 32, 33,
    19, 38, 23, 18, 41, 18,
    18, 24, 18, 23, 24, 36,
    18, 18, 19, 27, 34, 37,
    33, 27, 29, 17, 34, 21,
    16, 37, 16, 16, 22, 16,
    21, 22, 32, 16, 16, 17,
    37, 39, 35, 42, 48, 29,
    32, 36, 32, 46, 36, 29,
    32, 32, 32, 32, 32, 40,
    32, 41, 48, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32230968925927308, 38943127169821250, 42373278663683933, 37943128270344562, 32230968925927308, 33237565716790662,
    19505646819674126, 38325066097444556, 23481720980428464, 18427644307672546, 41325066626733619, 18427644307672546,
    18427644307672546, 24848306357822211, 18427644307672546, 23481720980428464, 24848306357822211, 36237547720378707,
    18427644307672546, 18427644307672546, 19505646819674126, 27589679809860620, 34301838044472825, 37731989547763934,
    33301839144995963, 27589679809860620, 29323931378317380, 17628523858683737, 34491980674764297, 21604598019432458,
    16550521346671598, 37491981204840408, 16550521346671598, 16550521346671598, 22971183409984650, 16550521346671598,
    21604598019432458, 22971183409984650, 32323912320242120, 16550521346671598, 16550521346671598, 17628523858683737,
    37333960965637631, 39117053412726780, 35333960936431892, 42953419556837322, 48682304923148847, 29359863274853029,
    32585114223768435, 36212753706577990, 32304048242662628, 46682304848088288, 36212753706577990, 29359863274853029,
    32324106923555380, 32319704100483882, 32324106923555380, 32304048242662628, 32319704100483882, 40953423537703716,
    32585114223768435, 41641938025563383, 48642528771234592, 35319788615481231
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
noncomputable def negativeCeiling : ℝ := 6172302517 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23245996452139523706437238784, coefficient := (-23245996452139523706437238784) }, { argument := 2437300802291401103628855934976, coefficient := (-2437300802291401103628855934976) }, { argument := 26271666569415422082168127488000, coefficient := (-26271666569415422082168127488000) }, { argument := 2437302661524901234759281147904, coefficient := (-2437302661524901234759281147904) }, { argument := 23245996452139523706437238784, coefficient := (-23245996452139523706437238784) }, { argument := 93410132999299106963617480704, coefficient := (-93410132999299106963617480704) }, { argument := 7030309764576595440404791296, coefficient := (-7030309764576595440404791296) }, { argument := 3176027162181358118726258393088, coefficient := (-3176027162181358118726258393088) }, { argument := 55317437358115843070553489408, coefficient := (-55317437358115843070553489408) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 3176028327387241357159188922368, coefficient := (-3176028327387241357159188922368) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 285282569920450267608004952064, coefficient := (-285282569920450267608004952064) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 55317437358115843070553489408, coefficient := (-55317437358115843070553489408) }, { argument := 285282569920450267608004952064, coefficient := (-285282569920450267608004952064) }, { argument := 93408967793415868530686951424, coefficient := (-93408967793415868530686951424) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 7030309764576595440404791296, coefficient := (-7030309764576595440404791296) }, { argument := 1862991701418127456437534720, coefficient := (-1862991701418127456437534720) }, { argument := 195331319863068654787708846080, coefficient := (-195331319863068654787708846080) }, { argument := 2105476394699365972747223040000, coefficient := (-2105476394699365972747223040000) }, { argument := 195331468866643910176612024320, coefficient := (-195331468866643910176612024320) }, { argument := 1862991701418127456437534720, coefficient := (-1862991701418127456437534720) }, { argument := 198345632002388495673323421696, coefficient := (-198345632002388495673323421696) }, { argument := 1913833464512581115754577920, coefficient := (-1913833464512581115754577920) }, { argument := 7131165211849241406986866655232, coefficient := (-7131165211849241406986866655232) }, { argument := 15058847523401625095016284160, coefficient := (-15058847523401625095016284160) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 7131167831987876148544159088640, coefficient := (-7131167831987876148544159088640) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 77661347428378949486672609280, coefficient := (-77661347428378949486672609280) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 15058847523401625095016284160, coefficient := (-15058847523401625095016284160) }, { argument := 77661347428378949486672609280, coefficient := (-77661347428378949486672609280) }, { argument := 198343011863753754116030988288, coefficient := (-198343011863753754116030988288) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 1813105387432971583346442240, coefficient := (-1813105387432971583346442240) }, { argument := 1913833464512581115754577920, coefficient := (-1913833464512581115754577920) }, { argument := 199729331054854706721179303936, coefficient := (-199729331054854706721179303936) }, { argument := 687394667986808682374898909184, coefficient := (-687394667986808682374898909184) }, { argument := 199729327011558990064966959104, coefficient := (-199729327011558990064966959104) }, { argument := 19177742298558572292315545600, coefficient := (-19177742298558572292315545600) }, { argument := 1017100385169426590763927470080, coefficient := (-1017100385169426590763927470080) }, { argument := 6354614964666208267146362880, coefficient := (-6354614964666208267146362880) }, { argument := 7428421414971550587666038784, coefficient := (-7428421414971550587666038784) }, { argument := 91817366269463866705193205760, coefficient := (-91817366269463866705193205760) }, { argument := 195630795346737583763809632256, coefficient := (-195630795346737583763809632256) }, { argument := 1017100332251714386195067699200, coefficient := (-1017100332251714386195067699200) }, { argument := 91817366269463866705193205760, coefficient := (-91817366269463866705193205760) }, { argument := 6354614964666208267146362880, coefficient := (-6354614964666208267146362880) }, { argument := 6199055247087561812117291008, coefficient := (-6199055247087561812117291008) }, { argument := 6180165781156083231262507008, coefficient := (-6180165781156083231262507008) }, { argument := 6199055247087561812117291008, coefficient := (-6199055247087561812117291008) }, { argument := 195630795346737583763809632256, coefficient := (-195630795346737583763809632256) }, { argument := 6180165781156083231262507008, coefficient := (-6180165781156083231262507008) }, { argument := 19177795216270776861175316480, coefficient := (-19177795216270776861175316480) }, { argument := 7428421414971550587666038784, coefficient := (-7428421414971550587666038784) }, { argument := 30907380122345624467211812864, coefficient := (-30907380122345624467211812864) }, { argument := 3957764924541366178660445323264, coefficient := (-3957764924541366178660445323264) }, { argument := 197776890691359399550379884544, coefficient := (-197776890691359399550379884544) }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7367922902820069889367528911667200)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17541390886591565, 1413825063, 3298925147, 42886026911, 42886026911, 1413825063,
    529241848583, 21207375945, 439400182247903, 42886026911, 3298925147, 21207375945,
    3298925147, 42886026911, 42886026911, 14207620325775, 112250044219099, 4617,
    4193863059439909, 72657, 2187, 33549149896000583, 2187, 2187,
    187353, 2187, 72657, 187353, 899754933271481, 2187,
    2187, 4617, 408460507, 42826347473, 461625220875, 21413190071,
    408460507, 10127546913, 744363, 344345554911, 11713923, 352593,
    2754765449943, 352593, 352593, 30205467, 352593, 11713923,
    30205467, 81019364649, 352593, 352593, 744363, 784225516030771,
    1412922276278989, 784225510002483, 87391855, 17955, 3098725585, 282555,
    8505, 24789813785, 8505, 8505
  ]
def negativeCoefficients : Array ℕ := #[
    39499700730206993296632441733120, 104321876408629133828771807232, 7606803488129207675014610944, 197776890691359399550379884544, 197776890691359399550379884544, 104321876408629133828771807232,
    2440697233476885776868973740032, 195603518266179625928947138560, 3957764994076367964508600139776, 197776890691359399550379884544, 7606803488129207675014610944, 195603518266179625928947138560,
    7606803488129207675014610944, 197776890691359399550379884544, 197776890691359399550379884544, 31992716802490887493071667200, 1011058514634911910118144606208, 174425328411273215613075456,
    37774960223472924978768383049728, 1372451926183439249166041088, 165245047968574625317650432, 37772984742556285057612793249792, 165245047968574625317650432, 165245047968574625317650432,
    7077996221320613117772693504, 165245047968574625317650432, 1372451926183439249166041088, 7077996221320613117772693504, 1013033995551551831273734406144, 165245047968574625317650432,
    165245047968574625317650432, 174425328411273215613075456, 1883691609211662205953507328, 197501667861547195396461166592, 2128870576862692261333303296000, 197501818520717731400796602368,
    1883691609211662205953507328, 93410132999299106963617480704, 7030309764576595440404791296, 3176027162181358118726258393088, 55317437358115843070553489408, 6660293461177827259330854912,
    3176028327387241357159188922368, 6660293461177827259330854912, 6660293461177827259330854912, 285282569920450267608004952064, 6660293461177827259330854912, 55317437358115843070553489408,
    285282569920450267608004952064, 93408967793415868530686951424, 6660293461177827259330854912, 6660293461177827259330854912, 7030309764576595440404791296, 882959435442653803227438383104,
    3181618118476763930004681654272, 882959428655404905606930235392, 6448380733246937787761950720, 169580180399848959623823360, 228645591284603653805509181440, 1334328261567232603355873280,
    160654907747225330169937920, 228645675263406049368242913280, 160654907747225330169937920, 160654907747225330169937920
  ]
def negativeScales : Array ℕ := #[
    53, 30, 31, 35, 35, 30,
    38, 34, 48, 35, 31, 34,
    31, 35, 35, 43, 46, 12,
    51, 16, 11, 54, 11, 11,
    17, 11, 16, 17, 49, 11,
    11, 12, 28, 35, 38, 34,
    28, 33, 19, 38, 23, 18,
    41, 18, 18, 24, 18, 23,
    24, 36, 18, 18, 19, 49,
    50, 49, 26, 14, 31, 18,
    13, 34, 13, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    53961612676914575, 30396956476003697, 31619348897349714, 35319788615481231, 35319788615481231, 30396956476003697,
    38945136197283019, 34303847071612210, 48642528796581676, 35319788615481231, 31619348897349714, 34303847071612210,
    31619348897349714, 35319788615481231, 35319788615481231, 43691730167366578, 46673709341754618, 12172740017049367,
    51897201181914093, 16148814177803887, 11094737505048094, 54897125732694752, 11094737505048094, 11094737505048094,
    17515399553521265, 11094737505048094, 16148814177803887, 17515399553521265, 49676525435796925, 11094737505048094,
    11094737505048094, 12172740017049367, 28605621353732004, 35317779588341847, 38747931091696951, 34317780688864985,
    28605621353732004, 33237565716790662, 19505646819674126, 38325066097444556, 23481720980428464, 18427644307672546,
    41325066626733619, 18427644307672546, 18427644307672546, 24848306357822211, 18427644307672546, 23481720980428464,
    24848306357822211, 36237547720378707, 18427644307672546, 18427644307672546, 19505646819674126, 49478261911430706,
    50327603529668105, 49478261900340808, 26380995489719092, 14132098032552021, 31529027853283808, 18108172193306541,
    13054095520550748, 34529028383168416, 13054095520550748, 13054095520550748
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
noncomputable def negativeCeiling : ℝ := 43598908671 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39499700730206993296632441733120, coefficient := (-39499700730206993296632441733120) }, { argument := 104321876408629133828771807232, coefficient := (-104321876408629133828771807232) }, { argument := 7606803488129207675014610944, coefficient := (-7606803488129207675014610944) }, { argument := 197776890691359399550379884544, coefficient := (-197776890691359399550379884544) }, { argument := 197776890691359399550379884544, coefficient := (-197776890691359399550379884544) }, { argument := 104321876408629133828771807232, coefficient := (-104321876408629133828771807232) }, { argument := 2440697233476885776868973740032, coefficient := (-2440697233476885776868973740032) }, { argument := 195603518266179625928947138560, coefficient := (-195603518266179625928947138560) }, { argument := 3957764994076367964508600139776, coefficient := (-3957764994076367964508600139776) }, { argument := 197776890691359399550379884544, coefficient := (-197776890691359399550379884544) }, { argument := 7606803488129207675014610944, coefficient := (-7606803488129207675014610944) }, { argument := 195603518266179625928947138560, coefficient := (-195603518266179625928947138560) }, { argument := 7606803488129207675014610944, coefficient := (-7606803488129207675014610944) }, { argument := 197776890691359399550379884544, coefficient := (-197776890691359399550379884544) }, { argument := 197776890691359399550379884544, coefficient := (-197776890691359399550379884544) }, { argument := 31992716802490887493071667200, coefficient := (-31992716802490887493071667200) }, { argument := 1011058514634911910118144606208, coefficient := (-1011058514634911910118144606208) }, { argument := 174425328411273215613075456, coefficient := (-174425328411273215613075456) }, { argument := 37774960223472924978768383049728, coefficient := (-37774960223472924978768383049728) }, { argument := 1372451926183439249166041088, coefficient := (-1372451926183439249166041088) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 37772984742556285057612793249792, coefficient := (-37772984742556285057612793249792) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 7077996221320613117772693504, coefficient := (-7077996221320613117772693504) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 1372451926183439249166041088, coefficient := (-1372451926183439249166041088) }, { argument := 7077996221320613117772693504, coefficient := (-7077996221320613117772693504) }, { argument := 1013033995551551831273734406144, coefficient := (-1013033995551551831273734406144) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 174425328411273215613075456, coefficient := (-174425328411273215613075456) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 197501667861547195396461166592, coefficient := (-197501667861547195396461166592) }, { argument := 2128870576862692261333303296000, coefficient := (-2128870576862692261333303296000) }, { argument := 197501818520717731400796602368, coefficient := (-197501818520717731400796602368) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 93410132999299106963617480704, coefficient := (-93410132999299106963617480704) }, { argument := 7030309764576595440404791296, coefficient := (-7030309764576595440404791296) }, { argument := 3176027162181358118726258393088, coefficient := (-3176027162181358118726258393088) }, { argument := 55317437358115843070553489408, coefficient := (-55317437358115843070553489408) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 3176028327387241357159188922368, coefficient := (-3176028327387241357159188922368) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 285282569920450267608004952064, coefficient := (-285282569920450267608004952064) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 55317437358115843070553489408, coefficient := (-55317437358115843070553489408) }, { argument := 285282569920450267608004952064, coefficient := (-285282569920450267608004952064) }, { argument := 93408967793415868530686951424, coefficient := (-93408967793415868530686951424) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 6660293461177827259330854912, coefficient := (-6660293461177827259330854912) }, { argument := 7030309764576595440404791296, coefficient := (-7030309764576595440404791296) }, { argument := 882959435442653803227438383104, coefficient := (-882959435442653803227438383104) }, { argument := 3181618118476763930004681654272, coefficient := (-3181618118476763930004681654272) }, { argument := 882959428655404905606930235392, coefficient := (-882959428655404905606930235392) }, { argument := 6448380733246937787761950720, coefficient := (-6448380733246937787761950720) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 228645591284603653805509181440, coefficient := (-228645591284603653805509181440) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 228645675263406049368242913280, coefficient := (-228645675263406049368242913280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
