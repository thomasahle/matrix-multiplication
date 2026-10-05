import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-22189721823795204328849724451848192)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    519416625, 298555620614436559, 535, 298555664304998705, 535, 7105475525,
    2074236683, 10165, 2074237173, 10165, 1633, 341,
    4815, 21935, 535, 229515, 10165, 535,
    10165, 19795, 373965, 19795, 229515, 373965,
    4815, 19795, 19795, 21935, 523961697, 61240950225,
    16766768655, 2073735947, 19795, 2073736437, 19795, 546036911,
    63821114175, 17473175265, 85903110227, 373965, 85903130541, 373965,
    10409, 533114049, 19795, 533114175, 19795, 10877,
    325284771, 38019474675, 10409109165, 23409314099, 229515, 23409319629,
    229515, 1633, 85903110227, 373965, 85903130541, 373965,
    10415, 5337, 15215376137932469, 4815
  ]
def negativeCoefficients : Array ℕ := #[
    598846596812810408165376000, 168071872718567957642841222545408, 161693828373456652116951040, 168071897314167882684478479400960, 161693828373456652116951040, 67109318928221191662700645580800,
    19131456619800603924694564864, 192011421193479774388879360, 19131461139252901983534710784, 192011421193479774388879360, 126347255259564124306891866112, 6595899271817416777196896256,
    181905556920138733631569920, 207170217603491335524843520, 161693828373456652116951040, 2167707886631653242442874880, 192011421193479774388879360, 161693828373456652116951040,
    192011421193479774388879360, 186958489056809254010224640, 7063999127065387489359298560, 186958489056809254010224640, 2167707886631653242442874880, 7063999127065387489359298560,
    181905556920138733631569920, 186958489056809254010224640, 186958489056809254010224640, 207170217603491335524843520, 19330774657971099499656904704, 70606008476960023851407769600,
    19330768145117519975578337280, 19126838145380357411675570176, 186958489056809254010224640, 19126842664832655470515716096, 186958489056809254010224640, 20145206304031839751191396352,
    73580734980326369342049484800, 20145199516782942130683248640, 792316344746565312625996988416, 7063999127065387489359298560, 792316532110144869293912752128, 7063999127065387489359298560,
    201339341701898801272265375744, 19668436848004107023960506368, 186958489056809254010224640, 19668441496583613598767513600, 186958489056809254010224640, 210391778239173144532465221632,
    12000889843424437235846479872, 43833469946662914435632332800, 12000885800128720579634135040, 215912813062666850937698516992, 2167707886631653242442874880, 215912864067914214744608735232,
    2167707886631653242442874880, 126347255259564124306891866112, 792316344746565312625996988416, 7063999127065387489359298560, 792316532110144869293912752128, 7063999127065387489359298560,
    3223286377289308890768594698240, 206465187177064828973019561984, 4282747644068412746074280689664, 181905556920138733631569920
  ]
def negativeScales : Array ℕ := #[
    28, 58, 9, 58, 9, 32,
    30, 13, 30, 13, 10, 8,
    12, 14, 9, 17, 13, 9,
    13, 14, 18, 14, 17, 18,
    12, 14, 14, 14, 28, 35,
    33, 30, 14, 30, 14, 29,
    35, 34, 36, 18, 36, 18,
    13, 28, 14, 28, 14, 13,
    28, 35, 33, 34, 17, 34,
    17, 10, 36, 18, 36, 18,
    13, 12, 53, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28952316961122897, 58050777342262024, 9063395081288510, 58050777553385675, 9063395081288510, 32726284057366455,
    30949933388206536, 13311322594732096, 30949933729016539, 13311322594732096, 10673309075599829, 8413627929024184,
    12233320082730822, 14420947085906609, 9063395081288510, 17808228919551386, 13311322594732096, 9063395081288510,
    13311322594732096, 14272848446917460, 18512543726664356, 14272848446917460, 17808228919551386, 18512543726664356,
    12233320082730822, 14272848446917460, 14272848446917460, 14420947085906609, 28964886123228136, 35833777618253350,
    33964885637160433, 30949585068900397, 14272848446917460, 30949585409792694, 14272848446917460, 29024423236831523,
    35893314747836377, 34024422750763928, 36321991315718589, 18512543726664356, 36321991656880900, 18512543726664356,
    13345543854110024, 28989868980738031, 14272848446917460, 28989869321715000, 14272848446917460, 13408993079342189,
    28277128039771587, 35146019546904059, 33277127553703992, 34446363612479160, 17808228919551386, 34446363953288062,
    17808228919551386, 10673309075599829, 36321991315718589, 18512543726664356, 36321991656880900, 18512543726664356,
    13346375218928010, 12381813295988320, 53756379517482666, 12233320082730822
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
noncomputable def negativeCeiling : ℝ := 266478263929 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 598846596812810408165376000, coefficient := (-598846596812810408165376000) }, { argument := 168071872718567957642841222545408, coefficient := (-168071872718567957642841222545408) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 168071897314167882684478479400960, coefficient := (-168071897314167882684478479400960) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 67109318928221191662700645580800, coefficient := (-67109318928221191662700645580800) }, { argument := 19131456619800603924694564864, coefficient := (-19131456619800603924694564864) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 19131461139252901983534710784, coefficient := (-19131461139252901983534710784) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 126347255259564124306891866112, coefficient := (-126347255259564124306891866112) }, { argument := 6595899271817416777196896256, coefficient := (-6595899271817416777196896256) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 161693828373456652116951040, coefficient := (-161693828373456652116951040) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 19330774657971099499656904704, coefficient := (-19330774657971099499656904704) }, { argument := 70606008476960023851407769600, coefficient := (-70606008476960023851407769600) }, { argument := 19330768145117519975578337280, coefficient := (-19330768145117519975578337280) }, { argument := 19126838145380357411675570176, coefficient := (-19126838145380357411675570176) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 19126842664832655470515716096, coefficient := (-19126842664832655470515716096) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 20145206304031839751191396352, coefficient := (-20145206304031839751191396352) }, { argument := 73580734980326369342049484800, coefficient := (-73580734980326369342049484800) }, { argument := 20145199516782942130683248640, coefficient := (-20145199516782942130683248640) }, { argument := 792316344746565312625996988416, coefficient := (-792316344746565312625996988416) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 792316532110144869293912752128, coefficient := (-792316532110144869293912752128) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 201339341701898801272265375744, coefficient := (-201339341701898801272265375744) }, { argument := 19668436848004107023960506368, coefficient := (-19668436848004107023960506368) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 19668441496583613598767513600, coefficient := (-19668441496583613598767513600) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 210391778239173144532465221632, coefficient := (-210391778239173144532465221632) }, { argument := 12000889843424437235846479872, coefficient := (-12000889843424437235846479872) }, { argument := 43833469946662914435632332800, coefficient := (-43833469946662914435632332800) }, { argument := 12000885800128720579634135040, coefficient := (-12000885800128720579634135040) }, { argument := 215912813062666850937698516992, coefficient := (-215912813062666850937698516992) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 215912864067914214744608735232, coefficient := (-215912864067914214744608735232) }, { argument := 2167707886631653242442874880, coefficient := (-2167707886631653242442874880) }, { argument := 126347255259564124306891866112, coefficient := (-126347255259564124306891866112) }, { argument := 792316344746565312625996988416, coefficient := (-792316344746565312625996988416) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 792316532110144869293912752128, coefficient := (-792316532110144869293912752128) }, { argument := 7063999127065387489359298560, coefficient := (-7063999127065387489359298560) }, { argument := 3223286377289308890768594698240, coefficient := (-3223286377289308890768594698240) }, { argument := 206465187177064828973019561984, coefficient := (-206465187177064828973019561984) }, { argument := 4282747644068412746074280689664, coefficient := (-4282747644068412746074280689664) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 310052032290481021745561232276979712
def positiveArguments : Array ℕ := #[
    40871, 489, 535, 489, 535, 21,
    3507, 91, 3773, 5649, 175, 5649,
    5887, 3507, 175, 217, 245, 105,
    2765, 245, 105, 245, 245, 10157,
    63, 2765, 10157, 217, 245, 63,
    245, 411, 11919, 10549, 685, 411
  ]
def positiveCoefficients : Array ℕ := #[
    3238134230120497741785734794182656, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 6499185206248246443220402176,
    135670491180432144502225895424, 7040783973435600313488769024, 145960867756991868037324865536, 218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168,
    227742281602282302447848259584, 135670491180432144502225895424, 6769984589841923378354585600, 67158247131231879913277489152, 75823827406229541837571358720, 64991852062482464432204021760,
    855726052156019115024019619840, 75823827406229541837571358720, 64991852062482464432204021760, 75823827406229541837571358720, 75823827406229541837571358720, 3143439244755401863037601185792,
    77990222474978957318644826112, 855726052156019115024019619840, 3143439244755401863037601185792, 67158247131231879913277489152, 75823827406229541837571358720, 77990222474978957318644826112,
    75823827406229541837571358720, 15899792379571602905735626752, 230546989503788242133166587904, 408094671075671141247214419968, 13249826982976335754779688960, 254396678073145646491770028032
  ]
def positiveScales : Array ℕ := #[
    15, 8, 9, 8, 9, 4,
    11, 6, 11, 12, 7, 12,
    12, 11, 7, 7, 7, 6,
    11, 7, 6, 7, 7, 13,
    5, 11, 13, 7, 7, 5,
    7, 8, 13, 13, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    15215378408714571, 4815, 696598301, 10409, 16231775, 1897179375,
    519416625, 2073735947, 19795, 2073736437, 19795, 341,
    533114049, 19795, 533114175, 19795, 5337, 341,
    2075738891, 21935, 2075739381, 21935, 10409, 5439,
    4412491, 1, 7, 7
  ]
def negativeCoefficients : Array ℕ := #[
    4282748283236752021498758168576, 181905556920138733631569920, 6579184937332680920666831060992, 201339341701898801272265375744, 598846798574073714363596800, 2187298899534077566648320000,
    598846596812810408165376000, 19126838145380357411675570176, 186958489056809254010224640, 19126842664832655470515716096, 186958489056809254010224640, 6595899271817416777196896256,
    19668436848004107023960506368, 186958489056809254010224640, 19668441496583613598767513600, 186958489056809254010224640, 206465187177064828973019561984, 6595899271817416777196896256,
    19145312043061343463751548928, 207170217603491335524843520, 19145316562513641522591694848, 207170217603491335524843520, 201339341701898801272265375744, 210411121052286978599260520448,
    41674799208727927357253353472, 158456325028528675187087900672, 1109194275199700726309615304704, 8873554201597605810476922437632
  ]
def negativeScales : Array ℕ := #[
    53, 12, 29, 13, 23, 30,
    28, 30, 14, 30, 14, 8,
    28, 14, 28, 14, 12, 8,
    30, 14, 30, 14, 13, 12,
    22, 0, 2, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15318789922085690, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509, 4392317422778759,
    11776021715228447, 6507794640198673, 11881496384617007, 12463779785335379, 7451211111832325, 12463779785335379,
    12523316912312711, 11776021715228447, 7451211111832325, 7761551232426566, 7936637938489789, 6714245517659862,
    11433063765122067, 7936637938489789, 6714245517659862, 7936637938489789, 7936637938489789, 13310186726124348,
    5977279922488012, 11433063765122067, 13310186726124348, 7761551232426566, 7936637938489789, 5977279922488012,
    7936637938489789, 8682994583678684, 13540975578809191, 13364818623655427, 9419960177847887, 8682994583678684
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    53756379732794191, 12233320082730822, 29375751713301367, 13345543854110024, 23952317447190580, 30821208944473030,
    28952316961122897, 30949585068900397, 14272848446917460, 30949585409792694, 14272848446917460, 8413627929024184,
    28989868980738031, 14272848446917460, 28989869321715000, 14272848446917460, 12381813295988320, 8413627929024184,
    30950977841829076, 14420947085906609, 30950978182392437, 14420947085906609, 13345543854110024, 12409125710465324,
    22073161905097543, 0, 2807354922807594, 2807354922807594
  ]

abbrev PositiveTerm := Fin 36
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
noncomputable def positiveFloor : ℝ := 598722045061 / 1000000000000
noncomputable def negativeCeiling : ℝ := 44943343 / 8000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4282748283236752021498758168576, coefficient := (-4282748283236752021498758168576) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 6579184937332680920666831060992, coefficient := (-6579184937332680920666831060992) }, { argument := 201339341701898801272265375744, coefficient := (-201339341701898801272265375744) }, { argument := 598846798574073714363596800, coefficient := (-598846798574073714363596800) }, { argument := 2187298899534077566648320000, coefficient := (-2187298899534077566648320000) }, { argument := 598846596812810408165376000, coefficient := (-598846596812810408165376000) }, { argument := 19126838145380357411675570176, coefficient := (-19126838145380357411675570176) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 19126842664832655470515716096, coefficient := (-19126842664832655470515716096) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 6595899271817416777196896256, coefficient := (-6595899271817416777196896256) }, { argument := 19668436848004107023960506368, coefficient := (-19668436848004107023960506368) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 19668441496583613598767513600, coefficient := (-19668441496583613598767513600) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 206465187177064828973019561984, coefficient := (-206465187177064828973019561984) }, { argument := 6595899271817416777196896256, coefficient := (-6595899271817416777196896256) }, { argument := 19145312043061343463751548928, coefficient := (-19145312043061343463751548928) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 19145316562513641522591694848, coefficient := (-19145316562513641522591694848) }, { argument := 207170217603491335524843520, coefficient := (-207170217603491335524843520) }, { argument := 201339341701898801272265375744, coefficient := (-201339341701898801272265375744) }, { argument := 210411121052286978599260520448, coefficient := (-210411121052286978599260520448) }, { argument := 41674799208727927357253353472, coefficient := (-41674799208727927357253353472) }, { argument := 3238134230120497741785734794182656, coefficient := 3238134230120497741785734794182656 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 227742281602282302447848259584, coefficient := 227742281602282302447848259584 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 67158247131231879913277489152, coefficient := 67158247131231879913277489152 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 855726052156019115024019619840, coefficient := 855726052156019115024019619840 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 3143439244755401863037601185792, coefficient := 3143439244755401863037601185792 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 855726052156019115024019619840, coefficient := 855726052156019115024019619840 }, { argument := 3143439244755401863037601185792, coefficient := 3143439244755401863037601185792 }, { argument := 67158247131231879913277489152, coefficient := 67158247131231879913277489152 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 77990222474978957318644826112, coefficient := 77990222474978957318644826112 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 8873554201597605810476922437632, coefficient := (-8873554201597605810476922437632) }, { argument := 15899792379571602905735626752, coefficient := 15899792379571602905735626752 }, { argument := 230546989503788242133166587904, coefficient := 230546989503788242133166587904 }, { argument := 408094671075671141247214419968, coefficient := 408094671075671141247214419968 }, { argument := 13249826982976335754779688960, coefficient := 13249826982976335754779688960 }, { argument := 254396678073145646491770028032, coefficient := 254396678073145646491770028032 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12
