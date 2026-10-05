import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 18, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-658613291372271098107482322501632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1144093603, 18899531571, 30769372501, 7977565257, 780140451, 7977565257,
    15929964693, 1146036131, 18899531571, 780140451, 3078575841687, 47863838316649,
    8713886571, 22472654841, 18803649969, 526043573523, 11951284927781, 18803649969,
    16969147533, 8713886571, 8713886571, 16969147533, 526043573523, 16969147533,
    769642592315, 22472654841, 10310335, 2044898625, 2044898625, 10310335,
    452929202061, 119428765861779, 3211543155, 4029311937166233, 1016311125, 121957335,
    3211543155, 6382433865, 1016311125, 98500874235, 6301128975, 477715473446011,
    3211543155, 121957335, 6301128975, 121957335, 3211543155, 3211543155,
    452929202061, 8542849, 1694344575, 1694344575, 8542849, 5722165,
    3686463135, 39207085703, 1843237123, 5722165, 14030898249, 11000915,
    268250867795, 115107135, 5097985, 536501650009
  ]
def negativeCoefficients : Array ℕ := #[
    2638100236363657310482989056, 43579352750403852731355758592, 70949342479322924319298813952, 36790026156798991520212451328, 1798881405143168355089252352, 36790026156798991520212451328,
    36731997724375018347467636736, 2642579400972659168968179712, 43579352750403852731355758592, 1798881405143168355089252352, 55458692053813537143162667008, 862238257629528419723552751616,
    40185708865642873995273437184, 51818414063592126993905221632, 693732237259519087918404599808, 1212973896549799380857332432896, 861180837557650188772642390016, 693732237259519087918404599808,
    39128190211283850995397820416, 40185708865642873995273437184, 40185708865642873995273437184, 39128190211283850995397820416, 1212973896549799380857332432896, 39128190211283850995397820416,
    55458593471332745094197411840, 51818414063592126993905221632, 190192111059210169860751360, 37721721592055560748924928000, 37721721592055560748924928000, 190192111059210169860751360,
    4079623571254271377787584512, 268929672716213058996579336192, 59242514661958725950483988480, 2268300967347667291408428957696, 37495262444277674652205056000, 2249715746656660479132303360,
    59242514661958725950483988480, 58867562037515949203961937920, 37495262444277674652205056000, 908510209024848056822928506880, 58117656788630395710917836800, 268929903525071902035968786432,
    59242514661958725950483988480, 2249715746656660479132303360, 58117656788630395710917836800, 2249715746656660479132303360, 59242514661958725950483988480, 59242514661958725950483988480,
    4079623571254271377787584512, 9849234322709098082074624, 1953446296731448681640755200, 1953446296731448681640755200, 9849234322709098082074624, 105555313302538216422768640,
    34001620994254992364881838080, 361621537919618869669107073024, 34001723475141693858295840768, 105555313302538216422768640, 4044131080055663667242336256, 101465531790816256007864320,
    154636097055151895805385768960, 1061675930201467654326190080, 94041224586610188495093760, 154636072388108074365743005696
  ]
def negativeScales : Array ℕ := #[
    30, 34, 34, 32, 29, 32,
    33, 30, 34, 29, 41, 45,
    33, 34, 34, 38, 43, 34,
    33, 33, 33, 33, 38, 33,
    39, 34, 23, 30, 30, 23,
    38, 46, 31, 51, 29, 26,
    31, 32, 29, 36, 32, 48,
    31, 26, 32, 26, 31, 31,
    38, 23, 30, 30, 23, 22,
    31, 35, 30, 22, 33, 23,
    37, 26, 22, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30091557943742117, 34137631426252767, 34840775972516475, 32893301362749349, 29539158639126325, 32893301362749349,
    33891024021881933, 30094005382542534, 34137631426252767, 29539158639126325, 41485400248886739, 45444001328246581,
    33020669187744178, 34387451518415804, 34130293678918676, 38936391358585071, 43442230969673290, 34130293678918676,
    33982195057703251, 33020669187744178, 33020669187744178, 33982195057703251, 38936391358585071, 33982195057703251,
    39485397684372912, 34387451518415804, 23297587873249950, 30929382185246576, 30929382185246576, 23297587873249950,
    38720494602277151, 46763143697718353, 31580619536729052, 51839454923629631, 29920694984623743, 26861801291435908,
    31580619536729052, 32571459537442814, 29920694984623743, 36519417478000530, 32552963193824364, 48763144935910672,
    31580619536729052, 26861801291435908, 32552963193824364, 26861801291435908, 31580619536729052, 31580619536729052,
    38720494602277151, 23026285851432555, 30658080156127340, 30658080156127340, 23026285851432555, 22448129668042580,
    31779590184357093, 35190395357928187, 30779594532633476, 22448129668042580, 33707888321275264, 23391120188967178,
    37964791895240383, 26778402022261855, 22281495697792675, 38964791665106325
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
noncomputable def negativeCeiling : ℝ := 5626687981 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2638100236363657310482989056, coefficient := (-2638100236363657310482989056) }, { argument := 43579352750403852731355758592, coefficient := (-43579352750403852731355758592) }, { argument := 70949342479322924319298813952, coefficient := (-70949342479322924319298813952) }, { argument := 36790026156798991520212451328, coefficient := (-36790026156798991520212451328) }, { argument := 1798881405143168355089252352, coefficient := (-1798881405143168355089252352) }, { argument := 36790026156798991520212451328, coefficient := (-36790026156798991520212451328) }, { argument := 36731997724375018347467636736, coefficient := (-36731997724375018347467636736) }, { argument := 2642579400972659168968179712, coefficient := (-2642579400972659168968179712) }, { argument := 43579352750403852731355758592, coefficient := (-43579352750403852731355758592) }, { argument := 1798881405143168355089252352, coefficient := (-1798881405143168355089252352) }, { argument := 55458692053813537143162667008, coefficient := (-55458692053813537143162667008) }, { argument := 862238257629528419723552751616, coefficient := (-862238257629528419723552751616) }, { argument := 40185708865642873995273437184, coefficient := (-40185708865642873995273437184) }, { argument := 51818414063592126993905221632, coefficient := (-51818414063592126993905221632) }, { argument := 693732237259519087918404599808, coefficient := (-693732237259519087918404599808) }, { argument := 1212973896549799380857332432896, coefficient := (-1212973896549799380857332432896) }, { argument := 861180837557650188772642390016, coefficient := (-861180837557650188772642390016) }, { argument := 693732237259519087918404599808, coefficient := (-693732237259519087918404599808) }, { argument := 39128190211283850995397820416, coefficient := (-39128190211283850995397820416) }, { argument := 40185708865642873995273437184, coefficient := (-40185708865642873995273437184) }, { argument := 40185708865642873995273437184, coefficient := (-40185708865642873995273437184) }, { argument := 39128190211283850995397820416, coefficient := (-39128190211283850995397820416) }, { argument := 1212973896549799380857332432896, coefficient := (-1212973896549799380857332432896) }, { argument := 39128190211283850995397820416, coefficient := (-39128190211283850995397820416) }, { argument := 55458593471332745094197411840, coefficient := (-55458593471332745094197411840) }, { argument := 51818414063592126993905221632, coefficient := (-51818414063592126993905221632) }, { argument := 190192111059210169860751360, coefficient := (-190192111059210169860751360) }, { argument := 37721721592055560748924928000, coefficient := (-37721721592055560748924928000) }, { argument := 37721721592055560748924928000, coefficient := (-37721721592055560748924928000) }, { argument := 190192111059210169860751360, coefficient := (-190192111059210169860751360) }, { argument := 4079623571254271377787584512, coefficient := (-4079623571254271377787584512) }, { argument := 268929672716213058996579336192, coefficient := (-268929672716213058996579336192) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 2268300967347667291408428957696, coefficient := (-2268300967347667291408428957696) }, { argument := 37495262444277674652205056000, coefficient := (-37495262444277674652205056000) }, { argument := 2249715746656660479132303360, coefficient := (-2249715746656660479132303360) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 58867562037515949203961937920, coefficient := (-58867562037515949203961937920) }, { argument := 37495262444277674652205056000, coefficient := (-37495262444277674652205056000) }, { argument := 908510209024848056822928506880, coefficient := (-908510209024848056822928506880) }, { argument := 58117656788630395710917836800, coefficient := (-58117656788630395710917836800) }, { argument := 268929903525071902035968786432, coefficient := (-268929903525071902035968786432) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 2249715746656660479132303360, coefficient := (-2249715746656660479132303360) }, { argument := 58117656788630395710917836800, coefficient := (-58117656788630395710917836800) }, { argument := 2249715746656660479132303360, coefficient := (-2249715746656660479132303360) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 59242514661958725950483988480, coefficient := (-59242514661958725950483988480) }, { argument := 4079623571254271377787584512, coefficient := (-4079623571254271377787584512) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 1953446296731448681640755200, coefficient := (-1953446296731448681640755200) }, { argument := 9849234322709098082074624, coefficient := (-9849234322709098082074624) }, { argument := 105555313302538216422768640, coefficient := (-105555313302538216422768640) }, { argument := 34001620994254992364881838080, coefficient := (-34001620994254992364881838080) }, { argument := 361621537919618869669107073024, coefficient := (-361621537919618869669107073024) }, { argument := 34001723475141693858295840768, coefficient := (-34001723475141693858295840768) }, { argument := 105555313302538216422768640, coefficient := (-105555313302538216422768640) }, { argument := 4044131080055663667242336256, coefficient := (-4044131080055663667242336256) }, { argument := 101465531790816256007864320, coefficient := (-101465531790816256007864320) }, { argument := 154636097055151895805385768960, coefficient := (-154636097055151895805385768960) }, { argument := 1061675930201467654326190080, coefficient := (-1061675930201467654326190080) }, { argument := 94041224586610188495093760, coefficient := (-94041224586610188495093760) }, { argument := 154636072388108074365743005696, coefficient := (-154636072388108074365743005696) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9988484410627605045755805626793984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5097985, 9927655, 187552185, 9927655, 115107135, 187552185,
    1753865847, 9927655, 9927655, 11000915, 1144093789, 18899536077,
    30769375915, 7977567159, 780140637, 7977567159, 15929968491, 1146036317,
    18899536077, 780140637, 355069630812839, 5640700324949337, 31343590863, 80833471173,
    67636169757, 1892163090519, 1408485986561205, 67636169757, 61037519049, 31343590863,
    31343590863, 61037519049, 1892163090519, 61037519049, 88767247798091, 80833471173,
    8653414285495, 2077473028141737, 125683613069, 67833242302487707, 39773295275, 4772795433,
    125683613069, 249776294327, 39773295275, 3854827778053, 246594430705, 8309897062334945,
    125683613069, 4772795433, 246594430705, 4772795433, 125683613069, 125683613069,
    8653414285495, 57443295, 11393006625, 11393006625, 57443295, 59873385,
    38572992315, 410239994307, 19286554287, 59873385
  ]
def negativeCoefficients : Array ℕ := #[
    94041224586610188495093760, 91566455518541499324170240, 3459727157160027460951080960, 91566455518541499324170240, 1061675930201467654326190080, 3459727157160027460951080960,
    4044139302403604147123257344, 91566455518541499324170240, 91566455518541499324170240, 101465531790816256007864320, 2638100665250457024230064128, 43579363140532452248260706304,
    70949350351470957774849966080, 36790034928225798569104244736, 1798881834029968068836327424, 36790034928225798569104244736, 36732006481966767341077266432, 2642579829859458882715254784,
    43579363140532452248260706304, 1798881834029968068836327424, 199886432127410163143585824768, 3175431985193808726836216070144, 144546799750205525136771121152, 186389294414738703465836445696,
    2495334227266705907624259354624, 4363031034565414140312538841088, 3171628482116804137373757603840, 2495334227266705907624259354624, 140742936598884327106856091648, 144546799750205525136771121152,
    144546799750205525136771121152, 140742936598884327106856091648, 4363031034565414140312538841088, 140742936598884327106856091648, 199886072053093554576129261568, 186389294414738703465836445696,
    155886053406551235557935022080, 9356106755411382703366499991552, 2318453444542980100794827669504, 76373441189204050839346943623168, 1467375597812012722022042828800, 88042535868720763321322569728,
    2318453444542980100794827669504, 2303779688564859973574607241216, 1467375597812012722022042828800, 35554510734985068254594097741824, 2274432176608619719134166384640, 9356112328354709418268090695680,
    2318453444542980100794827669504, 88042535868720763321322569728, 2274432176608619719134166384640, 88042535868720763321322569728, 2318453444542980100794827669504, 2318453444542980100794827669504,
    155886053406551235557935022080, 264910440403899879448903680, 52540969360363102471716864000, 52540969360363102471716864000, 264910440403899879448903680, 1104469009921680362082140160,
    355773058695985164013031915520, 3783796091890646221659681325056, 355774130995994796712412577792, 1104469009921680362082140160
  ]
def negativeScales : Array ℕ := #[
    22, 23, 27, 23, 26, 27,
    30, 23, 23, 23, 30, 34,
    34, 32, 29, 32, 33, 30,
    34, 29, 48, 52, 34, 36,
    35, 40, 50, 35, 35, 34,
    34, 35, 40, 35, 46, 36,
    42, 50, 36, 55, 35, 32,
    36, 37, 35, 41, 37, 52,
    36, 32, 37, 32, 36, 36,
    42, 25, 33, 33, 25, 25,
    35, 38, 34, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22281495697792675, 23243021549978039, 27482716829724676, 23243021549978039, 26778402022261855, 27482716829724676,
    30707891254495857, 23243021549978039, 23243021549978039, 23391120188967178, 30091558178286962, 34137631770218069,
    34840776132589962, 32893301706714675, 29539158983091627, 32893301706714675, 33891024365847258, 30094005616689826,
    34137631770218069, 29539158983091627, 48335095300020066, 52324795715829567, 34867451422205004, 36234233750468676,
    35977075927320993, 40783173582825911, 50323066633300008, 35977075927320993, 35828977273135642, 34867451422205004,
    34867451422205004, 35828977273135642, 40783173582825911, 35828977273135642, 46335092701154834, 36234233750468676,
    42976406628709934, 50883751173154205, 36871005606313091, 55912841976277622, 35211081045337954, 32152187356284386,
    36871005606313091, 37861845606622741, 35211081045337954, 41809803545802504, 37843349262362253, 52883752032491961,
    36871005606313091, 32152187356284386, 37843349262362253, 32152187356284386, 36871005606313091, 36871005606313091,
    42976406628709934, 25775635170444446, 33407429474723254, 33407429474723254, 25775635170444446, 25835411502231667,
    35166872016814904, 38577677190812660, 34166876365091248, 25835411502231667
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
noncomputable def negativeCeiling : ℝ := 20818038697 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 94041224586610188495093760, coefficient := (-94041224586610188495093760) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 3459727157160027460951080960, coefficient := (-3459727157160027460951080960) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 1061675930201467654326190080, coefficient := (-1061675930201467654326190080) }, { argument := 3459727157160027460951080960, coefficient := (-3459727157160027460951080960) }, { argument := 4044139302403604147123257344, coefficient := (-4044139302403604147123257344) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 91566455518541499324170240, coefficient := (-91566455518541499324170240) }, { argument := 101465531790816256007864320, coefficient := (-101465531790816256007864320) }, { argument := 2638100665250457024230064128, coefficient := (-2638100665250457024230064128) }, { argument := 43579363140532452248260706304, coefficient := (-43579363140532452248260706304) }, { argument := 70949350351470957774849966080, coefficient := (-70949350351470957774849966080) }, { argument := 36790034928225798569104244736, coefficient := (-36790034928225798569104244736) }, { argument := 1798881834029968068836327424, coefficient := (-1798881834029968068836327424) }, { argument := 36790034928225798569104244736, coefficient := (-36790034928225798569104244736) }, { argument := 36732006481966767341077266432, coefficient := (-36732006481966767341077266432) }, { argument := 2642579829859458882715254784, coefficient := (-2642579829859458882715254784) }, { argument := 43579363140532452248260706304, coefficient := (-43579363140532452248260706304) }, { argument := 1798881834029968068836327424, coefficient := (-1798881834029968068836327424) }, { argument := 199886432127410163143585824768, coefficient := (-199886432127410163143585824768) }, { argument := 3175431985193808726836216070144, coefficient := (-3175431985193808726836216070144) }, { argument := 144546799750205525136771121152, coefficient := (-144546799750205525136771121152) }, { argument := 186389294414738703465836445696, coefficient := (-186389294414738703465836445696) }, { argument := 2495334227266705907624259354624, coefficient := (-2495334227266705907624259354624) }, { argument := 4363031034565414140312538841088, coefficient := (-4363031034565414140312538841088) }, { argument := 3171628482116804137373757603840, coefficient := (-3171628482116804137373757603840) }, { argument := 2495334227266705907624259354624, coefficient := (-2495334227266705907624259354624) }, { argument := 140742936598884327106856091648, coefficient := (-140742936598884327106856091648) }, { argument := 144546799750205525136771121152, coefficient := (-144546799750205525136771121152) }, { argument := 144546799750205525136771121152, coefficient := (-144546799750205525136771121152) }, { argument := 140742936598884327106856091648, coefficient := (-140742936598884327106856091648) }, { argument := 4363031034565414140312538841088, coefficient := (-4363031034565414140312538841088) }, { argument := 140742936598884327106856091648, coefficient := (-140742936598884327106856091648) }, { argument := 199886072053093554576129261568, coefficient := (-199886072053093554576129261568) }, { argument := 186389294414738703465836445696, coefficient := (-186389294414738703465836445696) }, { argument := 155886053406551235557935022080, coefficient := (-155886053406551235557935022080) }, { argument := 9356106755411382703366499991552, coefficient := (-9356106755411382703366499991552) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 76373441189204050839346943623168, coefficient := (-76373441189204050839346943623168) }, { argument := 1467375597812012722022042828800, coefficient := (-1467375597812012722022042828800) }, { argument := 88042535868720763321322569728, coefficient := (-88042535868720763321322569728) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 2303779688564859973574607241216, coefficient := (-2303779688564859973574607241216) }, { argument := 1467375597812012722022042828800, coefficient := (-1467375597812012722022042828800) }, { argument := 35554510734985068254594097741824, coefficient := (-35554510734985068254594097741824) }, { argument := 2274432176608619719134166384640, coefficient := (-2274432176608619719134166384640) }, { argument := 9356112328354709418268090695680, coefficient := (-9356112328354709418268090695680) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 88042535868720763321322569728, coefficient := (-88042535868720763321322569728) }, { argument := 2274432176608619719134166384640, coefficient := (-2274432176608619719134166384640) }, { argument := 88042535868720763321322569728, coefficient := (-88042535868720763321322569728) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 2318453444542980100794827669504, coefficient := (-2318453444542980100794827669504) }, { argument := 155886053406551235557935022080, coefficient := (-155886053406551235557935022080) }, { argument := 264910440403899879448903680, coefficient := (-264910440403899879448903680) }, { argument := 52540969360363102471716864000, coefficient := (-52540969360363102471716864000) }, { argument := 52540969360363102471716864000, coefficient := (-52540969360363102471716864000) }, { argument := 264910440403899879448903680, coefficient := (-264910440403899879448903680) }, { argument := 1104469009921680362082140160, coefficient := (-1104469009921680362082140160) }, { argument := 355773058695985164013031915520, coefficient := (-355773058695985164013031915520) }, { argument := 3783796091890646221659681325056, coefficient := (-3783796091890646221659681325056) }, { argument := 355774130995994796712412577792, coefficient := (-355774130995994796712412577792) }, { argument := 1104469009921680362082140160, coefficient := (-1104469009921680362082140160) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
