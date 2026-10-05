import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 20, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20

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
def constantNumerator : ℤ := (-1014342310512814865163970431418368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    653751903, 26093843517, 653751903, 16378047, 938208479, 34646790945,
    277174259687, 7505735705, 1164116511, 4164549957, 291029031, 2419259991,
    89340052905, 714720248223, 19354254945, 435767613951, 1558929867237, 108941867271,
    555, 555, 17461747665, 62468249355, 4365435465, 39,
    39, 3172393, 60932335, 3801019745, 958882535, 28862685,
    3801018837, 28862685, 28862685, 2472570015, 28862685, 958882535,
    2472570015, 50758515, 28862685, 28862685, 60932335, 8442636657,
    653751903, 36727635, 33804016799, 1985740799, 2110658487, 1985740799,
    1985740799, 653751903, 36727635, 1147820555, 1121225205, 1147820555,
    1121225205, 35311534167, 126324682029, 8827880607, 555, 555,
    5, 5, 230055, 36727635
  ]
def negativeCoefficients : Array ℕ := #[
    24119188084683183276473450496, 240673226628762076788069236736, 24119188084683183276473450496, 151060820718093250357886976, 17306891699897302309419352064, 639120485537732505489238917120,
    639120329033249941128189313024, 17307048204379866670468956160, 42948318700793380109184663552, 153644774477914236025804161024, 42948304423013467057991712768, 89254939803483746358276390912,
    3296066182940413121954536488960, 3296065375816961234848387694592, 89255746926935633464425185280, 1004811706270645122137799524352, 3594647536222868480353709850624, 1004811372230085906377597779968,
    21470522556355814142781685760, 21470522556355814142781685760, 80528097563987587704721244160, 288083952146089192548382801920, 80528070793150250733734461440, 48279661532129830721065844736,
    48279661532129830721065844736, 3745300593422570597103173632, 2248006379117070183531806720, 70116438455131741087512657920, 17688260719894841707263426560, 2129690253900382279135395840,
    70116421705488122159239790592, 2129690253900382279135395840, 2129690253900382279135395840, 91221732542066374289632788480, 2129690253900382279135395840, 17688260719894841707263426560,
    91221732542066374289632788480, 3745317343066189525376040960, 2129690253900382279135395840, 2129690253900382279135395840, 2248006379117070183531806720, 38934789429749442611068796928,
    24119188084683183276473450496, 1355010566555235015532216320, 155893511638632844268505399296, 36630452315876519919887581184, 38934776936692018691274964992, 36630452315876519919887581184,
    36630452315876519919887581184, 24119188084683183276473450496, 1355010566555235015532216320, 10586776010314129222339133440, 10341477202813763560553840640, 10586776010314129222339133440,
    10341477202813763560553840640, 81422854203587449790329257984, 291284884947712405798920388608, 81422827135296364630775955456, 21470522556355814142781685760, 21470522556355814142781685760,
    1547425049106725343623905280, 1547425049106725343623905280, 8487531415754501794037760, 1355010566555235015532216320
  ]
def negativeScales : Array ℕ := #[
    29, 34, 29, 23, 29, 35,
    38, 32, 30, 31, 28, 31,
    36, 39, 34, 38, 40, 36,
    9, 9, 34, 35, 32, 5,
    5, 21, 25, 31, 29, 24,
    31, 24, 24, 31, 24, 29,
    31, 25, 24, 24, 25, 32,
    29, 25, 34, 30, 30, 30,
    30, 29, 25, 30, 30, 30,
    30, 35, 36, 33, 9, 9,
    2, 2, 17, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29284167999991430, 34602990411797712, 29284167999991430, 23965260010752695, 29805333298977177, 35012002682126927,
    38012002328847266, 32805346345064666, 30116588312086379, 31955513464283695, 28116587832475388, 31171918673974148,
    36378588057843859, 39378587704564198, 34171931720061447, 38664768023796710, 40503693164525735, 36664767544185719,
    9116343961237469, 9116343961237469, 34023478907694898, 35862404050645261, 32023478428083907, 5285402218862249,
    5285402218862249, 21597140074302745, 25860704693548500, 31823739374554093, 29836778853524058, 24782702179877530,
    31823739029918346, 24782702179877530, 24782702179877530, 31203364227898104, 24782702179877530, 29836778853524058,
    31203364227898104, 25597146526274530, 24782702179877530, 24782702179877530, 25860704693548500, 32975046496450796,
    29284167999991430, 25130362663912394, 34976475651561316, 30887030175976171, 30975046033531134, 30887030175976171,
    30887030175976171, 29284167999991430, 25130362663912394, 30096249969303906, 30062428935434864, 30096249969303906,
    30062428935434864, 35039420451563919, 36878345595270461, 33039419971952928, 9116343961237469, 9116343961237469,
    2321928094887363, 2321928094887363, 17811619287473556, 25130362663912394
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
noncomputable def negativeCeiling : ℝ := 1446610389 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 240673226628762076788069236736, coefficient := (-240673226628762076788069236736) }, { argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 151060820718093250357886976, coefficient := (-151060820718093250357886976) }, { argument := 17306891699897302309419352064, coefficient := (-17306891699897302309419352064) }, { argument := 639120485537732505489238917120, coefficient := (-639120485537732505489238917120) }, { argument := 639120329033249941128189313024, coefficient := (-639120329033249941128189313024) }, { argument := 17307048204379866670468956160, coefficient := (-17307048204379866670468956160) }, { argument := 42948318700793380109184663552, coefficient := (-42948318700793380109184663552) }, { argument := 153644774477914236025804161024, coefficient := (-153644774477914236025804161024) }, { argument := 42948304423013467057991712768, coefficient := (-42948304423013467057991712768) }, { argument := 89254939803483746358276390912, coefficient := (-89254939803483746358276390912) }, { argument := 3296066182940413121954536488960, coefficient := (-3296066182940413121954536488960) }, { argument := 3296065375816961234848387694592, coefficient := (-3296065375816961234848387694592) }, { argument := 89255746926935633464425185280, coefficient := (-89255746926935633464425185280) }, { argument := 1004811706270645122137799524352, coefficient := (-1004811706270645122137799524352) }, { argument := 3594647536222868480353709850624, coefficient := (-3594647536222868480353709850624) }, { argument := 1004811372230085906377597779968, coefficient := (-1004811372230085906377597779968) }, { argument := 21470522556355814142781685760, coefficient := (-21470522556355814142781685760) }, { argument := 21470522556355814142781685760, coefficient := (-21470522556355814142781685760) }, { argument := 80528097563987587704721244160, coefficient := (-80528097563987587704721244160) }, { argument := 288083952146089192548382801920, coefficient := (-288083952146089192548382801920) }, { argument := 80528070793150250733734461440, coefficient := (-80528070793150250733734461440) }, { argument := 48279661532129830721065844736, coefficient := (-48279661532129830721065844736) }, { argument := 48279661532129830721065844736, coefficient := (-48279661532129830721065844736) }, { argument := 3745300593422570597103173632, coefficient := (-3745300593422570597103173632) }, { argument := 2248006379117070183531806720, coefficient := (-2248006379117070183531806720) }, { argument := 70116438455131741087512657920, coefficient := (-70116438455131741087512657920) }, { argument := 17688260719894841707263426560, coefficient := (-17688260719894841707263426560) }, { argument := 2129690253900382279135395840, coefficient := (-2129690253900382279135395840) }, { argument := 70116421705488122159239790592, coefficient := (-70116421705488122159239790592) }, { argument := 2129690253900382279135395840, coefficient := (-2129690253900382279135395840) }, { argument := 2129690253900382279135395840, coefficient := (-2129690253900382279135395840) }, { argument := 91221732542066374289632788480, coefficient := (-91221732542066374289632788480) }, { argument := 2129690253900382279135395840, coefficient := (-2129690253900382279135395840) }, { argument := 17688260719894841707263426560, coefficient := (-17688260719894841707263426560) }, { argument := 91221732542066374289632788480, coefficient := (-91221732542066374289632788480) }, { argument := 3745317343066189525376040960, coefficient := (-3745317343066189525376040960) }, { argument := 2129690253900382279135395840, coefficient := (-2129690253900382279135395840) }, { argument := 2129690253900382279135395840, coefficient := (-2129690253900382279135395840) }, { argument := 2248006379117070183531806720, coefficient := (-2248006379117070183531806720) }, { argument := 38934789429749442611068796928, coefficient := (-38934789429749442611068796928) }, { argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }, { argument := 155893511638632844268505399296, coefficient := (-155893511638632844268505399296) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 38934776936692018691274964992, coefficient := (-38934776936692018691274964992) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }, { argument := 10586776010314129222339133440, coefficient := (-10586776010314129222339133440) }, { argument := 10341477202813763560553840640, coefficient := (-10341477202813763560553840640) }, { argument := 10586776010314129222339133440, coefficient := (-10586776010314129222339133440) }, { argument := 10341477202813763560553840640, coefficient := (-10341477202813763560553840640) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 21470522556355814142781685760, coefficient := (-21470522556355814142781685760) }, { argument := 21470522556355814142781685760, coefficient := (-21470522556355814142781685760) }, { argument := 1547425049106725343623905280, coefficient := (-1547425049106725343623905280) }, { argument := 1547425049106725343623905280, coefficient := (-1547425049106725343623905280) }, { argument := 8487531415754501794037760, coefficient := (-8487531415754501794037760) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }] }

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
def constantNumerator : ℤ := 5904398486374405967080402613960704
def positiveArguments : Array ℕ := #[
    391, 315, 245, 35, 329, 3885,
    273, 245
  ]
def positiveCoefficients : Array ℕ := #[
    61956423086154711998151369162752, 6092986130857731040519127040, 4738989212889346364848209920, 5415987671873538702683668480, 6363785514451407975653310464, 75146828947245349499735900160,
    168978815362454407523730456576, 4738989212889346364848209920
  ]
def positiveScales : Array ℕ := #[
    8, 8, 7, 5, 8, 11,
    8, 7
  ]
def negativeArguments : Array ℕ := #[
    1465946265, 36727635, 920115, 28240389, 1042879995, 8343037917,
    225925155, 2716271859, 9717283233, 679067739, 28240389, 1042879995,
    8343037917, 225925155, 17461747665, 62468249355, 4365435465, 39,
    39, 2716271859, 9717283233, 679067739, 39, 39,
    59618599, 2201635545, 17613080047, 476953105, 35311534167, 126324682029,
    8827880607, 39, 39, 35311534167, 126324682029, 8827880607,
    39, 39, 39, 39, 1167796971, 16378047,
    920115, 4222823907, 49747551, 145974573, 49747551, 49747551,
    16378047, 920115, 200648181, 13334027, 200648181, 13334027,
    47, 47
  ]
def negativeCoefficients : Array ℕ := #[
    13520967788132700943149957120, 1355010566555235015532216320, 8486562961690632042577920, 2083772913700009642605674496, 76950961469425987282985287680, 76950942626076915988678311936,
    2083791757049080936912650240, 3131648238599517299628048384, 11203264805681246376881553408, 3131647197511398639645229056, 2083772913700009642605674496, 76950961469425987282985287680,
    76950942626076915988678311936, 2083791757049080936912650240, 80528097563987587704721244160, 288083952146089192548382801920, 80528070793150250733734461440, 1508739422879057210033307648,
    1508739422879057210033307648, 3131648238599517299628048384, 11203264805681246376881553408, 3131647197511398639645229056, 1508739422879057210033307648, 1508739422879057210033307648,
    2199538075572232400528211968, 81226014884394097687595581440, 81225994994192300210271551488, 2199557965774029877852241920, 81422854203587449790329257984, 291284884947712405798920388608,
    81422827135296364630775955456, 1508739422879057210033307648, 1508739422879057210033307648, 81422854203587449790329257984, 291284884947712405798920388608, 81422827135296364630775955456,
    48279661532129830721065844736, 48279661532129830721065844736, 1508739422879057210033307648, 1508739422879057210033307648, 2692756481761276888866619392, 151060820718093250357886976,
    8486562961690632042577920, 9737168985096408092286910464, 229420085397703419551023104, 2692755589400032323167059968, 229420085397703419551023104, 229420085397703419551023104,
    151060820718093250357886976, 8486562961690632042577920, 1850652821881175727038005248, 122984691770466575702818816, 1850652821881175727038005248, 122984691770466575702818816,
    1818224432700402278758088704, 1818224432700402278758088704
  ]
def negativeScales : Array ℕ := #[
    30, 25, 19, 24, 29, 32,
    27, 31, 33, 29, 24, 29,
    32, 27, 34, 35, 32, 5,
    5, 31, 33, 29, 5, 5,
    25, 31, 34, 28, 35, 36,
    33, 5, 5, 35, 36, 33,
    5, 5, 5, 5, 30, 23,
    19, 31, 25, 27, 25, 25,
    23, 19, 27, 23, 27, 23,
    5, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8611024797306875, 8299208018387278, 7936637938489789, 5129283016944966, 8361943773735241, 11923698882884927,
    8092757140919852, 7936637938489789
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30449185075712581, 25130362663912394, 19811454662030972, 24751256625732562, 29957926021280624, 32957925668000893,
    27751269671819927, 31338980733422828, 33177905874182432, 29338980253811836, 24751256625732562, 29957926021280624,
    32957925668000893, 27751269671819927, 34023478907694898, 35862404050645261, 32023478428083907, 5285402218862249,
    5285402218862249, 31338980733422828, 33177905874182432, 29338980253811836, 5285402218862249, 5285402218862249,
    25829259138662317, 31035928521372408, 34035928168092747, 28829272184749913, 35039420451563919, 36878345595270461,
    33039419971952928, 5285402218862249, 5285402218862249, 35039420451563919, 36878345595270461, 33039419971952928,
    5285402218862249, 5285402218862249, 5285402218862249, 5285402218862249, 30121142328211015, 23965260010752695,
    19811454662030972, 31975560957520664, 25568122169827494, 27121141850111579, 25568122169827494, 25568122169827494,
    23965260010752695, 19811454662030972, 27580092836355472, 23668609217781520, 27580092836355472, 23668609217781520,
    5554588851679165, 5554588851679165
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 56
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
noncomputable def positiveFloor : ℝ := 6451607867 / 1000000000000
noncomputable def negativeCeiling : ℝ := 797940297 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13520967788132700943149957120, coefficient := (-13520967788132700943149957120) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }, { argument := 8486562961690632042577920, coefficient := (-8486562961690632042577920) }, { argument := 2083772913700009642605674496, coefficient := (-2083772913700009642605674496) }, { argument := 76950961469425987282985287680, coefficient := (-76950961469425987282985287680) }, { argument := 76950942626076915988678311936, coefficient := (-76950942626076915988678311936) }, { argument := 2083791757049080936912650240, coefficient := (-2083791757049080936912650240) }, { argument := 3131648238599517299628048384, coefficient := (-3131648238599517299628048384) }, { argument := 11203264805681246376881553408, coefficient := (-11203264805681246376881553408) }, { argument := 3131647197511398639645229056, coefficient := (-3131647197511398639645229056) }, { argument := 2083772913700009642605674496, coefficient := (-2083772913700009642605674496) }, { argument := 76950961469425987282985287680, coefficient := (-76950961469425987282985287680) }, { argument := 76950942626076915988678311936, coefficient := (-76950942626076915988678311936) }, { argument := 2083791757049080936912650240, coefficient := (-2083791757049080936912650240) }, { argument := 80528097563987587704721244160, coefficient := (-80528097563987587704721244160) }, { argument := 288083952146089192548382801920, coefficient := (-288083952146089192548382801920) }, { argument := 80528070793150250733734461440, coefficient := (-80528070793150250733734461440) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 3131648238599517299628048384, coefficient := (-3131648238599517299628048384) }, { argument := 11203264805681246376881553408, coefficient := (-11203264805681246376881553408) }, { argument := 3131647197511398639645229056, coefficient := (-3131647197511398639645229056) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 2199538075572232400528211968, coefficient := (-2199538075572232400528211968) }, { argument := 81226014884394097687595581440, coefficient := (-81226014884394097687595581440) }, { argument := 81225994994192300210271551488, coefficient := (-81225994994192300210271551488) }, { argument := 2199557965774029877852241920, coefficient := (-2199557965774029877852241920) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 48279661532129830721065844736, coefficient := (-48279661532129830721065844736) }, { argument := 48279661532129830721065844736, coefficient := (-48279661532129830721065844736) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 2692756481761276888866619392, coefficient := (-2692756481761276888866619392) }, { argument := 151060820718093250357886976, coefficient := (-151060820718093250357886976) }, { argument := 8486562961690632042577920, coefficient := (-8486562961690632042577920) }, { argument := 9737168985096408092286910464, coefficient := (-9737168985096408092286910464) }, { argument := 229420085397703419551023104, coefficient := (-229420085397703419551023104) }, { argument := 2692755589400032323167059968, coefficient := (-2692755589400032323167059968) }, { argument := 229420085397703419551023104, coefficient := (-229420085397703419551023104) }, { argument := 229420085397703419551023104, coefficient := (-229420085397703419551023104) }, { argument := 151060820718093250357886976, coefficient := (-151060820718093250357886976) }, { argument := 8486562961690632042577920, coefficient := (-8486562961690632042577920) }, { argument := 1850652821881175727038005248, coefficient := (-1850652821881175727038005248) }, { argument := 122984691770466575702818816, coefficient := (-122984691770466575702818816) }, { argument := 1850652821881175727038005248, coefficient := (-1850652821881175727038005248) }, { argument := 122984691770466575702818816, coefficient := (-122984691770466575702818816) }, { argument := 1818224432700402278758088704, coefficient := (-1818224432700402278758088704) }, { argument := 1818224432700402278758088704, coefficient := (-1818224432700402278758088704) }, { argument := 61956423086154711998151369162752, coefficient := 61956423086154711998151369162752 }, { argument := 6092986130857731040519127040, coefficient := 6092986130857731040519127040 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 6363785514451407975653310464, coefficient := 6363785514451407975653310464 }, { argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 168978815362454407523730456576, coefficient := 168978815362454407523730456576 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20
