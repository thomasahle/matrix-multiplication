import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 14, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14

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
def constantNumerator : ℤ := (-106895159627861754575731157893120)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    94703675267, 35739, 69597, 1314819, 69597, 806949,
    1314819, 2487691389, 69597, 69597, 77121, 239661337,
    27628122561, 7669164831, 3441, 10545, 31191, 69597,
    3441, 34743, 70707, 3441, 10545, 3441,
    4166217, 826305975, 826305975, 4166217, 3441, 10545,
    31191, 69597, 3441, 34743, 70707, 3441,
    10545, 3441, 215254545, 42692475375, 42692475375, 215254545,
    440325, 283676175, 3017015415, 141838515, 440325, 4166217,
    826305975, 826305975, 4166217, 440325, 283676175, 3017015415,
    141838515, 440325, 243351519, 3813, 9261309985, 39897,
    1767, 9261309985, 1767, 3441
  ]
def negativeCoefficients : Array ℕ := #[
    436743615122511522079459770368, 337545311462556500584562688, 328662540108278697937600512, 12418114353280368100453122048, 328662540108278697937600512, 3810708910985177335546773504,
    12418114353280368100453122048, 11472451596813508210543558656, 328662540108278697937600512, 328662540108278697937600512, 364193625525389908525449216, 35367770784016461519688564736,
    127412226529961977490800902144, 35367780224137741240551604224, 16249663067554449180327936, 398378836494883270227394560, 294590665934374207720783872, 328662540108278697937600512,
    16249663067554449180327936, 328138357428680167318880256, 333904366904264004124803072, 16249663067554449180327936, 398378836494883270227394560, 16249663067554449180327936,
    38426569377268993502478336, 7621327423701021457435852800, 7621327423701021457435852800, 38426569377268993502478336, 16249663067554449180327936, 398378836494883270227394560,
    294590665934374207720783872, 328662540108278697937600512, 16249663067554449180327936, 328138357428680167318880256, 333904366904264004124803072, 16249663067554449180327936,
    398378836494883270227394560, 16249663067554449180327936, 992686375579448998814023680, 196884291778943054317092864000, 196884291778943054317092864000, 992686375579448998814023680,
    64980500674049266522521600, 20931607200135374653567795200, 222616444907766453832840642560, 20931670288000106740234321920, 64980500674049266522521600, 38426569377268993502478336,
    7621327423701021457435852800, 7621327423701021457435852800, 38426569377268993502478336, 64980500674049266522521600, 20931607200135374653567795200, 222616444907766453832840642560,
    20931670288000106740234321920, 64980500674049266522521600, 561130398867683418820313088, 18006383399181957199822848, 21355126885073230796391710720, 188408255567050235090829312,
    16688843150461326185201664, 21355126885073230796391710720, 16688843150461326185201664, 16249663067554449180327936
  ]
def negativeScales : Array ℕ := #[
    36, 15, 16, 20, 16, 19,
    20, 31, 16, 16, 16, 27,
    34, 32, 11, 13, 14, 16,
    11, 15, 16, 11, 13, 11,
    21, 29, 29, 21, 11, 13,
    14, 16, 11, 15, 16, 11,
    13, 11, 27, 35, 35, 27,
    18, 28, 31, 27, 18, 21,
    29, 29, 21, 18, 28, 31,
    27, 18, 27, 11, 33, 15,
    10, 33, 10, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36462701363866067, 15125211646966781, 16086737499152145, 20326432778898632, 16086737499152145, 19622117971033051,
    20326432778898632, 31212160376763956, 16086737499152145, 16086737499152145, 16234836138141279, 27836421947611674,
    34685418477634670, 32836422332685836, 11748612176955137, 13364271474681056, 14928842193830838, 16086737499152145,
    11748612176955137, 15084434713282725, 16109565428606407, 11748612176955137, 13364271474681056, 11748612176955137,
    21990306574595697, 29622100859005944, 29622100859005944, 21990306574595697, 11748612176955137, 13364271474681056,
    14928842193830838, 16086737499152145, 11748612176955137, 15084434713282725, 16109565428606407, 11748612176955137,
    13364271474681056, 11748612176955137, 27681468458926589, 35313262763548721, 35313262763548721, 27681468458926589,
    18748209232060080, 28079669747734747, 31490474921729688, 27079674096011091, 18748209232060080, 21990306574595697,
    29622100859005944, 29622100859005944, 21990306574595697, 18748209232060080, 28079669747734747, 31490474921729688,
    27079674096011091, 18748209232060080, 27858466541078951, 11896710819843133, 33108569126866570, 15283992648607578,
    10787086325046961, 33108569126866570, 10787086325046961, 11748612176955137
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
noncomputable def negativeCeiling : ℝ := 337984863 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 436743615122511522079459770368, coefficient := (-436743615122511522079459770368) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 12418114353280368100453122048, coefficient := (-12418114353280368100453122048) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 3810708910985177335546773504, coefficient := (-3810708910985177335546773504) }, { argument := 12418114353280368100453122048, coefficient := (-12418114353280368100453122048) }, { argument := 11472451596813508210543558656, coefficient := (-11472451596813508210543558656) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 364193625525389908525449216, coefficient := (-364193625525389908525449216) }, { argument := 35367770784016461519688564736, coefficient := (-35367770784016461519688564736) }, { argument := 127412226529961977490800902144, coefficient := (-127412226529961977490800902144) }, { argument := 35367780224137741240551604224, coefficient := (-35367780224137741240551604224) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 38426569377268993502478336, coefficient := (-38426569377268993502478336) }, { argument := 7621327423701021457435852800, coefficient := (-7621327423701021457435852800) }, { argument := 7621327423701021457435852800, coefficient := (-7621327423701021457435852800) }, { argument := 38426569377268993502478336, coefficient := (-38426569377268993502478336) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 992686375579448998814023680, coefficient := (-992686375579448998814023680) }, { argument := 196884291778943054317092864000, coefficient := (-196884291778943054317092864000) }, { argument := 196884291778943054317092864000, coefficient := (-196884291778943054317092864000) }, { argument := 992686375579448998814023680, coefficient := (-992686375579448998814023680) }, { argument := 64980500674049266522521600, coefficient := (-64980500674049266522521600) }, { argument := 20931607200135374653567795200, coefficient := (-20931607200135374653567795200) }, { argument := 222616444907766453832840642560, coefficient := (-222616444907766453832840642560) }, { argument := 20931670288000106740234321920, coefficient := (-20931670288000106740234321920) }, { argument := 64980500674049266522521600, coefficient := (-64980500674049266522521600) }, { argument := 38426569377268993502478336, coefficient := (-38426569377268993502478336) }, { argument := 7621327423701021457435852800, coefficient := (-7621327423701021457435852800) }, { argument := 7621327423701021457435852800, coefficient := (-7621327423701021457435852800) }, { argument := 38426569377268993502478336, coefficient := (-38426569377268993502478336) }, { argument := 64980500674049266522521600, coefficient := (-64980500674049266522521600) }, { argument := 20931607200135374653567795200, coefficient := (-20931607200135374653567795200) }, { argument := 222616444907766453832840642560, coefficient := (-222616444907766453832840642560) }, { argument := 20931670288000106740234321920, coefficient := (-20931670288000106740234321920) }, { argument := 64980500674049266522521600, coefficient := (-64980500674049266522521600) }, { argument := 561130398867683418820313088, coefficient := (-561130398867683418820313088) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 21355126885073230796391710720, coefficient := (-21355126885073230796391710720) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 21355126885073230796391710720, coefficient := (-21355126885073230796391710720) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }] }

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
def constantNumerator : ℤ := (-716896679744392250912108196134912)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    65007, 3441, 39897, 65007, 243351519, 3441,
    3441, 3813, 3813, 11685, 34563, 77121,
    3813, 38499, 78351, 3813, 11685, 3813,
    109710381, 21759390675, 21759390675, 109710381, 857475, 552422025,
    5875240545, 276211845, 857475, 109710381, 21759390675, 21759390675,
    109710381, 26581725, 17125082775, 182132456895, 8562567195, 26581725,
    2487580797, 38499, 94703576963, 402831, 17841, 94703576963,
    17841, 34743, 656361, 34743, 402831, 656361,
    2487580797, 34743, 34743, 38499, 857475, 552422025,
    5875240545, 276211845, 857475, 4969965753, 78351, 189110761287,
    819819, 36309, 189110761287, 36309
  ]
def negativeCoefficients : Array ℕ := #[
    613973755903814052813471744, 16249663067554449180327936, 188408255567050235090829312, 613973755903814052813471744, 561130398867683418820313088, 16249663067554449180327936,
    16249663067554449180327936, 18006383399181957199822848, 18006383399181957199822848, 441446818818654434576302080, 326438305494847095041949696, 364193625525389908525449216,
    18006383399181957199822848, 363612774447996942164164608, 370002136299319572138295296, 18006383399181957199822848, 441446818818654434576302080, 18006383399181957199822848,
    1011899660268083495565262848, 200694955490793565045810790400, 200694955490793565045810790400, 1011899660268083495565262848, 63270487498416391087718400, 20380775431710759531105484800,
    216758117410193652416186941440, 20380836859368524983912366080, 63270487498416391087718400, 1011899660268083495565262848, 200694955490793565045810790400, 200694955490793565045810790400,
    1011899660268083495565262848, 1961385112450908123719270400, 631804038383033545464270028800, 6719501639716003224901795184640, 631805942640424274501283348480, 1961385112450908123719270400,
    11471941581233358288860479488, 363612774447996942164164608, 436743161775329166593519255552, 3804631225321724102156746752, 337006961683509361030201344, 436743161775329166593519255552,
    337006961683509361030201344, 328138357428680167318880256, 12398308748251212808426881024, 328138357428680167318880256, 3804631225321724102156746752, 12398308748251212808426881024,
    11471941581233358288860479488, 328138357428680167318880256, 328138357428680167318880256, 363612774447996942164164608, 63270487498416391087718400, 20380775431710759531105484800,
    216758117410193652416186941440, 20380836859368524983912366080, 63270487498416391087718400, 11459960787586522400063225856, 370002136299319572138295296, 436059726880708618528147636224,
    3871485767619709669447041024, 342928809253027896128176128, 436059726880708618528147636224, 342928809253027896128176128
  ]
def negativeScales : Array ℕ := #[
    15, 11, 15, 15, 27, 11,
    11, 11, 11, 13, 15, 16,
    11, 15, 16, 11, 13, 11,
    26, 34, 34, 26, 19, 29,
    32, 28, 19, 26, 34, 34,
    26, 24, 33, 37, 32, 24,
    31, 15, 36, 18, 14, 36,
    14, 15, 19, 15, 18, 19,
    31, 15, 15, 15, 19, 29,
    32, 28, 19, 32, 16, 37,
    19, 15, 37, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15988307476108722, 11748612176955137, 15283992648607578, 15988307476108722, 27858466541078951, 11748612176955137,
    11748612176955137, 11896710819843133, 11896710819843133, 13512370113670596, 15076940825560167, 16234836138141279,
    11896710819843133, 15232533352271859, 16257664067595541, 11896710819843133, 13512370113670596, 11896710819843133,
    26709124801872523, 34340919106451587, 34340919106451587, 26709124801872523, 19709735084120070, 29041195599920112,
    32452000773914906, 28041199948196456, 19709735084120070, 26709124801872523, 34340919106451587, 34340919106451587,
    26709124801872523, 24663931394446331, 33995391932302008, 37406197084301740, 32995396280579884, 24663931394446331,
    31212096239356384, 15232533352271859, 36462699866323691, 18619815185163015, 14122908861097361, 36462699866323691,
    14122908861097361, 15084434713282725, 19324129993029212, 15084434713282725, 18619815185163015, 19324129993029212,
    31212096239356384, 15084434713282725, 15084434713282725, 15232533352271859, 19709735084120070, 29041195599920112,
    32452000773914906, 28041199948196456, 19709735084120070, 32210588764496701, 16257664067595541, 37460440505481570,
    19644945900495728, 15148039576421043, 37460440505481570, 15148039576421043
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
noncomputable def negativeCeiling : ℝ := 4866369071 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 188408255567050235090829312, coefficient := (-188408255567050235090829312) }, { argument := 613973755903814052813471744, coefficient := (-613973755903814052813471744) }, { argument := 561130398867683418820313088, coefficient := (-561130398867683418820313088) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 326438305494847095041949696, coefficient := (-326438305494847095041949696) }, { argument := 364193625525389908525449216, coefficient := (-364193625525389908525449216) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 363612774447996942164164608, coefficient := (-363612774447996942164164608) }, { argument := 370002136299319572138295296, coefficient := (-370002136299319572138295296) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 441446818818654434576302080, coefficient := (-441446818818654434576302080) }, { argument := 18006383399181957199822848, coefficient := (-18006383399181957199822848) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 63270487498416391087718400, coefficient := (-63270487498416391087718400) }, { argument := 20380775431710759531105484800, coefficient := (-20380775431710759531105484800) }, { argument := 216758117410193652416186941440, coefficient := (-216758117410193652416186941440) }, { argument := 20380836859368524983912366080, coefficient := (-20380836859368524983912366080) }, { argument := 63270487498416391087718400, coefficient := (-63270487498416391087718400) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 200694955490793565045810790400, coefficient := (-200694955490793565045810790400) }, { argument := 1011899660268083495565262848, coefficient := (-1011899660268083495565262848) }, { argument := 1961385112450908123719270400, coefficient := (-1961385112450908123719270400) }, { argument := 631804038383033545464270028800, coefficient := (-631804038383033545464270028800) }, { argument := 6719501639716003224901795184640, coefficient := (-6719501639716003224901795184640) }, { argument := 631805942640424274501283348480, coefficient := (-631805942640424274501283348480) }, { argument := 1961385112450908123719270400, coefficient := (-1961385112450908123719270400) }, { argument := 11471941581233358288860479488, coefficient := (-11471941581233358288860479488) }, { argument := 363612774447996942164164608, coefficient := (-363612774447996942164164608) }, { argument := 436743161775329166593519255552, coefficient := (-436743161775329166593519255552) }, { argument := 3804631225321724102156746752, coefficient := (-3804631225321724102156746752) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 436743161775329166593519255552, coefficient := (-436743161775329166593519255552) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 12398308748251212808426881024, coefficient := (-12398308748251212808426881024) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 3804631225321724102156746752, coefficient := (-3804631225321724102156746752) }, { argument := 12398308748251212808426881024, coefficient := (-12398308748251212808426881024) }, { argument := 11471941581233358288860479488, coefficient := (-11471941581233358288860479488) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 363612774447996942164164608, coefficient := (-363612774447996942164164608) }, { argument := 63270487498416391087718400, coefficient := (-63270487498416391087718400) }, { argument := 20380775431710759531105484800, coefficient := (-20380775431710759531105484800) }, { argument := 216758117410193652416186941440, coefficient := (-216758117410193652416186941440) }, { argument := 20380836859368524983912366080, coefficient := (-20380836859368524983912366080) }, { argument := 63270487498416391087718400, coefficient := (-63270487498416391087718400) }, { argument := 11459960787586522400063225856, coefficient := (-11459960787586522400063225856) }, { argument := 370002136299319572138295296, coefficient := (-370002136299319572138295296) }, { argument := 436059726880708618528147636224, coefficient := (-436059726880708618528147636224) }, { argument := 3871485767619709669447041024, coefficient := (-3871485767619709669447041024) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 436059726880708618528147636224, coefficient := (-436059726880708618528147636224) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
