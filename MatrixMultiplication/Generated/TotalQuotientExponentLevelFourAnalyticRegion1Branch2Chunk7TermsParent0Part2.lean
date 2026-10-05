import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

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
def constantNumerator : ℤ := (-687543380113183023933822276206592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    609945, 42861, 38465, 609945, 5495, 42861,
    42861, 42861, 42861, 42861, 49455, 51653,
    772065, 600495, 85785, 806379, 9522135, 669123,
    600495, 9522135, 85785, 669123, 669123, 669123,
    669123, 669123, 772065, 806379, 973254985, 129530607965,
    4840155, 4963853289335, 4966695, 158175, 4840155, 2752245,
    4966695, 77537385, 94905, 129530607965, 4840155, 158175,
    94905, 158175, 2435895, 2752245, 3892664445, 945,
    735, 105, 987, 11655, 819, 735,
    11655, 105, 819, 819, 819, 819,
    819, 945, 987, 649093609
  ]
def negativeCoefficients : Array ℕ := #[
    23043070595151405998942453760, 51815769554502621057081409536, 1453166614108647225158533120, 23043070595151405998942453760, 1660761844695596828752609280, 1619242798578206908033794048,
    1619242798578206908033794048, 1619242798578206908033794048, 51815769554502621057081409536, 1619242798578206908033794048, 1868357075282546432346685440, 1951395167517326273784315904,
    29167791028774021055297617920, 22686059689046460820787036160, 25926925358910240938042327040, 30464137296719533102199734272, 359736089354879593015337287680, 808920071197999517266920603648,
    22686059689046460820787036160, 359736089354879593015337287680, 25926925358910240938042327040, 25278752224937484914591268864, 25278752224937484914591268864, 25278752224937484914591268864,
    808920071197999517266920603648, 25278752224937484914591268864, 29167791028774021055297617920, 30464137296719533102199734272, 4488346406689257138096701440, 597354493710589748412007055360,
    22856985743893927629296762880, 5722933202987754717780597800960, 23454553998636252534637854720, 746960318427906131676364800, 22856985743893927629296762880, 12997109540645566691168747520,
    23454553998636252534637854720, 366159948093359585747754024960, 14341638113815797728186204160, 597354493710589748412007055360, 22856985743893927629296762880, 746960318427906131676364800,
    14341638113815797728186204160, 746960318427906131676364800, 23006377807579508855632035840, 12997109540645566691168747520, 4487936548858976927030968320, 1142434899535824570097336320,
    888560477416752443409039360, 1015497688476288506753187840, 1193209783959638995434995712, 14090030427608503031200481280, 31683527880460201410699460608, 888560477416752443409039360,
    14090030427608503031200481280, 1015497688476288506753187840, 990110246264381294084358144, 990110246264381294084358144, 990110246264381294084358144, 31683527880460201410699460608,
    990110246264381294084358144, 1142434899535824570097336320, 1193209783959638995434995712, 2993415921275873719050305536
  ]
def negativeScales : Array ℕ := #[
    19, 15, 15, 19, 12, 15,
    15, 15, 15, 15, 15, 15,
    19, 19, 16, 19, 23, 19,
    19, 23, 16, 19, 19, 19,
    19, 19, 19, 19, 29, 36,
    22, 42, 22, 17, 22, 21,
    22, 26, 16, 36, 22, 17,
    16, 17, 21, 21, 31, 9,
    9, 6, 9, 13, 9, 9,
    13, 6, 9, 9, 9, 9,
    9, 9, 9, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19218319632186700, 15387377889811484, 15231258687894198, 19218319632186700, 12423903765836611, 15387377889811484,
    15387377889811484, 15387377889811484, 15387377889811484, 15387377889811484, 15593828767283669, 15656564522652026,
    19558362787255829, 19195792707869411, 16388437785811811, 19621098542612115, 23182853652161913, 19351911909786693,
    19195792707869411, 23182853652161913, 16388437785811811, 19351911909786693, 19351911909786693, 19351911909786693,
    19351911909786693, 19351911909786693, 19558362787255829, 19621098542612115, 29858242590182122, 36914502095136417,
    22206621818094862, 42174597614737754, 22243854724293838, 17271162070289573, 22206621818094862, 21392177471250944,
    22243854724293838, 26208388744269050, 16534196476124184, 36914502095136417, 22206621818094862, 17271162070289573,
    16534196476124184, 17271162070289573, 21216020516097112, 21392177471250944, 31858110843024607, 9884170522387776,
    9521600439724276, 6714245517766967, 9946906284348933, 13508661384016590, 9677719641683481, 9521600439724276,
    13508661384016590, 6714245517766967, 9677719641683481, 9677719641683481, 9677719641683481, 9677719641683481,
    9677719641683481, 9884170522387776, 9946906284348933, 29273851310515232
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
noncomputable def negativeCeiling : ℝ := 2150674619 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23043070595151405998942453760, coefficient := (-23043070595151405998942453760) }, { argument := 51815769554502621057081409536, coefficient := (-51815769554502621057081409536) }, { argument := 1453166614108647225158533120, coefficient := (-1453166614108647225158533120) }, { argument := 23043070595151405998942453760, coefficient := (-23043070595151405998942453760) }, { argument := 1660761844695596828752609280, coefficient := (-1660761844695596828752609280) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 51815769554502621057081409536, coefficient := (-51815769554502621057081409536) }, { argument := 1619242798578206908033794048, coefficient := (-1619242798578206908033794048) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 1951395167517326273784315904, coefficient := (-1951395167517326273784315904) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 22686059689046460820787036160, coefficient := (-22686059689046460820787036160) }, { argument := 25926925358910240938042327040, coefficient := (-25926925358910240938042327040) }, { argument := 30464137296719533102199734272, coefficient := (-30464137296719533102199734272) }, { argument := 359736089354879593015337287680, coefficient := (-359736089354879593015337287680) }, { argument := 808920071197999517266920603648, coefficient := (-808920071197999517266920603648) }, { argument := 22686059689046460820787036160, coefficient := (-22686059689046460820787036160) }, { argument := 359736089354879593015337287680, coefficient := (-359736089354879593015337287680) }, { argument := 25926925358910240938042327040, coefficient := (-25926925358910240938042327040) }, { argument := 25278752224937484914591268864, coefficient := (-25278752224937484914591268864) }, { argument := 25278752224937484914591268864, coefficient := (-25278752224937484914591268864) }, { argument := 25278752224937484914591268864, coefficient := (-25278752224937484914591268864) }, { argument := 808920071197999517266920603648, coefficient := (-808920071197999517266920603648) }, { argument := 25278752224937484914591268864, coefficient := (-25278752224937484914591268864) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 30464137296719533102199734272, coefficient := (-30464137296719533102199734272) }, { argument := 4488346406689257138096701440, coefficient := (-4488346406689257138096701440) }, { argument := 597354493710589748412007055360, coefficient := (-597354493710589748412007055360) }, { argument := 22856985743893927629296762880, coefficient := (-22856985743893927629296762880) }, { argument := 5722933202987754717780597800960, coefficient := (-5722933202987754717780597800960) }, { argument := 23454553998636252534637854720, coefficient := (-23454553998636252534637854720) }, { argument := 746960318427906131676364800, coefficient := (-746960318427906131676364800) }, { argument := 22856985743893927629296762880, coefficient := (-22856985743893927629296762880) }, { argument := 12997109540645566691168747520, coefficient := (-12997109540645566691168747520) }, { argument := 23454553998636252534637854720, coefficient := (-23454553998636252534637854720) }, { argument := 366159948093359585747754024960, coefficient := (-366159948093359585747754024960) }, { argument := 14341638113815797728186204160, coefficient := (-14341638113815797728186204160) }, { argument := 597354493710589748412007055360, coefficient := (-597354493710589748412007055360) }, { argument := 22856985743893927629296762880, coefficient := (-22856985743893927629296762880) }, { argument := 746960318427906131676364800, coefficient := (-746960318427906131676364800) }, { argument := 14341638113815797728186204160, coefficient := (-14341638113815797728186204160) }, { argument := 746960318427906131676364800, coefficient := (-746960318427906131676364800) }, { argument := 23006377807579508855632035840, coefficient := (-23006377807579508855632035840) }, { argument := 12997109540645566691168747520, coefficient := (-12997109540645566691168747520) }, { argument := 4487936548858976927030968320, coefficient := (-4487936548858976927030968320) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 888560477416752443409039360, coefficient := (-888560477416752443409039360) }, { argument := 1015497688476288506753187840, coefficient := (-1015497688476288506753187840) }, { argument := 1193209783959638995434995712, coefficient := (-1193209783959638995434995712) }, { argument := 14090030427608503031200481280, coefficient := (-14090030427608503031200481280) }, { argument := 31683527880460201410699460608, coefficient := (-31683527880460201410699460608) }, { argument := 888560477416752443409039360, coefficient := (-888560477416752443409039360) }, { argument := 14090030427608503031200481280, coefficient := (-14090030427608503031200481280) }, { argument := 1015497688476288506753187840, coefficient := (-1015497688476288506753187840) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 31683527880460201410699460608, coefficient := (-31683527880460201410699460608) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1193209783959638995434995712, coefficient := (-1193209783959638995434995712) }, { argument := 2993415921275873719050305536, coefficient := (-2993415921275873719050305536) }] }

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
def constantNumerator : ℤ := (-3449325423517585467754151130693632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    45505559165, 340119, 1352570672855, 349011, 11115, 340119,
    193401, 349011, 5448573, 6669, 45505559165, 340119,
    11115, 6669, 11115, 171171, 193401, 2596277661,
    6692510601, 122721935019, 122715762693, 6704875287, 17149873923879, 3379753917,
    95531579364569, 9154046763, 636687297, 18301801689, 1698286581, 17186053101351,
    3379753917, 619021683, 57512983462343, 3656712159145529, 3390910215, 3109545939,
    130454758639, 45577418575, 1828356329854991, 130454758639, 3390910215, 3381735175,
    1474874115, 3381735175, 45577418575, 1474874115, 28756241448945, 3109545939,
    14331215316891, 3676360040456967, 305235, 38779488336106845, 313215, 9975,
    305235, 173565, 313215, 4889745, 5985, 229772566905747,
    305235, 9975, 5985, 9975
  ]
def negativeCoefficients : Array ℕ := #[
    209857350961950780521877340160, 51397330105188507533986234368, 1559407815235081996568342036480, 52741051153690167861672148992, 1679651310627075409607393280, 51397330105188507533986234368,
    29225932804911112127168643072, 52741051153690167861672148992, 823365072469392365789544185856, 32249305164039847864461950976, 209857350961950780521877340160, 51397330105188507533986234368,
    1679651310627075409607393280, 32249305164039847864461950976, 1679651310627075409607393280, 51733260367313922615907713024, 29225932804911112127168643072, 2993304347297265391434203136,
    15431878783404387448129585152, 565955031881476734924594610176, 565926567051961359079122665472, 15460389808178609880746164224, 9654520726629056310304309248, 15586363884754098448622419968,
    107558996307096978361004589056, 21107794734478794296578277376, 734050476421306448842063872, 21100540740298013266321342464, 15663928961761103200489832448, 9674887792901740090739392512,
    15586363884754098448622419968, 713683410148622668406980608, 64753862722493358416731308032, 4117091879332241567808116228096, 15637813228258107879441039360, 14340249530543963223260921856,
    601616386452795795363548102656, 210188743998340221744499916800, 4117092442917712569237155872768, 601616386452795795363548102656, 15637813228258107879441039360, 15595500824571595858326323200,
    13603312670171934853347409920, 15595500824571595858326323200, 210188743998340221744499916800, 13603312670171934853347409920, 64753299137022356987691663360, 14340249530543963223260921856,
    32271027980458326174851923968, 4139213427070444545075113361408, 1441431533398716156802498560, 43661822305027320771180264161280, 1479116017932015925607792640, 47105605666624711006617600,
    1441431533398716156802498560, 819637538599269971515146240, 1479116017932015925607792640, 23091167897779433335443947520, 904427628799194451327057920, 4139214586786738201218722562048,
    1441431533398716156802498560, 47105605666624711006617600, 904427628799194451327057920, 47105605666624711006617600
  ]
def negativeScales : Array ℕ := #[
    35, 18, 40, 18, 13, 18,
    17, 18, 22, 12, 35, 18,
    13, 12, 13, 17, 17, 31,
    32, 36, 36, 32, 43, 31,
    46, 33, 29, 34, 30, 43,
    31, 29, 45, 51, 31, 31,
    36, 35, 50, 36, 31, 31,
    30, 31, 35, 30, 44, 31,
    43, 51, 18, 55, 18, 13,
    18, 17, 18, 22, 12, 47,
    18, 13, 12, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35405323751105105, 18375680075719645, 40298841116592240, 18412912981918629, 13440220327914385, 18375680075719645,
    17561235728877581, 18412912981918629, 22377447001893833, 12703254733826280, 35405323751105105, 18375680075719645,
    13440220327914385, 12703254733826280, 13440220327914385, 17385078773721895, 17561235728877581, 31273797535754285,
    32639900373113138, 36836602180936609, 36836529618453933, 32642563351756303, 43963263217117464, 31654271060384861,
    46441042949528796, 33091762515880689, 29246009739375422, 34091266627975299, 30661432784107865, 43966303504963373,
    31654271060384861, 29205414703932131, 45708952912504744, 51699468491702743, 31659025438998862, 31534056785025287,
    36924758621277146, 35407600164075565, 50699468689192120, 36924758621277146, 31659025438998862, 31655116540170739,
    30457944675297656, 31655116540170739, 35407600164075565, 30457944675297656, 44708940355948733, 31534056785025287,
    43704226191946094, 51707199485764648, 18219560873802360, 55106143286577237, 18256793780001336, 13284101125997071,
    18219560873802360, 17405116526958445, 18256793780001336, 22221327799976548, 12547135531832084, 47707199889975917,
    18219560873802360, 13284101125997071, 12547135531832084, 13284101125997071
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
noncomputable def negativeCeiling : ℝ := 10428238911 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 209857350961950780521877340160, coefficient := (-209857350961950780521877340160) }, { argument := 51397330105188507533986234368, coefficient := (-51397330105188507533986234368) }, { argument := 1559407815235081996568342036480, coefficient := (-1559407815235081996568342036480) }, { argument := 52741051153690167861672148992, coefficient := (-52741051153690167861672148992) }, { argument := 1679651310627075409607393280, coefficient := (-1679651310627075409607393280) }, { argument := 51397330105188507533986234368, coefficient := (-51397330105188507533986234368) }, { argument := 29225932804911112127168643072, coefficient := (-29225932804911112127168643072) }, { argument := 52741051153690167861672148992, coefficient := (-52741051153690167861672148992) }, { argument := 823365072469392365789544185856, coefficient := (-823365072469392365789544185856) }, { argument := 32249305164039847864461950976, coefficient := (-32249305164039847864461950976) }, { argument := 209857350961950780521877340160, coefficient := (-209857350961950780521877340160) }, { argument := 51397330105188507533986234368, coefficient := (-51397330105188507533986234368) }, { argument := 1679651310627075409607393280, coefficient := (-1679651310627075409607393280) }, { argument := 32249305164039847864461950976, coefficient := (-32249305164039847864461950976) }, { argument := 1679651310627075409607393280, coefficient := (-1679651310627075409607393280) }, { argument := 51733260367313922615907713024, coefficient := (-51733260367313922615907713024) }, { argument := 29225932804911112127168643072, coefficient := (-29225932804911112127168643072) }, { argument := 2993304347297265391434203136, coefficient := (-2993304347297265391434203136) }, { argument := 15431878783404387448129585152, coefficient := (-15431878783404387448129585152) }, { argument := 565955031881476734924594610176, coefficient := (-565955031881476734924594610176) }, { argument := 565926567051961359079122665472, coefficient := (-565926567051961359079122665472) }, { argument := 15460389808178609880746164224, coefficient := (-15460389808178609880746164224) }, { argument := 9654520726629056310304309248, coefficient := (-9654520726629056310304309248) }, { argument := 15586363884754098448622419968, coefficient := (-15586363884754098448622419968) }, { argument := 107558996307096978361004589056, coefficient := (-107558996307096978361004589056) }, { argument := 21107794734478794296578277376, coefficient := (-21107794734478794296578277376) }, { argument := 734050476421306448842063872, coefficient := (-734050476421306448842063872) }, { argument := 21100540740298013266321342464, coefficient := (-21100540740298013266321342464) }, { argument := 15663928961761103200489832448, coefficient := (-15663928961761103200489832448) }, { argument := 9674887792901740090739392512, coefficient := (-9674887792901740090739392512) }, { argument := 15586363884754098448622419968, coefficient := (-15586363884754098448622419968) }, { argument := 713683410148622668406980608, coefficient := (-713683410148622668406980608) }, { argument := 64753862722493358416731308032, coefficient := (-64753862722493358416731308032) }, { argument := 4117091879332241567808116228096, coefficient := (-4117091879332241567808116228096) }, { argument := 15637813228258107879441039360, coefficient := (-15637813228258107879441039360) }, { argument := 14340249530543963223260921856, coefficient := (-14340249530543963223260921856) }, { argument := 601616386452795795363548102656, coefficient := (-601616386452795795363548102656) }, { argument := 210188743998340221744499916800, coefficient := (-210188743998340221744499916800) }, { argument := 4117092442917712569237155872768, coefficient := (-4117092442917712569237155872768) }, { argument := 601616386452795795363548102656, coefficient := (-601616386452795795363548102656) }, { argument := 15637813228258107879441039360, coefficient := (-15637813228258107879441039360) }, { argument := 15595500824571595858326323200, coefficient := (-15595500824571595858326323200) }, { argument := 13603312670171934853347409920, coefficient := (-13603312670171934853347409920) }, { argument := 15595500824571595858326323200, coefficient := (-15595500824571595858326323200) }, { argument := 210188743998340221744499916800, coefficient := (-210188743998340221744499916800) }, { argument := 13603312670171934853347409920, coefficient := (-13603312670171934853347409920) }, { argument := 64753299137022356987691663360, coefficient := (-64753299137022356987691663360) }, { argument := 14340249530543963223260921856, coefficient := (-14340249530543963223260921856) }, { argument := 32271027980458326174851923968, coefficient := (-32271027980458326174851923968) }, { argument := 4139213427070444545075113361408, coefficient := (-4139213427070444545075113361408) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 43661822305027320771180264161280, coefficient := (-43661822305027320771180264161280) }, { argument := 1479116017932015925607792640, coefficient := (-1479116017932015925607792640) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 819637538599269971515146240, coefficient := (-819637538599269971515146240) }, { argument := 1479116017932015925607792640, coefficient := (-1479116017932015925607792640) }, { argument := 23091167897779433335443947520, coefficient := (-23091167897779433335443947520) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 4139214586786738201218722562048, coefficient := (-4139214586786738201218722562048) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 904427628799194451327057920, coefficient := (-904427628799194451327057920) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
