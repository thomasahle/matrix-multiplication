import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-423680298132898719792343438852096)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    891, 514371093, 181335, 9640628175, 2046495, 181335,
    19281249285, 181335, 181335, 7517631, 46629, 2046495,
    7517631, 64296681, 181335, 46629, 181335, 16496670231,
    118839506923, 32993352679, 39105, 586575, 1029765, 39105,
    325875, 39105, 1029765, 2046495, 325875, 31583805,
    2020425, 586575, 1029765, 39105, 2020425, 39105,
    1029765, 1029765, 39105, 309382131, 28875, 5784744393,
    325875, 28875, 11569484547, 28875, 28875, 1197075,
    7425, 325875, 1197075, 38672943, 28875, 7425,
    28875, 143649, 2154735, 3782757, 143649, 1197075,
    143649, 3782757, 7517631, 1197075
  ]
def negativeCoefficients : Array ℕ := #[
    67322056579789662166450176, 37953887645941018517047345152, 1712660652342334229651128320, 1422705605232148640606611046400, 19328598790720629163205591040, 1712660652342334229651128320,
    1422705083927161117574682378240, 1712660652342334229651128320, 1712660652342334229651128320, 71002017329963627634965348352, 1761593813837829493355446272, 19328598790720629163205591040,
    71002017329963627634965348352, 37954061414270192861023567872, 1712660652342334229651128320, 1761593813837829493355446272, 1712660652342334229651128320, 76077463454910007471006285824,
    274025246256801935195107229696, 76077491625394051034705297408, 738672565250469904326328320, 11080088478757048564894924800, 19451710884929040813926645760, 738672565250469904326328320,
    12311209420841165072105472000, 738672565250469904326328320, 19451710884929040813926645760, 19328598790720629163205591040, 12311209420841165072105472000, 298300604266981429697115586560,
    19082374602303805861763481600, 11080088478757048564894924800, 19451710884929040813926645760, 738672565250469904326328320, 19082374602303805861763481600, 738672565250469904326328320,
    19451710884929040813926645760, 19451710884929040813926645760, 738672565250469904326328320, 22828371966143528616050294784, 1090866657542888044363776000, 853677594795978459369600712704,
    12311209420841165072105472000, 1090866657542888044363776000, 853677282012985945550443511808, 1090866657542888044363776000, 1090866657542888044363776000, 45224214859849444353481113600,
    1122034276329827702774169600, 12311209420841165072105472000, 45224214859849444353481113600, 22828476227141033222436028416, 1090866657542888044363776000, 1122034276329827702774169600,
    1090866657542888044363776000, 2713452891590966661208866816, 40701793373864499918133002240, 71454259478562122078500159488, 2713452891590966661208866816, 45224214859849444353481113600,
    2713452891590966661208866816, 71454259478562122078500159488, 71002017329963627634965348352, 45224214859849444353481113600
  ]
def negativeScales : Array ℕ := #[
    9, 28, 17, 33, 20, 17,
    34, 17, 17, 22, 15, 20,
    22, 25, 17, 15, 17, 33,
    36, 34, 15, 19, 19, 15,
    18, 15, 19, 20, 18, 24,
    20, 19, 19, 15, 20, 15,
    19, 19, 15, 28, 14, 32,
    18, 14, 33, 14, 14, 20,
    12, 18, 20, 25, 14, 12,
    14, 17, 21, 21, 17, 20,
    17, 21, 22, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9799281622158559, 28938234334953952, 17468297885195138, 33166480008266286, 20964723724652524, 17468297885195138,
    34166479479636712, 17468297885195138, 17468297885195138, 22841846673798092, 15508939869692758, 20964723724652524,
    22841846673798092, 25938240940184274, 17468297885195138, 15508939869692758, 17468297885195138, 33941455811088605,
    36790223568701940, 34941456345299585, 15255065463144076, 19161956058752594, 19973883726115834, 15255065463144076,
    18313959152197644, 15255065463144076, 19973883726115834, 20964723724652524, 18313959152197644, 24912681657347254,
    20946227377476479, 19161956058752594, 19973883726115834, 15255065463144076, 20946227377476479, 15255065463144076,
    19973883726115834, 19973883726115834, 15255065463144076, 28204814632478783, 14817533326997925, 32429606067234632,
    18313959152197644, 14817533326997925, 33429605538638640, 14817533326997925, 14817533326997925, 20191082113199923,
    12858175312598496, 18313959152197644, 20191082113199923, 25204821221493576, 14817533326997925, 12858175312598496,
    14817533326997925, 17132188424146355, 21039079019754873, 21851006673368008, 17132188424146355, 20191082113199923,
    17132188424146355, 21851006673368008, 22841846673798092, 20191082113199923
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
noncomputable def negativeCeiling : ℝ := 2364341017 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 37953887645941018517047345152, coefficient := (-37953887645941018517047345152) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1422705605232148640606611046400, coefficient := (-1422705605232148640606611046400) }, { argument := 19328598790720629163205591040, coefficient := (-19328598790720629163205591040) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1422705083927161117574682378240, coefficient := (-1422705083927161117574682378240) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 71002017329963627634965348352, coefficient := (-71002017329963627634965348352) }, { argument := 1761593813837829493355446272, coefficient := (-1761593813837829493355446272) }, { argument := 19328598790720629163205591040, coefficient := (-19328598790720629163205591040) }, { argument := 71002017329963627634965348352, coefficient := (-71002017329963627634965348352) }, { argument := 37954061414270192861023567872, coefficient := (-37954061414270192861023567872) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1761593813837829493355446272, coefficient := (-1761593813837829493355446272) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 76077463454910007471006285824, coefficient := (-76077463454910007471006285824) }, { argument := 274025246256801935195107229696, coefficient := (-274025246256801935195107229696) }, { argument := 76077491625394051034705297408, coefficient := (-76077491625394051034705297408) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 19328598790720629163205591040, coefficient := (-19328598790720629163205591040) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 298300604266981429697115586560, coefficient := (-298300604266981429697115586560) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 22828371966143528616050294784, coefficient := (-22828371966143528616050294784) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 853677594795978459369600712704, coefficient := (-853677594795978459369600712704) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 853677282012985945550443511808, coefficient := (-853677282012985945550443511808) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }, { argument := 22828476227141033222436028416, coefficient := (-22828476227141033222436028416) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 71002017329963627634965348352, coefficient := (-71002017329963627634965348352) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }] }

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


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5181609191603675339739446376398848)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    116020509, 7421865, 2154735, 3782757, 143649, 7421865,
    143649, 3782757, 3782757, 143649, 252219950211, 2798565,
    4725872338041, 31583805, 2798565, 9451741212819, 2798565, 2798565,
    116020509, 719631, 31583805, 116020509, 31527638079, 2798565,
    719631, 2798565, 883888911643, 3183698384735, 441944619459, 16155206829,
    179025, 302717638167, 2020425, 179025, 605435054493, 179025,
    179025, 7421865, 46035, 2020425, 7421865, 2019410097,
    179025, 46035, 179025, 1592941376135, 5737414533577, 99558872763,
    104966655405, 104966648403, 7501812962391, 1274092651610769, 975826665, 25996669428353745,
    38043879, 63821121, 1939517637, 63248241, 38043879, 31013692791,
    1986489081, 2548189195558577, 1939517637, 63821121
  ]
def negativeCoefficients : Array ℕ := #[
    1095782726054152036684847382528, 70097533032766638747895726080, 40701793373864499918133002240, 71454259478562122078500159488, 2713452891590966661208866816, 70097533032766638747895726080,
    2713452891590966661208866816, 71454259478562122078500159488, 71454259478562122078500159488, 2713452891590966661208866816, 581579608978260302832831823872, 26431699112264177314934292480,
    21794239386216429883864922456064, 298300604266981429697115586560, 26431699112264177314934292480, 21794231400475652265419565170688, 26431699112264177314934292480, 26431699112264177314934292480,
    1095782726054152036684847382528, 27186890515471725238218129408, 298300604266981429697115586560, 1095782726054152036684847382528, 581582270891852842314617585664, 26431699112264177314934292480,
    27186890515471725238218129408, 26431699112264177314934292480, 1019054533916755984222485741568, 3670554331943064578712519311360, 1019054911239141404428329811968, 37251370729050978453666398208,
    1690843319191476468763852800, 1396038699466114905886024531968, 19082374602303805861763481600, 1690843319191476468763852800, 1396038187935595898910944526336, 1690843319191476468763852800,
    1690843319191476468763852800, 70097533032766638747895726080, 1739153128311232939299962880, 19082374602303805861763481600, 70097533032766638747895726080, 37251541239223980778693066752,
    1690843319191476468763852800, 1739153128311232939299962880, 1690843319191476468763852800, 1836536368124065564092803317760, 6614788596604785999567652913152, 1836537046126073542755125035008,
    242036628566162053066716610560, 242036612420649302552431558656, 8446290515506816080867753984, 1434500797757436612158586617856, 36001649499113011864173281280, 14634823843800986405322558013440,
    22457142383493544410347470848, 1177291885584250212540481536, 35777785476184903374593851392, 37335171674857711507542638592, 22457142383493544410347470848, 572101653696227893580981600256,
    36644255682425483450589904896, 1434502988948391417256056193024, 35777785476184903374593851392, 1177291885584250212540481536
  ]
def negativeScales : Array ℕ := #[
    26, 22, 21, 21, 17, 22,
    17, 21, 21, 17, 37, 21,
    42, 24, 21, 43, 21, 21,
    26, 19, 24, 26, 34, 21,
    19, 21, 39, 41, 38, 33,
    17, 38, 20, 17, 39, 17,
    17, 22, 15, 20, 22, 30,
    17, 15, 17, 40, 42, 36,
    36, 36, 42, 50, 29, 54,
    25, 25, 30, 25, 25, 34,
    30, 51, 30, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26789804613400575, 22823350329731722, 21039079019754873, 21851006673368008, 17132188424146355, 22823350329731722,
    17132188424146355, 21851006673368008, 21851006673368008, 17132188424146355, 37875891441720789, 21416255825754780,
    42103717796364094, 24912681657347254, 21416255825754780, 43103717267738592, 21416255825754780, 21416255825754780,
    26789804613400575, 19456897810252173, 24912681657347254, 26789804613400575, 34875898044980069, 21416255825754780,
    19456897810252173, 21416255825754780, 39685074104952666, 41533840803846555, 38685074639135103, 33911280175212968,
    17449801541577704, 38139181781545221, 20946227377476479, 17449801541577704, 39139181252918988, 17449801541577704,
    17449801541577704, 22823350329731722, 15490443526075200, 20946227377476479, 22823350329731722, 30911286778826108,
    17449801541577704, 15490443526075200, 17449801541577704, 40534830312031178, 42383537896472751, 36534830844636996,
    36611140145736913, 36611140049499198, 42770376432709041, 50178391617042107, 29862049667512679, 54529176321952948,
    25181161016844176, 25927530620679710, 30853050750895663, 25914522027365838, 25181161016844176, 34852186268118994,
    30887573720959331, 51178393820748033, 30853050750895663, 25927530620679710
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
noncomputable def negativeCeiling : ℝ := 22704113743 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1095782726054152036684847382528, coefficient := (-1095782726054152036684847382528) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 581579608978260302832831823872, coefficient := (-581579608978260302832831823872) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 21794239386216429883864922456064, coefficient := (-21794239386216429883864922456064) }, { argument := 298300604266981429697115586560, coefficient := (-298300604266981429697115586560) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 21794231400475652265419565170688, coefficient := (-21794231400475652265419565170688) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1095782726054152036684847382528, coefficient := (-1095782726054152036684847382528) }, { argument := 27186890515471725238218129408, coefficient := (-27186890515471725238218129408) }, { argument := 298300604266981429697115586560, coefficient := (-298300604266981429697115586560) }, { argument := 1095782726054152036684847382528, coefficient := (-1095782726054152036684847382528) }, { argument := 581582270891852842314617585664, coefficient := (-581582270891852842314617585664) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 27186890515471725238218129408, coefficient := (-27186890515471725238218129408) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1019054533916755984222485741568, coefficient := (-1019054533916755984222485741568) }, { argument := 3670554331943064578712519311360, coefficient := (-3670554331943064578712519311360) }, { argument := 1019054911239141404428329811968, coefficient := (-1019054911239141404428329811968) }, { argument := 37251370729050978453666398208, coefficient := (-37251370729050978453666398208) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1396038699466114905886024531968, coefficient := (-1396038699466114905886024531968) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1396038187935595898910944526336, coefficient := (-1396038187935595898910944526336) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 37251541239223980778693066752, coefficient := (-37251541239223980778693066752) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1836536368124065564092803317760, coefficient := (-1836536368124065564092803317760) }, { argument := 6614788596604785999567652913152, coefficient := (-6614788596604785999567652913152) }, { argument := 1836537046126073542755125035008, coefficient := (-1836537046126073542755125035008) }, { argument := 242036628566162053066716610560, coefficient := (-242036628566162053066716610560) }, { argument := 242036612420649302552431558656, coefficient := (-242036612420649302552431558656) }, { argument := 8446290515506816080867753984, coefficient := (-8446290515506816080867753984) }, { argument := 1434500797757436612158586617856, coefficient := (-1434500797757436612158586617856) }, { argument := 36001649499113011864173281280, coefficient := (-36001649499113011864173281280) }, { argument := 14634823843800986405322558013440, coefficient := (-14634823843800986405322558013440) }, { argument := 22457142383493544410347470848, coefficient := (-22457142383493544410347470848) }, { argument := 1177291885584250212540481536, coefficient := (-1177291885584250212540481536) }, { argument := 35777785476184903374593851392, coefficient := (-35777785476184903374593851392) }, { argument := 37335171674857711507542638592, coefficient := (-37335171674857711507542638592) }, { argument := 22457142383493544410347470848, coefficient := (-22457142383493544410347470848) }, { argument := 572101653696227893580981600256, coefficient := (-572101653696227893580981600256) }, { argument := 36644255682425483450589904896, coefficient := (-36644255682425483450589904896) }, { argument := 1434502988948391417256056193024, coefficient := (-1434502988948391417256056193024) }, { argument := 35777785476184903374593851392, coefficient := (-35777785476184903374593851392) }, { argument := 1177291885584250212540481536, coefficient := (-1177291885584250212540481536) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
