import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9657053865706651586141282547793920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1986489081, 63821121, 1939517637, 63264609, 7501812962391, 2552005194714495,
    51975, 12513094241657983, 586575, 51975, 50052383731680787, 51975,
    51975, 2154735, 13365, 586575, 2154735, 2552022799237731,
    51975, 13365, 51975, 19127265855305037, 70166521471029379, 1195414089120675,
    15772727145, 91245, 295019176203, 1029765, 91245, 590038136217,
    91245, 91245, 3782757, 23463, 1029765, 3782757,
    1971599901, 91245, 23463, 91245, 883888911643, 3183698384735,
    441944619459, 5085711008736519, 5085712028588793, 25989215545, 46802925583, 25989225129,
    173921015181, 173921004147, 513, 3465, 51975, 91245,
    3465, 28875, 3465, 91245, 181335, 28875,
    2798565, 179025, 51975, 91245
  ]
def negativeCoefficients : Array ℕ := #[
    36644255682425483450589904896, 1177291885584250212540481536, 35777785476184903374593851392, 37344833636681662801649860608, 8446290515506816080867753984, 1436651205495471221264288317440,
    981779991788599239927398400, 56353966563982791464529657069568, 11080088478757048564894924800, 981779991788599239927398400, 56353974180750667094829813465088, 981779991788599239927398400,
    981779991788599239927398400, 40701793373864499918133002240, 1009830848696844932496752640, 11080088478757048564894924800, 40701793373864499918133002240, 1436661115961006931869089923072,
    981779991788599239927398400, 1009830848696844932496752640, 981779991788599239927398400, 10767693422321022011843536748544, 39500239993851477263671516725248, 10767332892634625652702157209600,
    36369432623533315702432727040, 1723569318917763110094766080, 1360535810063341057011206848512, 19451710884929040813926645760, 1723569318917763110094766080, 1360535311565446738111925059584,
    1723569318917763110094766080, 1723569318917763110094766080, 71454259478562122078500159488, 1772814156601127770383187968, 19451710884929040813926645760, 71454259478562122078500159488,
    36369598789498088668859990016, 1723569318917763110094766080, 1772814156601127770383187968, 1723569318917763110094766080, 1019054533916755984222485741568, 3670554331943064578712519311360,
    1019054911239141404428329811968, 1431500387741238518473203646464, 1431500674804133590932765278208, 59927050979386113084190883840, 215840397532618602759986348032, 59927073078585513388233719808,
    200517278505228794349439942656, 200517265783892912517490409472, 39691452509587505063953170432, 65451999452573282661826560, 981779991788599239927398400, 1723569318917763110094766080,
    65451999452573282661826560, 1090866657542888044363776000, 65451999452573282661826560, 1723569318917763110094766080, 1712660652342334229651128320, 1090866657542888044363776000,
    26431699112264177314934292480, 1690843319191476468763852800, 981779991788599239927398400, 1723569318917763110094766080
  ]
def negativeScales : Array ℕ := #[
    30, 25, 30, 25, 42, 51,
    15, 53, 19, 15, 55, 15,
    15, 21, 13, 19, 21, 51,
    15, 13, 15, 54, 55, 50,
    33, 16, 38, 19, 16, 39,
    16, 16, 21, 14, 19, 21,
    30, 16, 14, 16, 39, 41,
    38, 52, 52, 34, 35, 34,
    37, 37, 9, 11, 15, 16,
    11, 14, 11, 16, 17, 14,
    21, 17, 15, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30887573720959331, 25927530620679710, 30853050750895663, 25914895333870589, 42770376432709041, 51180552689082973,
    15665530232664571, 53474288101875451, 19161956058752594, 15665530232664571, 55474288296869223, 15665530232664571,
    15665530232664571, 21039079019754873, 13706172217214084, 19161956058752594, 21039079019754873, 51180562641206433,
    15665530232664571, 13706172217214084, 15665530232664571, 54086480180752459, 55961632372958463, 50086431874854607,
    33876713079103881, 16477457884480649, 38102017776248441, 19973883726115834, 16477457884480649, 39102017247647454,
    16477457884480649, 16477457884480649, 21851006673368008, 14518099868978360, 19973883726115834, 21851006673368008,
    30876719670525882, 16477457884480649, 14518099868978360, 16477457884480649, 39685074104952666, 41533840803846555,
    38685074639135103, 52175370907731652, 52175371197039414, 34597194037232327, 35445879662275664, 34597194569252492,
    37339641310307843, 37339641218779527, 9002815015607055, 11758639637295877, 15665530232664571, 16477457884480649,
    11758639637295877, 14817533326997925, 11758639637295877, 16477457884480649, 17468297885195138, 14817533326997925,
    21416255825754780, 17449801541577704, 15665530232664571, 16477457884480649
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
noncomputable def negativeCeiling : ℝ := 122126725987 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 36644255682425483450589904896, coefficient := (-36644255682425483450589904896) }, { argument := 1177291885584250212540481536, coefficient := (-1177291885584250212540481536) }, { argument := 35777785476184903374593851392, coefficient := (-35777785476184903374593851392) }, { argument := 37344833636681662801649860608, coefficient := (-37344833636681662801649860608) }, { argument := 8446290515506816080867753984, coefficient := (-8446290515506816080867753984) }, { argument := 1436651205495471221264288317440, coefficient := (-1436651205495471221264288317440) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 56353966563982791464529657069568, coefficient := (-56353966563982791464529657069568) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 56353974180750667094829813465088, coefficient := (-56353974180750667094829813465088) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 1436661115961006931869089923072, coefficient := (-1436661115961006931869089923072) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 10767693422321022011843536748544, coefficient := (-10767693422321022011843536748544) }, { argument := 39500239993851477263671516725248, coefficient := (-39500239993851477263671516725248) }, { argument := 10767332892634625652702157209600, coefficient := (-10767332892634625652702157209600) }, { argument := 36369432623533315702432727040, coefficient := (-36369432623533315702432727040) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1360535810063341057011206848512, coefficient := (-1360535810063341057011206848512) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1360535311565446738111925059584, coefficient := (-1360535311565446738111925059584) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 36369598789498088668859990016, coefficient := (-36369598789498088668859990016) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1019054533916755984222485741568, coefficient := (-1019054533916755984222485741568) }, { argument := 3670554331943064578712519311360, coefficient := (-3670554331943064578712519311360) }, { argument := 1019054911239141404428329811968, coefficient := (-1019054911239141404428329811968) }, { argument := 1431500387741238518473203646464, coefficient := (-1431500387741238518473203646464) }, { argument := 1431500674804133590932765278208, coefficient := (-1431500674804133590932765278208) }, { argument := 59927050979386113084190883840, coefficient := (-59927050979386113084190883840) }, { argument := 215840397532618602759986348032, coefficient := (-215840397532618602759986348032) }, { argument := 59927073078585513388233719808, coefficient := (-59927073078585513388233719808) }, { argument := 200517278505228794349439942656, coefficient := (-200517278505228794349439942656) }, { argument := 200517265783892912517490409472, coefficient := (-200517265783892912517490409472) }, { argument := 39691452509587505063953170432, coefficient := (-39691452509587505063953170432) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }] }

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


end Parent3

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-224081360961975646802648431067136)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3465, 179025, 3465, 91245, 91245, 3465,
    518954133, 3465, 9642845775, 39105, 3465, 19285684485,
    3465, 3465, 143649, 891, 39105, 143649,
    64869561, 3465, 891, 3465, 891, 13365,
    23463, 891, 7425, 891, 23463, 46629,
    7425, 719631, 46035, 13365, 23463, 891,
    46035, 891, 23463, 23463, 891, 16155206829,
    179025, 302717638167, 2020425, 179025, 605435054493, 179025,
    179025, 7421865, 46035, 2020425, 7421865, 2019410097,
    179025, 46035, 179025, 26062059631, 93871204737, 1628879329,
    518954133, 3465, 9642845775, 39105
  ]
def negativeCoefficients : Array ℕ := #[
    65451999452573282661826560, 1690843319191476468763852800, 65451999452573282661826560, 1723569318917763110094766080, 1723569318917763110094766080, 65451999452573282661826560,
    1196626759680603556587503616, 65451999452573282661826560, 44469777038419109594372505600, 738672565250469904326328320, 65451999452573282661826560, 44469760747638249499624734720,
    65451999452573282661826560, 65451999452573282661826560, 2713452891590966661208866816, 67322056579789662166450176, 738672565250469904326328320, 2713452891590966661208866816,
    1196632189940890254836760576, 65451999452573282661826560, 67322056579789662166450176, 65451999452573282661826560, 67322056579789662166450176, 1009830848696844932496752640,
    1772814156601127770383187968, 67322056579789662166450176, 1122034276329827702774169600, 67322056579789662166450176, 1772814156601127770383187968, 1761593813837829493355446272,
    1122034276329827702774169600, 27186890515471725238218129408, 1739153128311232939299962880, 1009830848696844932496752640, 1772814156601127770383187968, 67322056579789662166450176,
    1739153128311232939299962880, 67322056579789662166450176, 1772814156601127770383187968, 1772814156601127770383187968, 67322056579789662166450176, 37251370729050978453666398208,
    1690843319191476468763852800, 1396038699466114905886024531968, 19082374602303805861763481600, 1690843319191476468763852800, 1396038187935595898910944526336, 1690843319191476468763852800,
    1690843319191476468763852800, 70097533032766638747895726080, 1739153128311232939299962880, 19082374602303805861763481600, 70097533032766638747895726080, 37251541239223980778693066752,
    1690843319191476468763852800, 1739153128311232939299962880, 1690843319191476468763852800, 60095018005851774198808051712, 216452261209278842352250650624, 60095040218037481954321891328,
    1196626759680603556587503616, 65451999452573282661826560, 44469777038419109594372505600, 738672565250469904326328320
  ]
def negativeScales : Array ℕ := #[
    11, 17, 11, 16, 16, 11,
    28, 11, 33, 15, 11, 34,
    11, 11, 17, 9, 15, 17,
    25, 11, 9, 11, 9, 13,
    14, 9, 12, 9, 14, 15,
    12, 19, 15, 13, 14, 9,
    15, 9, 14, 14, 9, 33,
    17, 38, 20, 17, 39, 17,
    17, 22, 15, 20, 22, 30,
    17, 15, 17, 34, 36, 30,
    28, 11, 33, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11758639637295877, 17449801541577704, 11758639637295877, 16477457884480649, 16477457884480649, 11758639637295877,
    28951031803438305, 11758639637295877, 33166811828201332, 15255065463144076, 11758639637295877, 34166811299693329,
    11758639637295877, 11758639637295877, 17132188424146355, 9799281622158559, 15255065463144076, 17132188424146355,
    25951038350336198, 11758639637295877, 9799281622158559, 11758639637295877, 9799281622158559, 13706172217214084,
    14518099868978360, 9799281622158559, 12858175312598496, 9799281622158559, 14518099868978360, 15508939869692758,
    12858175312598496, 19456897810252173, 15490443526075200, 13706172217214084, 14518099868978360, 9799281622158559,
    15490443526075200, 9799281622158559, 14518099868978360, 14518099868978360, 9799281622158559, 33911280175212968,
    17449801541577704, 38139181781545221, 20946227377476479, 17449801541577704, 39139181252918988, 17449801541577704,
    17449801541577704, 22823350329731722, 15490443526075200, 20946227377476479, 22823350329731722, 30911286778826108,
    17449801541577704, 15490443526075200, 17449801541577704, 34601232050514382, 36449963623747778, 30601232583759987,
    28951031803438305, 11758639637295877, 33166811828201332, 15255065463144076
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
noncomputable def negativeCeiling : ℝ := 7940091 / 5000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1196626759680603556587503616, coefficient := (-1196626759680603556587503616) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 44469777038419109594372505600, coefficient := (-44469777038419109594372505600) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 44469760747638249499624734720, coefficient := (-44469760747638249499624734720) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 1196632189940890254836760576, coefficient := (-1196632189940890254836760576) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1761593813837829493355446272, coefficient := (-1761593813837829493355446272) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 27186890515471725238218129408, coefficient := (-27186890515471725238218129408) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 37251370729050978453666398208, coefficient := (-37251370729050978453666398208) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1396038699466114905886024531968, coefficient := (-1396038699466114905886024531968) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1396038187935595898910944526336, coefficient := (-1396038187935595898910944526336) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 37251541239223980778693066752, coefficient := (-37251541239223980778693066752) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 60095018005851774198808051712, coefficient := (-60095018005851774198808051712) }, { argument := 216452261209278842352250650624, coefficient := (-216452261209278842352250650624) }, { argument := 60095040218037481954321891328, coefficient := (-60095040218037481954321891328) }, { argument := 1196626759680603556587503616, coefficient := (-1196626759680603556587503616) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 44469777038419109594372505600, coefficient := (-44469777038419109594372505600) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
