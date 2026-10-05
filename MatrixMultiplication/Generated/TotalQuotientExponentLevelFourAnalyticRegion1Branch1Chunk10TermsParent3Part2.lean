import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3203708560758861635381124904517632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3465, 28875, 3465, 91245, 181335, 28875,
    2798565, 179025, 51975, 91245, 3465, 179025,
    3465, 91245, 91245, 3465, 309382131, 28875,
    5784744393, 325875, 28875, 11569484547, 28875, 28875,
    1197075, 7425, 325875, 1197075, 38672943, 28875,
    7425, 28875, 19127563419569897, 70167605473419063, 597716343442575, 518954133,
    3465, 9642845775, 39105, 3465, 19285684485, 3465,
    3465, 143649, 891, 39105, 143649, 64869561,
    3465, 891, 3465, 50898120085, 183332526893, 25449069471,
    133539641063361, 133539662235711, 3465, 51975, 91245, 3465,
    28875, 3465, 91245, 181335
  ]
def negativeCoefficients : Array ℕ := #[
    65451999452573282661826560, 1090866657542888044363776000, 65451999452573282661826560, 1723569318917763110094766080, 1712660652342334229651128320, 1090866657542888044363776000,
    26431699112264177314934292480, 1690843319191476468763852800, 981779991788599239927398400, 1723569318917763110094766080, 65451999452573282661826560, 1690843319191476468763852800,
    65451999452573282661826560, 1723569318917763110094766080, 1723569318917763110094766080, 65451999452573282661826560, 22828371966143528616050294784, 1090866657542888044363776000,
    853677594795978459369600712704, 12311209420841165072105472000, 1090866657542888044363776000, 853677282012985945550443511808, 1090866657542888044363776000, 1090866657542888044363776000,
    45224214859849444353481113600, 1122034276329827702774169600, 12311209420841165072105472000, 45224214859849444353481113600, 22828476227141033222436028416, 1090866657542888044363776000,
    1122034276329827702774169600, 1090866657542888044363776000, 10767860936110064795790673444864, 39500850232946258462371171270656, 10767500406404944721198501068800, 1196626759680603556587503616,
    65451999452573282661826560, 44469777038419109594372505600, 738672565250469904326328320, 65451999452573282661826560, 44469760747638249499624734720, 65451999452573282661826560,
    65451999452573282661826560, 2713452891590966661208866816, 67322056579789662166450176, 738672565250469904326328320, 2713452891590966661208866816, 1196632189940890254836760576,
    65451999452573282661826560, 67322056579789662166450176, 65451999452573282661826560, 58681537190058178097667112960, 211368012748852796619455725568, 58681558930698990468980539392,
    37588067358258899113859874816, 37588073317745622273717436416, 65451999452573282661826560, 981779991788599239927398400, 1723569318917763110094766080, 65451999452573282661826560,
    1090866657542888044363776000, 65451999452573282661826560, 1723569318917763110094766080, 1712660652342334229651128320
  ]
def negativeScales : Array ℕ := #[
    11, 14, 11, 16, 17, 14,
    21, 17, 15, 16, 11, 17,
    11, 16, 16, 11, 28, 14,
    32, 18, 14, 33, 14, 14,
    20, 12, 18, 20, 25, 14,
    12, 14, 54, 55, 49, 28,
    11, 33, 15, 11, 34, 11,
    11, 17, 9, 15, 17, 25,
    11, 9, 11, 35, 37, 34,
    46, 46, 11, 15, 16, 11,
    14, 11, 16, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11758639637295877, 14817533326997925, 11758639637295877, 16477457884480649, 17468297885195138, 14817533326997925,
    21416255825754780, 17449801541577704, 15665530232664571, 16477457884480649, 11758639637295877, 17449801541577704,
    11758639637295877, 16477457884480649, 16477457884480649, 11758639637295877, 28204814632478783, 14817533326997925,
    32429606067234632, 18313959152197644, 14817533326997925, 33429605538638640, 14817533326997925, 14817533326997925,
    20191082113199923, 12858175312598496, 18313959152197644, 20191082113199923, 25204821221493576, 14817533326997925,
    12858175312598496, 14817533326997925, 54086502624689468, 55961654660982568, 49086454319540606, 28951031803438305,
    11758639637295877, 33166811828201332, 15255065463144076, 11758639637295877, 34166811299693329, 11758639637295877,
    11758639637295877, 17132188424146355, 9799281622158559, 15255065463144076, 17132188424146355, 25951038350336198,
    11758639637295877, 9799281622158559, 11758639637295877, 35566893320419752, 37415671815586075, 34566893854916808,
    46924261402705910, 46924261631441327, 11758639637295877, 15665530232664571, 16477457884480649, 11758639637295877,
    14817533326997925, 11758639637295877, 16477457884480649, 17468297885195138
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
noncomputable def negativeCeiling : ℝ := 20468939321 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 22828371966143528616050294784, coefficient := (-22828371966143528616050294784) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 853677594795978459369600712704, coefficient := (-853677594795978459369600712704) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 853677282012985945550443511808, coefficient := (-853677282012985945550443511808) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }, { argument := 22828476227141033222436028416, coefficient := (-22828476227141033222436028416) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 10767860936110064795790673444864, coefficient := (-10767860936110064795790673444864) }, { argument := 39500850232946258462371171270656, coefficient := (-39500850232946258462371171270656) }, { argument := 10767500406404944721198501068800, coefficient := (-10767500406404944721198501068800) }, { argument := 1196626759680603556587503616, coefficient := (-1196626759680603556587503616) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 44469777038419109594372505600, coefficient := (-44469777038419109594372505600) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 44469760747638249499624734720, coefficient := (-44469760747638249499624734720) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 1196632189940890254836760576, coefficient := (-1196632189940890254836760576) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 58681537190058178097667112960, coefficient := (-58681537190058178097667112960) }, { argument := 211368012748852796619455725568, coefficient := (-211368012748852796619455725568) }, { argument := 58681558930698990468980539392, coefficient := (-58681558930698990468980539392) }, { argument := 37588067358258899113859874816, coefficient := (-37588067358258899113859874816) }, { argument := 37588073317745622273717436416, coefficient := (-37588073317745622273717436416) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-328426308147944358803106133180416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    28875, 2798565, 179025, 51975, 91245, 3465,
    179025, 3465, 91245, 91245, 3465, 143649,
    2154735, 3782757, 143649, 1197075, 143649, 3782757,
    7517631, 1197075, 116020509, 7421865, 2154735, 3782757,
    143649, 7421865, 143649, 3782757, 3782757, 143649,
    15772727145, 91245, 295019176203, 1029765, 91245, 590038136217,
    91245, 91245, 3782757, 23463, 1029765, 3782757,
    1971599901, 91245, 23463, 91245, 891, 13365,
    23463, 891, 7425, 891, 23463, 46629,
    7425, 719631, 46035, 13365, 23463, 891,
    46035, 891, 23463, 23463
  ]
def negativeCoefficients : Array ℕ := #[
    1090866657542888044363776000, 26431699112264177314934292480, 1690843319191476468763852800, 981779991788599239927398400, 1723569318917763110094766080, 65451999452573282661826560,
    1690843319191476468763852800, 65451999452573282661826560, 1723569318917763110094766080, 1723569318917763110094766080, 65451999452573282661826560, 2713452891590966661208866816,
    40701793373864499918133002240, 71454259478562122078500159488, 2713452891590966661208866816, 45224214859849444353481113600, 2713452891590966661208866816, 71454259478562122078500159488,
    71002017329963627634965348352, 45224214859849444353481113600, 1095782726054152036684847382528, 70097533032766638747895726080, 40701793373864499918133002240, 71454259478562122078500159488,
    2713452891590966661208866816, 70097533032766638747895726080, 2713452891590966661208866816, 71454259478562122078500159488, 71454259478562122078500159488, 2713452891590966661208866816,
    36369432623533315702432727040, 1723569318917763110094766080, 1360535810063341057011206848512, 19451710884929040813926645760, 1723569318917763110094766080, 1360535311565446738111925059584,
    1723569318917763110094766080, 1723569318917763110094766080, 71454259478562122078500159488, 1772814156601127770383187968, 19451710884929040813926645760, 71454259478562122078500159488,
    36369598789498088668859990016, 1723569318917763110094766080, 1772814156601127770383187968, 1723569318917763110094766080, 67322056579789662166450176, 1009830848696844932496752640,
    1772814156601127770383187968, 67322056579789662166450176, 1122034276329827702774169600, 67322056579789662166450176, 1772814156601127770383187968, 1761593813837829493355446272,
    1122034276329827702774169600, 27186890515471725238218129408, 1739153128311232939299962880, 1009830848696844932496752640, 1772814156601127770383187968, 67322056579789662166450176,
    1739153128311232939299962880, 67322056579789662166450176, 1772814156601127770383187968, 1772814156601127770383187968
  ]
def negativeScales : Array ℕ := #[
    14, 21, 17, 15, 16, 11,
    17, 11, 16, 16, 11, 17,
    21, 21, 17, 20, 17, 21,
    22, 20, 26, 22, 21, 21,
    17, 22, 17, 21, 21, 17,
    33, 16, 38, 19, 16, 39,
    16, 16, 21, 14, 19, 21,
    30, 16, 14, 16, 9, 13,
    14, 9, 12, 9, 14, 15,
    12, 19, 15, 13, 14, 9,
    15, 9, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14817533326997925, 21416255825754780, 17449801541577704, 15665530232664571, 16477457884480649, 11758639637295877,
    17449801541577704, 11758639637295877, 16477457884480649, 16477457884480649, 11758639637295877, 17132188424146355,
    21039079019754873, 21851006673368008, 17132188424146355, 20191082113199923, 17132188424146355, 21851006673368008,
    22841846673798092, 20191082113199923, 26789804613400575, 22823350329731722, 21039079019754873, 21851006673368008,
    17132188424146355, 22823350329731722, 17132188424146355, 21851006673368008, 21851006673368008, 17132188424146355,
    33876713079103881, 16477457884480649, 38102017776248441, 19973883726115834, 16477457884480649, 39102017247647454,
    16477457884480649, 16477457884480649, 21851006673368008, 14518099868978360, 19973883726115834, 21851006673368008,
    30876719670525882, 16477457884480649, 14518099868978360, 16477457884480649, 9799281622158559, 13706172217214084,
    14518099868978360, 9799281622158559, 12858175312598496, 9799281622158559, 14518099868978360, 15508939869692758,
    12858175312598496, 19456897810252173, 15490443526075200, 13706172217214084, 14518099868978360, 9799281622158559,
    15490443526075200, 9799281622158559, 14518099868978360, 14518099868978360
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
noncomputable def negativeCeiling : ℝ := 1912210719 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 71002017329963627634965348352, coefficient := (-71002017329963627634965348352) }, { argument := 45224214859849444353481113600, coefficient := (-45224214859849444353481113600) }, { argument := 1095782726054152036684847382528, coefficient := (-1095782726054152036684847382528) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 70097533032766638747895726080, coefficient := (-70097533032766638747895726080) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 36369432623533315702432727040, coefficient := (-36369432623533315702432727040) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1360535810063341057011206848512, coefficient := (-1360535810063341057011206848512) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1360535311565446738111925059584, coefficient := (-1360535311565446738111925059584) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 36369598789498088668859990016, coefficient := (-36369598789498088668859990016) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1761593813837829493355446272, coefficient := (-1761593813837829493355446272) }, { argument := 1122034276329827702774169600, coefficient := (-1122034276329827702774169600) }, { argument := 27186890515471725238218129408, coefficient := (-27186890515471725238218129408) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1739153128311232939299962880, coefficient := (-1739153128311232939299962880) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
