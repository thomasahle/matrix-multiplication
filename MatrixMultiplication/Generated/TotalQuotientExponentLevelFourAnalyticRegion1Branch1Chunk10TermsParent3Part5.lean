import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
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

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-432772669367685005988668674932736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3465, 19285684485, 3465, 3465, 143649, 891,
    39105, 143649, 64869561, 3465, 891, 3465,
    50898120085, 183332526893, 25449069471, 8581546263, 8581545705, 3465,
    51975, 91245, 3465, 28875, 3465, 91245,
    181335, 28875, 2798565, 179025, 51975, 91245,
    3465, 179025, 3465, 91245, 91245, 3465,
    15772727145, 91245, 295019176203, 1029765, 91245, 590038136217,
    91245, 91245, 3782757, 23463, 1029765, 3782757,
    1971599901, 91245, 23463, 91245, 50752431913, 182801819751,
    3172028167, 514502037, 91245, 9640691535, 1029765, 91245,
    19281376005, 91245, 91245, 3782757
  ]
def negativeCoefficients : Array ℕ := #[
    65451999452573282661826560, 44469760747638249499624734720, 65451999452573282661826560, 65451999452573282661826560, 2713452891590966661208866816, 67322056579789662166450176,
    738672565250469904326328320, 2713452891590966661208866816, 1196632189940890254836760576, 65451999452573282661826560, 67322056579789662166450176, 65451999452573282661826560,
    58681537190058178097667112960, 211368012748852796619455725568, 58681558930698990468980539392, 9893849229391224951105650688, 9893848586061025380485038080, 65451999452573282661826560,
    981779991788599239927398400, 1723569318917763110094766080, 65451999452573282661826560, 1090866657542888044363776000, 65451999452573282661826560, 1723569318917763110094766080,
    1712660652342334229651128320, 1090866657542888044363776000, 26431699112264177314934292480, 1690843319191476468763852800, 981779991788599239927398400, 1723569318917763110094766080,
    65451999452573282661826560, 1690843319191476468763852800, 65451999452573282661826560, 1723569318917763110094766080, 1723569318917763110094766080, 65451999452573282661826560,
    36369432623533315702432727040, 1723569318917763110094766080, 1360535810063341057011206848512, 19451710884929040813926645760, 1723569318917763110094766080, 1360535311565446738111925059584,
    1723569318917763110094766080, 1723569318917763110094766080, 71454259478562122078500159488, 1772814156601127770383187968, 19451710884929040813926645760, 71454259478562122078500159488,
    36369598789498088668859990016, 1723569318917763110094766080, 1772814156601127770383187968, 1723569318917763110094766080, 58513570163592516983049945088, 210756149072192557027191422976,
    58513591791247021902892367872, 37963549607764969811154567168, 1723569318917763110094766080, 1422714955517784722504134164480, 19451710884929040813926645760, 1723569318917763110094766080,
    1422714434212797199472205496320, 1723569318917763110094766080, 1723569318917763110094766080, 71454259478562122078500159488
  ]
def negativeScales : Array ℕ := #[
    11, 34, 11, 11, 17, 9,
    15, 17, 25, 11, 9, 11,
    35, 37, 34, 32, 32, 11,
    15, 16, 11, 14, 11, 16,
    17, 14, 21, 17, 15, 16,
    11, 17, 11, 16, 16, 11,
    33, 16, 38, 19, 16, 39,
    16, 16, 21, 14, 19, 21,
    30, 16, 14, 16, 35, 37,
    31, 28, 16, 33, 19, 16,
    34, 16, 16, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11758639637295877, 34166811299693329, 11758639637295877, 11758639637295877, 17132188424146355, 9799281622158559,
    15255065463144076, 17132188424146355, 25951038350336198, 11758639637295877, 9799281622158559, 11758639637295877,
    35566893320419752, 37415671815586075, 34566893854916808, 32998590499799513, 32998590405990760, 11758639637295877,
    15665530232664571, 16477457884480649, 11758639637295877, 14817533326997925, 11758639637295877, 16477457884480649,
    17468297885195138, 14817533326997925, 21416255825754780, 17449801541577704, 15665530232664571, 16477457884480649,
    11758639637295877, 17449801541577704, 11758639637295877, 16477457884480649, 16477457884480649, 11758639637295877,
    33876713079103881, 16477457884480649, 38102017776248441, 19973883726115834, 16477457884480649, 39102017247647454,
    16477457884480649, 16477457884480649, 21851006673368008, 14518099868978360, 19973883726115834, 21851006673368008,
    30876719670525882, 16477457884480649, 14518099868978360, 16477457884480649, 35562757902695844, 37411489475933106,
    31562758435941449, 28938601556689324, 16477457884480649, 33166489489895050, 19973883726115834, 16477457884480649,
    34166488961268951, 16477457884480649, 16477457884480649, 21851006673368008
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
noncomputable def negativeCeiling : ℝ := 571729699 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 44469760747638249499624734720, coefficient := (-44469760747638249499624734720) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 1196632189940890254836760576, coefficient := (-1196632189940890254836760576) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 58681537190058178097667112960, coefficient := (-58681537190058178097667112960) }, { argument := 211368012748852796619455725568, coefficient := (-211368012748852796619455725568) }, { argument := 58681558930698990468980539392, coefficient := (-58681558930698990468980539392) }, { argument := 9893849229391224951105650688, coefficient := (-9893849229391224951105650688) }, { argument := 9893848586061025380485038080, coefficient := (-9893848586061025380485038080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 36369432623533315702432727040, coefficient := (-36369432623533315702432727040) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1360535810063341057011206848512, coefficient := (-1360535810063341057011206848512) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1360535311565446738111925059584, coefficient := (-1360535311565446738111925059584) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 36369598789498088668859990016, coefficient := (-36369598789498088668859990016) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 58513570163592516983049945088, coefficient := (-58513570163592516983049945088) }, { argument := 210756149072192557027191422976, coefficient := (-210756149072192557027191422976) }, { argument := 58513591791247021902892367872, coefficient := (-58513591791247021902892367872) }, { argument := 37963549607764969811154567168, coefficient := (-37963549607764969811154567168) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1422714955517784722504134164480, coefficient := (-1422714955517784722504134164480) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1422714434212797199472205496320, coefficient := (-1422714434212797199472205496320) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }] }

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

end TermShard10


end Parent3

namespace Parent3

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 323757934432721331372190094189395968
def positiveArguments : Array ℕ := #[
    10423, 1023, 1155, 495, 13035, 1155,
    495, 1155, 1155, 47883, 297, 13035,
    47883, 1023, 1155, 297
  ]
def positiveCoefficients : Array ℕ := #[
    3303180551544708762950034377408512, 79150791261809001326362755072, 89363796585913388594280529920, 76597539930782904509383311360, 1008534275755308242706880266240, 89363796585913388594280529920,
    76597539930782904509383311360, 89363796585913388594280529920, 89363796585913388594280529920, 3704767681318866481437172826112, 91917047916939485411259973632, 1008534275755308242706880266240,
    3704767681318866481437172826112, 79150791261809001326362755072, 89363796585913388594280529920, 91917047916939485411259973632
  ]
def positiveScales : Array ℕ := #[
    13, 9, 10, 8, 13, 10,
    8, 10, 10, 15, 8, 13,
    15, 9, 10, 8
  ]
def negativeArguments : Array ℕ := #[
    23463, 1029765, 3782757, 64313049, 91245, 23463,
    91245, 1592941376135, 5737414533577, 99558872763, 86847261369, 86847255879,
    50752431913, 182801819751, 3172028167, 176135607981, 176135596371, 2049,
    1882307024049, 3465, 146890290686819, 39105, 3465, 73445144169973,
    3465, 3465, 143649, 891, 39105, 143649,
    3764630474577, 3465, 891, 3465, 232703622298291, 844514635517821,
    14543858064221, 16758097031271, 16758099693465, 16496670231, 118839506923, 32993352679,
    104966655405, 104966648403, 1021, 8581546263, 8581545705, 2049
  ]
def negativeCoefficients : Array ℕ := #[
    1772814156601127770383187968, 19451710884929040813926645760, 71454259478562122078500159488, 37963723376094144155130789888, 1723569318917763110094766080, 1772814156601127770383187968,
    1723569318917763110094766080, 1836536368124065564092803317760, 6614788596604785999567652913152, 1836537046126073542755125035008, 200256150497063153823318540288, 200256137837985033240138743808,
    58513570163592516983049945088, 210756149072192557027191422976, 58513591791247021902892367872, 203070530168296284493191315456, 203070516782877616007697924096, 39633424070246002863567273984,
    8477157212103943652905058304, 65451999452573282661826560, 330767529200750943677408346112, 738672565250469904326328320, 65451999452573282661826560, 330767523916062759534469316608,
    65451999452573282661826560, 65451999452573282661826560, 2713452891590966661208866816, 67322056579789662166450176, 738672565250469904326328320, 2713452891590966661208866816,
    8477194201246295357543940096, 65451999452573282661826560, 67322056579789662166450176, 65451999452573282661826560, 131000493333793498948060577792, 475419474728373612731697201152,
    130999427517110157765857247232, 37735879772735345426807390208, 37735885767463298620792504320, 76077463454910007471006285824, 274025246256801935195107229696, 76077491625394051034705297408,
    242036628566162053066716610560, 242036612420649302552431558656, 39498024378449164396000182272, 9893849229391224951105650688, 9893848586061025380485038080, 39633424070246002863567273984
  ]
def negativeScales : Array ℕ := #[
    14, 19, 21, 25, 16, 14,
    16, 40, 42, 36, 36, 36,
    35, 37, 31, 37, 37, 11,
    40, 11, 47, 15, 11, 46,
    11, 11, 17, 9, 15, 17,
    41, 11, 9, 11, 47, 49,
    43, 43, 43, 33, 36, 34,
    36, 36, 9, 32, 32, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13347482960639703, 9998590428318153, 10173677136303419, 8951284714309401, 13670102962420728, 10173677136303419,
    8951284714309401, 10173677136303419, 10173677136303419, 15547225923425121, 8214319120800765, 13670102962420728,
    15547225923425121, 9998590428318153, 10173677136303419, 8214319120800765
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    14518099868978360, 19973883726115834, 21851006673368008, 25938608160238583, 16477457884480649, 14518099868978360,
    16477457884480649, 40534830312031178, 42383537896472751, 36534830844636996, 36337761304756245, 36337761213557099,
    35562757902695844, 37411489475933106, 31562758435941449, 37357895640974223, 37357895545878801, 11000704269011247,
    40775639105014731, 11758639637295877, 47061732366652797, 15255065463144076, 11758639637295877, 46061732343602791,
    11758639637295877, 11758639637295877, 17132188424146355, 9799281622158559, 15255065463144076, 17132188424146355,
    41775645400042051, 11758639637295877, 9799281622158559, 11758639637295877, 47725486996671454, 49585115753710442,
    43725475258893495, 43929923573775398, 43929923802962176, 33941455811088605, 36790223568701940, 34941456345299585,
    36611140145736913, 36611140049499198, 9995767173005471, 32998590499799513, 32998590405990760, 11000704269011247
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 266265395989 / 500000000000
noncomputable def negativeCeiling : ℝ := 6884452093 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 37963723376094144155130789888, coefficient := (-37963723376094144155130789888) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1836536368124065564092803317760, coefficient := (-1836536368124065564092803317760) }, { argument := 6614788596604785999567652913152, coefficient := (-6614788596604785999567652913152) }, { argument := 1836537046126073542755125035008, coefficient := (-1836537046126073542755125035008) }, { argument := 200256150497063153823318540288, coefficient := (-200256150497063153823318540288) }, { argument := 200256137837985033240138743808, coefficient := (-200256137837985033240138743808) }, { argument := 58513570163592516983049945088, coefficient := (-58513570163592516983049945088) }, { argument := 210756149072192557027191422976, coefficient := (-210756149072192557027191422976) }, { argument := 58513591791247021902892367872, coefficient := (-58513591791247021902892367872) }, { argument := 203070530168296284493191315456, coefficient := (-203070530168296284493191315456) }, { argument := 203070516782877616007697924096, coefficient := (-203070516782877616007697924096) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 8477157212103943652905058304, coefficient := (-8477157212103943652905058304) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 330767529200750943677408346112, coefficient := (-330767529200750943677408346112) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 330767523916062759534469316608, coefficient := (-330767523916062759534469316608) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 8477194201246295357543940096, coefficient := (-8477194201246295357543940096) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 131000493333793498948060577792, coefficient := (-131000493333793498948060577792) }, { argument := 475419474728373612731697201152, coefficient := (-475419474728373612731697201152) }, { argument := 130999427517110157765857247232, coefficient := (-130999427517110157765857247232) }, { argument := 37735879772735345426807390208, coefficient := (-37735879772735345426807390208) }, { argument := 37735885767463298620792504320, coefficient := (-37735885767463298620792504320) }, { argument := 76077463454910007471006285824, coefficient := (-76077463454910007471006285824) }, { argument := 274025246256801935195107229696, coefficient := (-274025246256801935195107229696) }, { argument := 76077491625394051034705297408, coefficient := (-76077491625394051034705297408) }, { argument := 242036628566162053066716610560, coefficient := (-242036628566162053066716610560) }, { argument := 242036612420649302552431558656, coefficient := (-242036612420649302552431558656) }, { argument := 39498024378449164396000182272, coefficient := (-39498024378449164396000182272) }, { argument := 9893849229391224951105650688, coefficient := (-9893849229391224951105650688) }, { argument := 9893848586061025380485038080, coefficient := (-9893848586061025380485038080) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 3303180551544708762950034377408512, coefficient := 3303180551544708762950034377408512 }, { argument := 79150791261809001326362755072, coefficient := 79150791261809001326362755072 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 76597539930782904509383311360, coefficient := 76597539930782904509383311360 }, { argument := 1008534275755308242706880266240, coefficient := 1008534275755308242706880266240 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 76597539930782904509383311360, coefficient := 76597539930782904509383311360 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 3704767681318866481437172826112, coefficient := 3704767681318866481437172826112 }, { argument := 91917047916939485411259973632, coefficient := 91917047916939485411259973632 }, { argument := 1008534275755308242706880266240, coefficient := 1008534275755308242706880266240 }, { argument := 3704767681318866481437172826112, coefficient := 3704767681318866481437172826112 }, { argument := 79150791261809001326362755072, coefficient := 79150791261809001326362755072 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 91917047916939485411259973632, coefficient := 91917047916939485411259973632 }] }

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

end TermShard11


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
