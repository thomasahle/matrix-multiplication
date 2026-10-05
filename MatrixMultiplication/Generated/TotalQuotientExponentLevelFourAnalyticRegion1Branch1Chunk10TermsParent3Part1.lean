import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6195228444532336967173261706133504)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    292706944659681, 39105, 586575, 1029765, 39105, 325875,
    39105, 1029765, 2046495, 325875, 31583805, 2020425,
    586575, 1029765, 39105, 2020425, 39105, 1029765,
    1029765, 39105, 638000323624089, 51975, 50052300546196455, 586575,
    51975, 6256538413902525, 51975, 51975, 2154735, 13365,
    586575, 2154735, 1276009449483519, 51975, 13365, 51975,
    3465, 51975, 91245, 3465, 28875, 3465,
    91245, 181335, 28875, 2798565, 179025, 51975,
    91245, 3465, 179025, 3465, 91245, 91245,
    3465, 7935744861, 91245, 148472656167, 1029765, 91245,
    296945203533, 91245, 91245, 3782757
  ]
def negativeCoefficients : Array ℕ := #[
    329558721724523936426905042944, 738672565250469904326328320, 11080088478757048564894924800, 19451710884929040813926645760, 738672565250469904326328320, 12311209420841165072105472000,
    738672565250469904326328320, 19451710884929040813926645760, 19328598790720629163205591040, 12311209420841165072105472000, 298300604266981429697115586560, 19082374602303805861763481600,
    11080088478757048564894924800, 19451710884929040813926645760, 738672565250469904326328320, 19082374602303805861763481600, 738672565250469904326328320, 19451710884929040813926645760,
    19451710884929040813926645760, 738672565250469904326328320, 1436649009867851538258116739072, 981779991788599239927398400, 56353880522221607037471471697920, 11080088478757048564894924800,
    981779991788599239927398400, 56353888138961211321110809804800, 981779991788599239927398400, 981779991788599239927398400, 40701793373864499918133002240, 1009830848696844932496752640,
    11080088478757048564894924800, 40701793373864499918133002240, 1436658920303801977010814713856, 981779991788599239927398400, 1009830848696844932496752640, 981779991788599239927398400,
    65451999452573282661826560, 981779991788599239927398400, 1723569318917763110094766080, 65451999452573282661826560, 1090866657542888044363776000, 65451999452573282661826560,
    1723569318917763110094766080, 1712660652342334229651128320, 1090866657542888044363776000, 26431699112264177314934292480, 1690843319191476468763852800, 981779991788599239927398400,
    1723569318917763110094766080, 65451999452573282661826560, 1690843319191476468763852800, 65451999452573282661826560, 1723569318917763110094766080, 1723569318917763110094766080,
    65451999452573282661826560, 36597163621280694860821561344, 1723569318917763110094766080, 1369418545128261580653053607936, 19451710884929040813926645760, 1723569318917763110094766080,
    1369418043372211089734822264832, 1723569318917763110094766080, 1723569318917763110094766080, 71454259478562122078500159488
  ]
def negativeScales : Array ℕ := #[
    48, 15, 19, 19, 15, 18,
    15, 19, 20, 18, 24, 20,
    19, 19, 15, 20, 15, 19,
    19, 15, 49, 15, 55, 19,
    15, 52, 15, 15, 21, 13,
    19, 21, 50, 15, 13, 15,
    11, 15, 16, 11, 14, 11,
    16, 17, 14, 21, 17, 15,
    16, 11, 17, 11, 16, 16,
    11, 32, 16, 37, 19, 16,
    38, 16, 16, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48056450303439390, 15255065463144076, 19161956058752594, 19973883726115834, 15255065463144076, 18313959152197644,
    15255065463144076, 19973883726115834, 20964723724652524, 18313959152197644, 24912681657347254, 20946227377476479,
    19161956058752594, 19973883726115834, 15255065463144076, 20946227377476479, 15255065463144076, 19973883726115834,
    19973883726115834, 15255065463144076, 49180550484216901, 15665530232664571, 55474285899153540, 19161956058752594,
    15665530232664571, 52474286094146886, 15665530232664571, 15665530232664571, 21039079019754873, 13706172217214084,
    19161956058752594, 21039079019754873, 50180560436325862, 15665530232664571, 13706172217214084, 15665530232664571,
    11758639637295877, 15665530232664571, 16477457884480649, 11758639637295877, 14817533326997925, 11758639637295877,
    16477457884480649, 17468297885195138, 14817533326997925, 21416255825754780, 17449801541577704, 15665530232664571,
    16477457884480649, 11758639637295877, 17449801541577704, 11758639637295877, 16477457884480649, 16477457884480649,
    11758639637295877, 32885718500311357, 16477457884480649, 37111406301759156, 19973883726115834, 16477457884480649,
    38111405773154442, 16477457884480649, 16477457884480649, 21851006673368008
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
noncomputable def negativeCeiling : ℝ := 76589763773 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 329558721724523936426905042944, coefficient := (-329558721724523936426905042944) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 19328598790720629163205591040, coefficient := (-19328598790720629163205591040) }, { argument := 12311209420841165072105472000, coefficient := (-12311209420841165072105472000) }, { argument := 298300604266981429697115586560, coefficient := (-298300604266981429697115586560) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 19082374602303805861763481600, coefficient := (-19082374602303805861763481600) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 1436649009867851538258116739072, coefficient := (-1436649009867851538258116739072) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 56353880522221607037471471697920, coefficient := (-56353880522221607037471471697920) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 56353888138961211321110809804800, coefficient := (-56353888138961211321110809804800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 11080088478757048564894924800, coefficient := (-11080088478757048564894924800) }, { argument := 40701793373864499918133002240, coefficient := (-40701793373864499918133002240) }, { argument := 1436658920303801977010814713856, coefficient := (-1436658920303801977010814713856) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1009830848696844932496752640, coefficient := (-1009830848696844932496752640) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 36597163621280694860821561344, coefficient := (-36597163621280694860821561344) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1369418545128261580653053607936, coefficient := (-1369418545128261580653053607936) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1369418043372211089734822264832, coefficient := (-1369418043372211089734822264832) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }] }

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
def constantNumerator : ℤ := (-97100829793782950101523701516206080)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    23463, 1029765, 3782757, 991972641, 91245, 23463,
    91245, 232704427409687, 844517521354953, 7271954199153, 118174455878633, 9688370922212375,
    12945835421, 2097998763, 224821411259, 405226766779, 2422056298236975, 224821411259,
    6611700527, 6629539907, 12945835421, 12910156661, 405226766779, 12910156661,
    29543511235537, 2097998763, 292706940229899, 12494269850359673, 291906989429, 510084878413238977,
    11373190491, 18958527725, 580027139361, 18954092525, 11373190491, 9291368969067,
    595162332229, 49977155666482501, 580027139361, 18958527725, 595162332229, 18958527725,
    580027139361, 18954219245, 292706940229899, 26030200282227981, 3465, 510746943558405265,
    39105, 3465, 510747020119714909, 3465, 3465, 143649,
    891, 39105, 143649, 26030385737754903, 3465, 891,
    3465, 3465, 51975, 91245
  ]
def negativeCoefficients : Array ℕ := #[
    1772814156601127770383187968, 19451710884929040813926645760, 71454259478562122078500159488, 36597330873297525166898675712, 1723569318917763110094766080, 1772814156601127770383187968,
    1723569318917763110094766080, 131000946571216376115541049344, 475421099310252653624306958336, 130999880886243057835601559552, 133052608864930674818775252992, 10908135918775700184495030272000,
    59702128207887737044110147584, 77402492496040440223305302016, 1036805758946244028394306011136, 1868778614647250214520373641216, 10907971842210403537879931289600, 1036805758946244028394306011136,
    60982173756789784632220450816, 61146712995436610982674169856, 59702128207887737044110147584, 59537588969240910693656428544, 1868778614647250214520373641216, 59537588969240910693656428544,
    133052146191580495083420516352, 77402492496040440223305302016, 329558716737032795293772414976, 56269189042346246141120828407808, 1346183381830950620097010466816, 574304517087296953947913241755648,
    839193337156096302139859533824, 43715388619675247238656819200, 1337451524449778868926306844672, 1398565175832345045223709081600, 839193337156096302139859533824, 21424438183348188557093092982784,
    1372350903117557627916551979008, 56269274909151966042859056922624, 1337451524449778868926306844672, 43715388619675247238656819200, 1372350903117557627916551979008, 43715388619675247238656819200,
    1337451524449778868926306844672, 1398574526117981127121232199680, 329558716737032795293772414976, 14653700036427664380540928131072, 65451999452573282661826560, 575049936172563425942362768015360,
    738672565250469904326328320, 65451999452573282661826560, 575050022372934821871253209481216, 65451999452573282661826560, 65451999452573282661826560, 2713452891590966661208866816,
    67322056579789662166450176, 738672565250469904326328320, 2713452891590966661208866816, 14653804438607906845314552692736, 65451999452573282661826560, 67322056579789662166450176,
    65451999452573282661826560, 65451999452573282661826560, 981779991788599239927398400, 1723569318917763110094766080
  ]
def negativeScales : Array ℕ := #[
    14, 19, 21, 29, 16, 14,
    16, 47, 49, 42, 46, 53,
    33, 30, 37, 38, 51, 37,
    32, 32, 33, 33, 38, 33,
    44, 30, 48, 53, 38, 58,
    33, 34, 39, 34, 33, 43,
    39, 55, 39, 34, 39, 34,
    39, 34, 48, 54, 11, 58,
    15, 11, 58, 11, 11, 17,
    9, 15, 17, 54, 11, 9,
    11, 11, 15, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14518099868978360, 19973883726115834, 21851006673368008, 29885725093530472, 16477457884480649, 14518099868978360,
    16477457884480649, 47725491988120238, 49585120683614118, 42725480251833405, 46747911550618115, 53105175523416218,
    33591769017155468, 30966366694981365, 37709988483531351, 38559938516578825, 51105153822712345, 37709988483531351,
    32622374234102290, 32626261604136234, 33591769017155468, 33587787456314108, 38559938516578825, 33587787456314108,
    44747906533822749, 30966366694981365, 48056450281605865, 53472116112776275, 38086717798944555, 58823514946454185,
    33404917975299296, 34142127881131245, 39077329449010702, 34141790334370702, 33404917975299296, 43079028314306933,
    39114492265055600, 55472118314327824, 39077329449010702, 34142127881131245, 39114492265055600, 34142127881131245,
    39077329449010702, 34141799979659930, 48056450281605865, 54531035930404086, 11758639637295877, 58825386279684447,
    15255065463144076, 11758639637295877, 58825386495945390, 11758639637295877, 11758639637295877, 17132188424146355,
    9799281622158559, 15255065463144076, 17132188424146355, 54531046209034791, 11758639637295877, 9799281622158559,
    11758639637295877, 11758639637295877, 15665530232664571, 16477457884480649
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
noncomputable def negativeCeiling : ℝ := 674189210573 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 19451710884929040813926645760, coefficient := (-19451710884929040813926645760) }, { argument := 71454259478562122078500159488, coefficient := (-71454259478562122078500159488) }, { argument := 36597330873297525166898675712, coefficient := (-36597330873297525166898675712) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1772814156601127770383187968, coefficient := (-1772814156601127770383187968) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 131000946571216376115541049344, coefficient := (-131000946571216376115541049344) }, { argument := 475421099310252653624306958336, coefficient := (-475421099310252653624306958336) }, { argument := 130999880886243057835601559552, coefficient := (-130999880886243057835601559552) }, { argument := 133052608864930674818775252992, coefficient := (-133052608864930674818775252992) }, { argument := 10908135918775700184495030272000, coefficient := (-10908135918775700184495030272000) }, { argument := 59702128207887737044110147584, coefficient := (-59702128207887737044110147584) }, { argument := 77402492496040440223305302016, coefficient := (-77402492496040440223305302016) }, { argument := 1036805758946244028394306011136, coefficient := (-1036805758946244028394306011136) }, { argument := 1868778614647250214520373641216, coefficient := (-1868778614647250214520373641216) }, { argument := 10907971842210403537879931289600, coefficient := (-10907971842210403537879931289600) }, { argument := 1036805758946244028394306011136, coefficient := (-1036805758946244028394306011136) }, { argument := 60982173756789784632220450816, coefficient := (-60982173756789784632220450816) }, { argument := 61146712995436610982674169856, coefficient := (-61146712995436610982674169856) }, { argument := 59702128207887737044110147584, coefficient := (-59702128207887737044110147584) }, { argument := 59537588969240910693656428544, coefficient := (-59537588969240910693656428544) }, { argument := 1868778614647250214520373641216, coefficient := (-1868778614647250214520373641216) }, { argument := 59537588969240910693656428544, coefficient := (-59537588969240910693656428544) }, { argument := 133052146191580495083420516352, coefficient := (-133052146191580495083420516352) }, { argument := 77402492496040440223305302016, coefficient := (-77402492496040440223305302016) }, { argument := 329558716737032795293772414976, coefficient := (-329558716737032795293772414976) }, { argument := 56269189042346246141120828407808, coefficient := (-56269189042346246141120828407808) }, { argument := 1346183381830950620097010466816, coefficient := (-1346183381830950620097010466816) }, { argument := 574304517087296953947913241755648, coefficient := (-574304517087296953947913241755648) }, { argument := 839193337156096302139859533824, coefficient := (-839193337156096302139859533824) }, { argument := 43715388619675247238656819200, coefficient := (-43715388619675247238656819200) }, { argument := 1337451524449778868926306844672, coefficient := (-1337451524449778868926306844672) }, { argument := 1398565175832345045223709081600, coefficient := (-1398565175832345045223709081600) }, { argument := 839193337156096302139859533824, coefficient := (-839193337156096302139859533824) }, { argument := 21424438183348188557093092982784, coefficient := (-21424438183348188557093092982784) }, { argument := 1372350903117557627916551979008, coefficient := (-1372350903117557627916551979008) }, { argument := 56269274909151966042859056922624, coefficient := (-56269274909151966042859056922624) }, { argument := 1337451524449778868926306844672, coefficient := (-1337451524449778868926306844672) }, { argument := 43715388619675247238656819200, coefficient := (-43715388619675247238656819200) }, { argument := 1372350903117557627916551979008, coefficient := (-1372350903117557627916551979008) }, { argument := 43715388619675247238656819200, coefficient := (-43715388619675247238656819200) }, { argument := 1337451524449778868926306844672, coefficient := (-1337451524449778868926306844672) }, { argument := 1398574526117981127121232199680, coefficient := (-1398574526117981127121232199680) }, { argument := 329558716737032795293772414976, coefficient := (-329558716737032795293772414976) }, { argument := 14653700036427664380540928131072, coefficient := (-14653700036427664380540928131072) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 575049936172563425942362768015360, coefficient := (-575049936172563425942362768015360) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 575050022372934821871253209481216, coefficient := (-575050022372934821871253209481216) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 14653804438607906845314552692736, coefficient := (-14653804438607906845314552692736) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
