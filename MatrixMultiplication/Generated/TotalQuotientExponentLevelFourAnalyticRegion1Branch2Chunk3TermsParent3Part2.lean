import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3

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
def constantNumerator : ℤ := (-242516466226807448174380992954368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    228856421984043, 254745, 2423791025232265, 261405, 8325, 254745,
    144855, 261405, 4080915, 4995, 114428277045037, 254745,
    8325, 4995, 8325, 128205, 144855, 2097362413689,
    87988005, 7398844635, 3699421425, 43994895, 108508503, 6576440301,
    73899, 65255797455, 75831, 2415, 73899, 42021,
    75831, 1183833, 1449, 6576440301, 73899, 2415,
    1449, 2415, 37191, 42021, 108508503, 255488383,
    9184841089, 73478757769, 2043882103, 465, 5565, 8325,
    2415, 465, 9645, 4845, 465, 5565,
    465, 279, 3339, 4995, 1449, 279,
    5787, 2907, 279, 3339
  ]
def negativeCoefficients : Array ℕ := #[
    257669424192170260917840248832, 2405998499357255539925975040, 2728946089514995280512402063360, 2468900420909079214172405760, 78627401939779592808038400, 2405998499357255539925975040,
    1368116793752164914859868160, 2468900420909079214172405760, 38543152430879956394500423680, 1509646117243768181914337280, 257669572930338257166638514176, 2405998499357255539925975040,
    78627401939779592808038400, 1509646117243768181914337280, 78627401939779592808038400, 2421723979745211458487582720, 1368116793752164914859868160, 2361420146187666119706279936,
    202886526223909549517045760, 17060574177872995065287147520, 17060570061943223618843443200, 202890642153680995960750080, 500407146165586275663347712, 60656955574288204908051038208,
    2791825285740671293175365632, 601878497489106045376281968640, 2864814182099904529598251008, 91236120449041545528606720, 2791825285740671293175365632, 1587508495813322892197756928,
    2864814182099904529598251008, 44723946244120165618123014144, 1751733512621597674149249024, 60656955574288204908051038208, 2791825285740671293175365632, 91236120449041545528606720,
    1751733512621597674149249024, 91236120449041545528606720, 2810072509830479602281086976, 1587508495813322892197756928, 500407146165586275663347712, 4712928815006886154026876928,
    169430412926474734334403149824, 169430479927355053056708313088, 4712871258859533171012141056, 4391800829068770048737280, 105119877908678302456872960, 78627401939779592808038400,
    91236120449041545528606720, 4391800829068770048737280, 91094449454555456172195840, 91519462438013724241428480, 4391800829068770048737280, 105119877908678302456872960,
    4391800829068770048737280, 84322575918120384935755776, 2018301655846623407171960832, 1509646117243768181914337280, 1751733512621597674149249024, 84322575918120384935755776,
    1749013429527464758506160128, 1757173678809863505435426816, 84322575918120384935755776, 2018301655846623407171960832
  ]
def negativeScales : Array ℕ := #[
    47, 17, 51, 17, 13, 17,
    17, 17, 21, 12, 46, 17,
    13, 12, 13, 16, 17, 40,
    26, 32, 31, 25, 26, 32,
    16, 35, 16, 11, 16, 15,
    16, 20, 10, 32, 16, 11,
    10, 11, 15, 15, 26, 27,
    33, 36, 30, 8, 12, 13,
    11, 8, 13, 12, 8, 12,
    8, 8, 11, 12, 10, 8,
    12, 11, 8, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47701436104747367, 17958694316714768, 51106186740991957, 17995927233034729, 13023234556845987, 17958694316714768,
    17144249957807353, 17995927233034729, 21960461243250186, 12286268962679781, 46701436937534402, 17958694316714768,
    13023234556845987, 12286268962679781, 13023234556845987, 16968093016757167, 17144249957807353, 40931713319708264,
    26390803525387317, 32784652859051247, 31784652510995421, 25390832792837202, 26693232859482636, 32614659746506441,
    16173267221528426, 35925387034987905, 16210500127727401, 11237807473723136, 16173267221528426, 15358822874684503,
    16210500127727401, 20175034147702613, 10500841879557209, 32614659746506441, 16173267221528426, 11237807473723136,
    10500841879557209, 11237807473723136, 15182665919530675, 15358822874684503, 26693232859482636, 27928682459969980,
    33096607614833513, 36096608185343948, 30928664841098771, 8861086908132560, 12442165972229357, 13023234556845987,
    11237807473723136, 8861086908132560, 13235565522936466, 12242280950302444, 8861086908132560, 12442165972229357,
    8861086908132560, 8124121311829188, 11705200378144884, 12286268962679781, 10500841879557209, 8124121311829188,
    12498599928770519, 11505315356136561, 8124121311829188, 11705200378144884
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
noncomputable def negativeCeiling : ℝ := 617491917 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 257669424192170260917840248832, coefficient := (-257669424192170260917840248832) }, { argument := 2405998499357255539925975040, coefficient := (-2405998499357255539925975040) }, { argument := 2728946089514995280512402063360, coefficient := (-2728946089514995280512402063360) }, { argument := 2468900420909079214172405760, coefficient := (-2468900420909079214172405760) }, { argument := 78627401939779592808038400, coefficient := (-78627401939779592808038400) }, { argument := 2405998499357255539925975040, coefficient := (-2405998499357255539925975040) }, { argument := 1368116793752164914859868160, coefficient := (-1368116793752164914859868160) }, { argument := 2468900420909079214172405760, coefficient := (-2468900420909079214172405760) }, { argument := 38543152430879956394500423680, coefficient := (-38543152430879956394500423680) }, { argument := 1509646117243768181914337280, coefficient := (-1509646117243768181914337280) }, { argument := 257669572930338257166638514176, coefficient := (-257669572930338257166638514176) }, { argument := 2405998499357255539925975040, coefficient := (-2405998499357255539925975040) }, { argument := 78627401939779592808038400, coefficient := (-78627401939779592808038400) }, { argument := 1509646117243768181914337280, coefficient := (-1509646117243768181914337280) }, { argument := 78627401939779592808038400, coefficient := (-78627401939779592808038400) }, { argument := 2421723979745211458487582720, coefficient := (-2421723979745211458487582720) }, { argument := 1368116793752164914859868160, coefficient := (-1368116793752164914859868160) }, { argument := 2361420146187666119706279936, coefficient := (-2361420146187666119706279936) }, { argument := 202886526223909549517045760, coefficient := (-202886526223909549517045760) }, { argument := 17060574177872995065287147520, coefficient := (-17060574177872995065287147520) }, { argument := 17060570061943223618843443200, coefficient := (-17060570061943223618843443200) }, { argument := 202890642153680995960750080, coefficient := (-202890642153680995960750080) }, { argument := 500407146165586275663347712, coefficient := (-500407146165586275663347712) }, { argument := 60656955574288204908051038208, coefficient := (-60656955574288204908051038208) }, { argument := 2791825285740671293175365632, coefficient := (-2791825285740671293175365632) }, { argument := 601878497489106045376281968640, coefficient := (-601878497489106045376281968640) }, { argument := 2864814182099904529598251008, coefficient := (-2864814182099904529598251008) }, { argument := 91236120449041545528606720, coefficient := (-91236120449041545528606720) }, { argument := 2791825285740671293175365632, coefficient := (-2791825285740671293175365632) }, { argument := 1587508495813322892197756928, coefficient := (-1587508495813322892197756928) }, { argument := 2864814182099904529598251008, coefficient := (-2864814182099904529598251008) }, { argument := 44723946244120165618123014144, coefficient := (-44723946244120165618123014144) }, { argument := 1751733512621597674149249024, coefficient := (-1751733512621597674149249024) }, { argument := 60656955574288204908051038208, coefficient := (-60656955574288204908051038208) }, { argument := 2791825285740671293175365632, coefficient := (-2791825285740671293175365632) }, { argument := 91236120449041545528606720, coefficient := (-91236120449041545528606720) }, { argument := 1751733512621597674149249024, coefficient := (-1751733512621597674149249024) }, { argument := 91236120449041545528606720, coefficient := (-91236120449041545528606720) }, { argument := 2810072509830479602281086976, coefficient := (-2810072509830479602281086976) }, { argument := 1587508495813322892197756928, coefficient := (-1587508495813322892197756928) }, { argument := 500407146165586275663347712, coefficient := (-500407146165586275663347712) }, { argument := 4712928815006886154026876928, coefficient := (-4712928815006886154026876928) }, { argument := 169430412926474734334403149824, coefficient := (-169430412926474734334403149824) }, { argument := 169430479927355053056708313088, coefficient := (-169430479927355053056708313088) }, { argument := 4712871258859533171012141056, coefficient := (-4712871258859533171012141056) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 78627401939779592808038400, coefficient := (-78627401939779592808038400) }, { argument := 91236120449041545528606720, coefficient := (-91236120449041545528606720) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 91094449454555456172195840, coefficient := (-91094449454555456172195840) }, { argument := 91519462438013724241428480, coefficient := (-91519462438013724241428480) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }, { argument := 1509646117243768181914337280, coefficient := (-1509646117243768181914337280) }, { argument := 1751733512621597674149249024, coefficient := (-1751733512621597674149249024) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1749013429527464758506160128, coefficient := (-1749013429527464758506160128) }, { argument := 1757173678809863505435426816, coefficient := (-1757173678809863505435426816) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }] }

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
def constantNumerator : ℤ := (-21775558147966770505764137074688)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    279, 87988005, 7398844635, 3699421425, 43994895, 465,
    5565, 8325, 2415, 465, 9645, 4845,
    465, 5565, 465, 37709145, 3170933415, 1585466325,
    18854955, 3768809, 209162195, 14229, 2021724785, 14601,
    465, 14229, 8091, 14601, 227943, 279,
    209162195, 14229, 465, 279, 465, 7161,
    8091, 3768809, 7161, 85701, 128205, 37191,
    7161, 148533, 74613, 7161, 85701, 7161,
    87988005, 7398844635, 3699421425, 43994895, 8091, 96831,
    144855, 42021, 8091, 167823, 84303, 8091,
    96831, 8091, 993007485, 83501246595
  ]
def negativeCoefficients : Array ℕ := #[
    84322575918120384935755776, 202886526223909549517045760, 17060574177872995065287147520, 17060570061943223618843443200, 202890642153680995960750080, 4391800829068770048737280,
    105119877908678302456872960, 78627401939779592808038400, 91236120449041545528606720, 4391800829068770048737280, 91094449454555456172195840, 91519462438013724241428480,
    4391800829068770048737280, 105119877908678302456872960, 4391800829068770048737280, 173902736763351042443182080, 14623349295319710055960412160, 14623345767379905959008665600,
    173906264703155139394928640, 17380563771423305379086336, 1929180740530165804234178560, 134389105369504363491360768, 18647119848185233696652001280, 137902546032759379530350592,
    4391800829068770048737280, 134389105369504363491360768, 76417334425796598848028672, 137902546032759379530350592, 2152860766409511077891014656, 84322575918120384935755776,
    1929180740530165804234178560, 134389105369504363491360768, 4391800829068770048737280, 84322575918120384935755776, 4391800829068770048737280, 135267465535318117501108224,
    76417334425796598848028672, 17380563771423305379086336, 135267465535318117501108224, 3237692239587291715671687168, 2421723979745211458487582720, 2810072509830479602281086976,
    135267465535318117501108224, 2805709043200308050103631872, 2818799443090822706635997184, 135267465535318117501108224, 3237692239587291715671687168, 135267465535318117501108224,
    202886526223909549517045760, 17060574177872995065287147520, 17060570061943223618843443200, 202890642153680995960750080, 76417334425796598848028672, 1829085875611002462749589504,
    1368116793752164914859868160, 1587508495813322892197756928, 76417334425796598848028672, 1585043420509264937396207616, 1592438646421438801800855552, 76417334425796598848028672,
    1829085875611002462749589504, 76417334425796598848028672, 2289719367384122058835230720, 192540765721709515736812093440
  ]
def negativeScales : Array ℕ := #[
    8, 26, 32, 31, 25, 8,
    12, 13, 11, 8, 13, 12,
    8, 12, 8, 25, 31, 30,
    24, 21, 27, 13, 30, 13,
    8, 13, 12, 13, 17, 8,
    27, 13, 8, 8, 8, 12,
    12, 21, 12, 16, 16, 15,
    12, 17, 16, 12, 16, 12,
    26, 32, 31, 25, 12, 16,
    17, 15, 12, 17, 16, 12,
    16, 12, 29, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    8124121311829188, 26390803525387317, 32784652859051247, 31784652510995421, 25390832792837202, 8861086908132560,
    12442165972229357, 13023234556845987, 11237807473723136, 8861086908132560, 13235565522936466, 12242280950302444,
    8861086908132560, 12442165972229357, 8861086908132560, 25168411104050864, 31562260437245805, 30562260089189982,
    24168440371500750, 21845677253229287, 27640046874492154, 13796546654402698, 30912939477724391, 13833779561266426,
    8861086908132560, 13796546654402698, 12982102324703674, 13833779561266426, 17798313580599046, 8124121311829188,
    27640046874492154, 13796546654402698, 8861086908132560, 8124121311829188, 8861086908132560, 12805945352531863,
    12982102324703674, 21845677253229287, 12805945352531863, 16387024418036865, 16968093016757167, 15182665919530675,
    12805945352531863, 17180423968744005, 16187139396109983, 12805945352531863, 16387024418036865, 12805945352531863,
    26390803525387317, 32784652859051247, 31784652510995421, 25390832792837202, 12982102324703674, 16563181373192661,
    17144249957807353, 15358822874684503, 12982102324703674, 17356580923897833, 16363296351263811, 12982102324703674,
    16563181373192661, 12982102324703674, 29887229354974391, 36281078684699833
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
noncomputable def negativeCeiling : ℝ := 137179481 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 202886526223909549517045760, coefficient := (-202886526223909549517045760) }, { argument := 17060574177872995065287147520, coefficient := (-17060574177872995065287147520) }, { argument := 17060570061943223618843443200, coefficient := (-17060570061943223618843443200) }, { argument := 202890642153680995960750080, coefficient := (-202890642153680995960750080) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 78627401939779592808038400, coefficient := (-78627401939779592808038400) }, { argument := 91236120449041545528606720, coefficient := (-91236120449041545528606720) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 91094449454555456172195840, coefficient := (-91094449454555456172195840) }, { argument := 91519462438013724241428480, coefficient := (-91519462438013724241428480) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 173902736763351042443182080, coefficient := (-173902736763351042443182080) }, { argument := 14623349295319710055960412160, coefficient := (-14623349295319710055960412160) }, { argument := 14623345767379905959008665600, coefficient := (-14623345767379905959008665600) }, { argument := 173906264703155139394928640, coefficient := (-173906264703155139394928640) }, { argument := 17380563771423305379086336, coefficient := (-17380563771423305379086336) }, { argument := 1929180740530165804234178560, coefficient := (-1929180740530165804234178560) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 18647119848185233696652001280, coefficient := (-18647119848185233696652001280) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1929180740530165804234178560, coefficient := (-1929180740530165804234178560) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 17380563771423305379086336, coefficient := (-17380563771423305379086336) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 3237692239587291715671687168, coefficient := (-3237692239587291715671687168) }, { argument := 2421723979745211458487582720, coefficient := (-2421723979745211458487582720) }, { argument := 2810072509830479602281086976, coefficient := (-2810072509830479602281086976) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 2805709043200308050103631872, coefficient := (-2805709043200308050103631872) }, { argument := 2818799443090822706635997184, coefficient := (-2818799443090822706635997184) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 3237692239587291715671687168, coefficient := (-3237692239587291715671687168) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 202886526223909549517045760, coefficient := (-202886526223909549517045760) }, { argument := 17060574177872995065287147520, coefficient := (-17060574177872995065287147520) }, { argument := 17060570061943223618843443200, coefficient := (-17060570061943223618843443200) }, { argument := 202890642153680995960750080, coefficient := (-202890642153680995960750080) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 1368116793752164914859868160, coefficient := (-1368116793752164914859868160) }, { argument := 1587508495813322892197756928, coefficient := (-1587508495813322892197756928) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 1585043420509264937396207616, coefficient := (-1585043420509264937396207616) }, { argument := 1592438646421438801800855552, coefficient := (-1592438646421438801800855552) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 2289719367384122058835230720, coefficient := (-2289719367384122058835230720) }, { argument := 192540765721709515736812093440, coefficient := (-192540765721709515736812093440) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
