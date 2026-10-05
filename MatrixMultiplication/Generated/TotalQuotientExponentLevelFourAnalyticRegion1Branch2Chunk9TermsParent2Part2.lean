import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

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
def constantNumerator : ℤ := (-228259326437769504107073546223616)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    112135667757441, 76531, 4457429625984867, 2523, 5887, 76531,
    76531, 2523, 944443, 37845, 112135667757441, 76531,
    5887, 37845, 5887, 76531, 76531, 3150897249057,
    6435325, 538824195, 269412195, 3217565, 23704707, 1209694353,
    73437, 11889900123, 2421, 5649, 73437, 73437,
    2421, 906261, 36315, 1209694353, 73437, 5649,
    36315, 5649, 73437, 73437, 25357443, 120487309,
    4503208563, 36023767333, 965799643, 175, 3507, 5887,
    5649, 175, 5649, 3773, 91, 3507,
    21, 1125, 22545, 37845, 36315, 1125,
    36315, 24255, 585, 22545
  ]
def negativeCoefficients : Array ℕ := #[
    252507075763676515217983930368, 5782518868807949085589897216, 2509309800326957046944187285504, 3050119842887709407783682048, 222404571877228810984226816, 5782518868807949085589897216,
    5782518868807949085589897216, 3050119842887709407783682048, 71360095490893701352939061248, 5718974705414455139594403840, 252507075763676515217983930368, 5782518868807949085589897216,
    222404571877228810984226816, 5718974705414455139594403840, 222404571877228810984226816, 5782518868807949085589897216, 5782518868807949085589897216, 1773797459591978266115702784,
    237421586612289840506470400, 19879104051775139626604298240, 19879111246005328373329428480, 237414392382101093781340160, 437274663371271324158656512, 44629844274405320704074448896,
    5548742838439970168931090432, 438659889261897437650706497536, 2926809409287017231963652096, 213413186093845006497349632, 5548742838439970168931090432, 5548742838439970168931090432,
    2926809409287017231963652096, 68475145138110840656149610496, 5487767642413157309931847680, 44629844274405320704074448896, 5548742838439970168931090432, 213413186093845006497349632,
    5487767642413157309931847680, 213413186093845006497349632, 5548742838439970168931090432, 5548742838439970168931090432, 467762261384677753658277888, 4445197106505923043616882688,
    166139071744396712024123375616, 166130304140677372408634540032, 4453964710225262659105718272, 6611313076017503299174400, 132490714043390766115454976, 222404571877228810984226816,
    213413186093845006497349632, 6611313076017503299174400, 213413186093845006497349632, 142539909918937371130200064, 6875765599058203431141376, 132490714043390766115454976,
    6346860552976803167207424, 170005193383307227693056000, 3406904075401476842968842240, 5718974705414455139594403840, 5487767642413157309931847680, 170005193383307227693056000,
    5487767642413157309931847680, 3665311969344103829062287360, 176805401118639516800778240, 3406904075401476842968842240
  ]
def negativeScales : Array ℕ := #[
    46, 16, 51, 11, 12, 16,
    16, 11, 19, 15, 46, 16,
    12, 15, 12, 16, 16, 41,
    22, 29, 28, 21, 24, 30,
    16, 33, 11, 12, 16, 16,
    11, 19, 15, 30, 16, 12,
    15, 12, 16, 16, 24, 26,
    32, 35, 29, 7, 11, 12,
    12, 7, 12, 11, 6, 11,
    4, 10, 14, 15, 15, 10,
    15, 14, 9, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    46672238567461377, 16223756630453841, 51985133462676113, 11300924490976301, 12523316912313329, 16223756630453841,
    16223756630453841, 11300924490976301, 19849104204358487, 15207815086584820, 46672238567461377, 16223756630453841,
    12523316912313329, 15207815086584820, 12523316912313329, 16223756630453841, 16223756630453841, 41518899847401983,
    22617581579325264, 29005239393163415, 28005239915273381, 21617537862839240, 24498670225077859, 30171995429491591,
    16164219503476477, 33469017545146706, 11241387363998937, 12463779785335462, 16164219503476477, 16164219503476477,
    11241387363998937, 19789567076199844, 15148277959607456, 30171995429491591, 16164219503476477, 12463779785335462,
    15148277959607456, 12463779785335462, 16164219503476477, 16164219503476477, 24595905938195166, 26844305955182006,
    32068306150639567, 35068230013749878, 29847148690969260, 7451211111832378, 11776021715645854, 12523316912313329,
    12463779785335462, 7451211111832378, 12463779785335462, 11881496387932734, 6507794640199048, 11776021715645854,
    4392317422778766, 10135709286104400, 14460519889524952, 15207815086584820, 15148277959607456, 10135709286104400,
    15148277959607456, 14565994559084324, 9192292814470767, 14460519889524952
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
noncomputable def negativeCeiling : ℝ := 568222779 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 252507075763676515217983930368, coefficient := (-252507075763676515217983930368) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 2509309800326957046944187285504, coefficient := (-2509309800326957046944187285504) }, { argument := 3050119842887709407783682048, coefficient := (-3050119842887709407783682048) }, { argument := 222404571877228810984226816, coefficient := (-222404571877228810984226816) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 3050119842887709407783682048, coefficient := (-3050119842887709407783682048) }, { argument := 71360095490893701352939061248, coefficient := (-71360095490893701352939061248) }, { argument := 5718974705414455139594403840, coefficient := (-5718974705414455139594403840) }, { argument := 252507075763676515217983930368, coefficient := (-252507075763676515217983930368) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 222404571877228810984226816, coefficient := (-222404571877228810984226816) }, { argument := 5718974705414455139594403840, coefficient := (-5718974705414455139594403840) }, { argument := 222404571877228810984226816, coefficient := (-222404571877228810984226816) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 1773797459591978266115702784, coefficient := (-1773797459591978266115702784) }, { argument := 237421586612289840506470400, coefficient := (-237421586612289840506470400) }, { argument := 19879104051775139626604298240, coefficient := (-19879104051775139626604298240) }, { argument := 19879111246005328373329428480, coefficient := (-19879111246005328373329428480) }, { argument := 237414392382101093781340160, coefficient := (-237414392382101093781340160) }, { argument := 437274663371271324158656512, coefficient := (-437274663371271324158656512) }, { argument := 44629844274405320704074448896, coefficient := (-44629844274405320704074448896) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 438659889261897437650706497536, coefficient := (-438659889261897437650706497536) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 68475145138110840656149610496, coefficient := (-68475145138110840656149610496) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 44629844274405320704074448896, coefficient := (-44629844274405320704074448896) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 467762261384677753658277888, coefficient := (-467762261384677753658277888) }, { argument := 4445197106505923043616882688, coefficient := (-4445197106505923043616882688) }, { argument := 166139071744396712024123375616, coefficient := (-166139071744396712024123375616) }, { argument := 166130304140677372408634540032, coefficient := (-166130304140677372408634540032) }, { argument := 4453964710225262659105718272, coefficient := (-4453964710225262659105718272) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 222404571877228810984226816, coefficient := (-222404571877228810984226816) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 142539909918937371130200064, coefficient := (-142539909918937371130200064) }, { argument := 6875765599058203431141376, coefficient := (-6875765599058203431141376) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 6346860552976803167207424, coefficient := (-6346860552976803167207424) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }, { argument := 5718974705414455139594403840, coefficient := (-5718974705414455139594403840) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 3665311969344103829062287360, coefficient := (-3665311969344103829062287360) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }] }

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
def constantNumerator : ℤ := (-55662516927300161527236706435072)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    135, 50195535, 4202828721, 2101415121, 25097007, 175,
    3507, 5887, 5649, 175, 5649, 3773,
    91, 3507, 21, 50195535, 4202828721, 2101415121,
    25097007, 3997117, 228158511, 2275, 2289019365, 75,
    175, 2275, 2275, 75, 28075, 1125,
    228158511, 2275, 175, 1125, 175, 2275,
    2275, 4201917, 2275, 45591, 76531, 73437,
    2275, 73437, 49049, 1183, 45591, 273,
    50195535, 4202828721, 2101415121, 25097007, 2275, 45591,
    76531, 73437, 2275, 73437, 49049, 1183,
    45591, 273, 50195535, 4202828721
  ]
def negativeCoefficients : Array ℕ := #[
    163204985647974938585333760, 231486046946982594493808640, 19382126450480761135939190784, 19382133464855195163996192768, 231479032572548566436806656, 6611313076017503299174400,
    132490714043390766115454976, 222404571877228810984226816, 213413186093845006497349632, 6611313076017503299174400, 213413186093845006497349632, 142539909918937371130200064,
    6875765599058203431141376, 132490714043390766115454976, 6346860552976803167207424, 231486046946982594493808640, 19382126450480761135939190784, 19382133464855195163996192768,
    231479032572548566436806656, 18433448582918425456672768, 2104390830327822771592101888, 171894139976455085778534400, 21112477202960075517245521920, 90669436471097188102963200,
    6611313076017503299174400, 171894139976455085778534400, 171894139976455085778534400, 90669436471097188102963200, 2121287024105044629992243200, 170005193383307227693056000,
    2104390830327822771592101888, 171894139976455085778534400, 6611313076017503299174400, 170005193383307227693056000, 6611313076017503299174400, 171894139976455085778534400,
    171894139976455085778534400, 19377921879492354499411968, 171894139976455085778534400, 3444758565128159919001829376, 5782518868807949085589897216, 5548742838439970168931090432,
    171894139976455085778534400, 5548742838439970168931090432, 3706037657892371649385201664, 178769905575513289209675776, 3444758565128159919001829376, 165018374377396882347393024,
    231486046946982594493808640, 19382126450480761135939190784, 19382133464855195163996192768, 231479032572548566436806656, 171894139976455085778534400, 3444758565128159919001829376,
    5782518868807949085589897216, 5548742838439970168931090432, 171894139976455085778534400, 5548742838439970168931090432, 3706037657892371649385201664, 178769905575513289209675776,
    3444758565128159919001829376, 165018374377396882347393024, 7407553502303443023801876480, 620228046415384356350054105088
  ]
def negativeScales : Array ℕ := #[
    7, 25, 31, 30, 24, 7,
    11, 12, 12, 7, 12, 11,
    6, 11, 4, 25, 31, 30,
    24, 21, 27, 11, 31, 6,
    7, 11, 11, 6, 14, 10,
    27, 11, 7, 10, 7, 11,
    11, 22, 11, 15, 16, 16,
    11, 16, 15, 10, 15, 8,
    25, 31, 30, 24, 11, 15,
    16, 16, 11, 16, 15, 10,
    15, 8, 25, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    7076815597050831, 25581055703294337, 31968713531387334, 30968714053497423, 24581011986808319, 7451211111832378,
    11776021715645854, 12523316912313329, 12463779785335462, 7451211111832378, 12463779785335462, 11881496387932734,
    6507794640199048, 11776021715645854, 4392317422778766, 25581055703294337, 31968713531387334, 30968714053497423,
    24581011986808319, 21930528379441940, 27765461231072863, 11151650829973422, 31092082522066096, 6228818690495881,
    7451211111832378, 11151650829973422, 11151650829973422, 6228818690495881, 14776998402576533, 10135709286104400,
    27765461231072863, 11151650829973422, 7451211111832378, 10135709286104400, 7451211111832378, 11151650829973422,
    11151650829973422, 22002616234221609, 11151650829973422, 15476461433394026, 16223756630453841, 16164219503476477,
    11151650829973422, 16164219503476477, 15581936102954605, 10208234358339789, 15476461433394026, 8092757140919853,
    25581055703294337, 31968713531387334, 30968714053497423, 24581011986808319, 11151650829973422, 15476461433394026,
    16223756630453841, 16164219503476477, 11151650829973422, 16164219503476477, 15581936102954605, 10208234358339789,
    15476461433394026, 8092757140919853, 25581055703294337, 31968713531387334
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
noncomputable def negativeCeiling : ℝ := 306185161 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 163204985647974938585333760, coefficient := (-163204985647974938585333760) }, { argument := 231486046946982594493808640, coefficient := (-231486046946982594493808640) }, { argument := 19382126450480761135939190784, coefficient := (-19382126450480761135939190784) }, { argument := 19382133464855195163996192768, coefficient := (-19382133464855195163996192768) }, { argument := 231479032572548566436806656, coefficient := (-231479032572548566436806656) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 222404571877228810984226816, coefficient := (-222404571877228810984226816) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 142539909918937371130200064, coefficient := (-142539909918937371130200064) }, { argument := 6875765599058203431141376, coefficient := (-6875765599058203431141376) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 6346860552976803167207424, coefficient := (-6346860552976803167207424) }, { argument := 231486046946982594493808640, coefficient := (-231486046946982594493808640) }, { argument := 19382126450480761135939190784, coefficient := (-19382126450480761135939190784) }, { argument := 19382133464855195163996192768, coefficient := (-19382133464855195163996192768) }, { argument := 231479032572548566436806656, coefficient := (-231479032572548566436806656) }, { argument := 18433448582918425456672768, coefficient := (-18433448582918425456672768) }, { argument := 2104390830327822771592101888, coefficient := (-2104390830327822771592101888) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 21112477202960075517245521920, coefficient := (-21112477202960075517245521920) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 2121287024105044629992243200, coefficient := (-2121287024105044629992243200) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 2104390830327822771592101888, coefficient := (-2104390830327822771592101888) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 6611313076017503299174400, coefficient := (-6611313076017503299174400) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 19377921879492354499411968, coefficient := (-19377921879492354499411968) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 231486046946982594493808640, coefficient := (-231486046946982594493808640) }, { argument := 19382126450480761135939190784, coefficient := (-19382126450480761135939190784) }, { argument := 19382133464855195163996192768, coefficient := (-19382133464855195163996192768) }, { argument := 231479032572548566436806656, coefficient := (-231479032572548566436806656) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 7407553502303443023801876480, coefficient := (-7407553502303443023801876480) }, { argument := 620228046415384356350054105088, coefficient := (-620228046415384356350054105088) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
