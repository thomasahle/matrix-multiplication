import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 22, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-548494815649656711324123093008384)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    30247, 3762081, 553, 7880711, 175, 21,
    553, 1099, 175, 16961, 1085, 3762087,
    553, 21, 1085, 21, 553, 553,
    30247, 8758742047, 16852711463, 6272812037, 176336907747, 7809793117,
    6272810117, 7809793117, 15208544491, 287318178357, 15208544491, 176336907747,
    287318178357, 8758762527, 15208544491, 15208544491, 16852711463, 1073207089945,
    314743065, 260787111, 133120155480585, 1753568505, 34342615827159, 7023266679,
    7023266679, 5026896381, 260787111, 105027525, 4110247995, 4110247995,
    105027525, 314743065, 1132121445, 157371585, 1058565637, 105027525,
    1058565745, 105027525, 260787111, 938043483, 130393599, 1031798661,
    1031798907, 30247, 8758742929, 16852715481
  ]
def negativeCoefficients : Array ℕ := #[
    1142699352058865270229303296, 71063700880962870940746645504, 21393151303900477875600490496, 595449687801313993626742685696, 13539969179683846756709171200, 812398150781030805402550272,
    21393151303900477875600490496, 21257751612103639408033398784, 13539969179683846756709171200, 328073453223739606915063218176, 20986952228509962472899215360, 71063814217758459812231774208,
    21393151303900477875600490496, 812398150781030805402550272, 20986952228509962472899215360, 812398150781030805402550272, 21393151303900477875600490496, 21393151303900477875600490496,
    1142699352058865270229303296, 40392568237161979251143999488, 19429853456627017340722085888, 925703666152189524949740814336, 203302612997390010711457923072, 18008156862239674608474128384,
    925703382810200552771027992576, 18008156862239674608474128384, 17534257997443893697724809216, 662510612984501713227548196864, 17534257997443893697724809216, 203302612997390010711457923072,
    662510612984501713227548196864, 40392662684491636644048273408, 17534257997443893697724809216, 17534257997443893697724809216, 19429853456627017340722085888, 309330883223531288608720814080,
    92895756304478883126328688640, 4810673094339085019042021376, 1199039765235730193733459640320, 129390517709809872925957816320, 309330783684242741326384201728, 129556402988925013788683403264,
    129556402988925013788683403264, 92729871025363742263603101696, 4810673094339085019042021376, 3874831748740263550176460800, 151641385686485633484026019840, 151641385686485633484026019840,
    3874831748740263550176460800, 92895756304478883126328688640, 334143272900371905372928081920, 92895787295008926958375403520, 39054178781924652918750838784, 3874831748740263550176460800,
    39054182766421372840013987840, 3874831748740263550176460800, 4810673094339085019042021376, 17303848060912116528240918528, 4810674699205819431773011968, 19033325835063200660299186176,
    19033330372962242792848883712, 1142699352058865270229303296, 40392572304669047504100130816, 19429858089065622851033235456
  ]
def negativeScales : Array ℕ := #[
    14, 21, 9, 22, 7, 4,
    9, 10, 7, 14, 10, 21,
    9, 4, 10, 4, 9, 9,
    14, 33, 33, 32, 37, 32,
    32, 32, 33, 38, 33, 37,
    38, 33, 33, 33, 33, 39,
    28, 27, 46, 30, 44, 32,
    32, 32, 27, 26, 31, 31,
    26, 28, 30, 27, 29, 26,
    29, 26, 27, 29, 26, 29,
    29, 14, 33, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14884504440946755, 21843099482180234, 9111135670234708, 22909894370446650, 7451211111832378, 4392317422778766,
    9111135670234708, 10101975670949232, 7451211111832378, 14049933611508951, 10083479327331842, 21843101783077954,
    9111135670234708, 4392317422778766, 10083479327331842, 4392317422778766, 9111135670234708, 9111135670234708,
    14884504440946755, 33028076535128383, 33972261691858168, 32546465187343781, 37359543509632094, 32862637187776507,
    32546464745759546, 32862637187776507, 33824163038810487, 38063858317507984, 33824163038810487, 37359543509632094,
    38063858317507984, 33028079908484938, 33824163038810487, 33824163038810487, 33972261691858168, 39965065642703883,
    28229599349274063, 27958297339440358, 46919722358236849, 30707646646165271, 44965065178460250, 32709495070561436,
    32709495070561436, 32227020805172287, 27958297339440358, 26646192229648104, 31936578304938546, 31936578304938546,
    26646192229648104, 28229599349274063, 30076381581326938, 27229599830564903, 29979463598280324, 26646192229648104,
    29979463745471102, 26646192229648104, 27958297339440358, 29805079560225814, 26958297820731294, 29942514342537762,
    29942514686503118, 14884504440946755, 33028076680406890, 33972262035823556
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
noncomputable def negativeCeiling : ℝ := 3479595259 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1142699352058865270229303296, coefficient := (-1142699352058865270229303296) }, { argument := 71063700880962870940746645504, coefficient := (-71063700880962870940746645504) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 595449687801313993626742685696, coefficient := (-595449687801313993626742685696) }, { argument := 13539969179683846756709171200, coefficient := (-13539969179683846756709171200) }, { argument := 812398150781030805402550272, coefficient := (-812398150781030805402550272) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 21257751612103639408033398784, coefficient := (-21257751612103639408033398784) }, { argument := 13539969179683846756709171200, coefficient := (-13539969179683846756709171200) }, { argument := 328073453223739606915063218176, coefficient := (-328073453223739606915063218176) }, { argument := 20986952228509962472899215360, coefficient := (-20986952228509962472899215360) }, { argument := 71063814217758459812231774208, coefficient := (-71063814217758459812231774208) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 812398150781030805402550272, coefficient := (-812398150781030805402550272) }, { argument := 20986952228509962472899215360, coefficient := (-20986952228509962472899215360) }, { argument := 812398150781030805402550272, coefficient := (-812398150781030805402550272) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 1142699352058865270229303296, coefficient := (-1142699352058865270229303296) }, { argument := 40392568237161979251143999488, coefficient := (-40392568237161979251143999488) }, { argument := 19429853456627017340722085888, coefficient := (-19429853456627017340722085888) }, { argument := 925703666152189524949740814336, coefficient := (-925703666152189524949740814336) }, { argument := 203302612997390010711457923072, coefficient := (-203302612997390010711457923072) }, { argument := 18008156862239674608474128384, coefficient := (-18008156862239674608474128384) }, { argument := 925703382810200552771027992576, coefficient := (-925703382810200552771027992576) }, { argument := 18008156862239674608474128384, coefficient := (-18008156862239674608474128384) }, { argument := 17534257997443893697724809216, coefficient := (-17534257997443893697724809216) }, { argument := 662510612984501713227548196864, coefficient := (-662510612984501713227548196864) }, { argument := 17534257997443893697724809216, coefficient := (-17534257997443893697724809216) }, { argument := 203302612997390010711457923072, coefficient := (-203302612997390010711457923072) }, { argument := 662510612984501713227548196864, coefficient := (-662510612984501713227548196864) }, { argument := 40392662684491636644048273408, coefficient := (-40392662684491636644048273408) }, { argument := 17534257997443893697724809216, coefficient := (-17534257997443893697724809216) }, { argument := 17534257997443893697724809216, coefficient := (-17534257997443893697724809216) }, { argument := 19429853456627017340722085888, coefficient := (-19429853456627017340722085888) }, { argument := 309330883223531288608720814080, coefficient := (-309330883223531288608720814080) }, { argument := 92895756304478883126328688640, coefficient := (-92895756304478883126328688640) }, { argument := 4810673094339085019042021376, coefficient := (-4810673094339085019042021376) }, { argument := 1199039765235730193733459640320, coefficient := (-1199039765235730193733459640320) }, { argument := 129390517709809872925957816320, coefficient := (-129390517709809872925957816320) }, { argument := 309330783684242741326384201728, coefficient := (-309330783684242741326384201728) }, { argument := 129556402988925013788683403264, coefficient := (-129556402988925013788683403264) }, { argument := 129556402988925013788683403264, coefficient := (-129556402988925013788683403264) }, { argument := 92729871025363742263603101696, coefficient := (-92729871025363742263603101696) }, { argument := 4810673094339085019042021376, coefficient := (-4810673094339085019042021376) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 92895756304478883126328688640, coefficient := (-92895756304478883126328688640) }, { argument := 334143272900371905372928081920, coefficient := (-334143272900371905372928081920) }, { argument := 92895787295008926958375403520, coefficient := (-92895787295008926958375403520) }, { argument := 39054178781924652918750838784, coefficient := (-39054178781924652918750838784) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 39054182766421372840013987840, coefficient := (-39054182766421372840013987840) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 4810673094339085019042021376, coefficient := (-4810673094339085019042021376) }, { argument := 17303848060912116528240918528, coefficient := (-17303848060912116528240918528) }, { argument := 4810674699205819431773011968, coefficient := (-4810674699205819431773011968) }, { argument := 19033325835063200660299186176, coefficient := (-19033325835063200660299186176) }, { argument := 19033330372962242792848883712, coefficient := (-19033330372962242792848883712) }, { argument := 1142699352058865270229303296, coefficient := (-1142699352058865270229303296) }, { argument := 40392572304669047504100130816, coefficient := (-40392572304669047504100130816) }, { argument := 19429858089065622851033235456, coefficient := (-19429858089065622851033235456) }] }

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

end TermShard0


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1314003754596399469619405234634752)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12545624123, 176336949789, 7809794979, 12545620283, 7809794979, 15208548117,
    287318246859, 15208548117, 176336949789, 287318246859, 8758763409, 15208548117,
    15208548117, 16852715481, 133120155480585, 1132121445, 938043483, 16429749128621049,
    6307533765, 4259843766047463, 25262481387, 25262481387, 18081596793, 938043483,
    24035957525, 4110247995, 24035957621, 4110247995, 1753568505, 6307533765,
    876784545, 10796137209, 10796139783, 3762081, 478150599, 478150713,
    553, 34342615827159, 157371585, 130393599, 4259843766047463, 876784545,
    1098963352834617, 3511634511, 3511634511, 2513449029, 130393599, 24035950229,
    4110247995, 24035950325, 4110247995, 7880711, 478150599, 478150713,
    175, 21, 105027525, 4110247995, 4110247995, 105027525,
    7023266679, 25262481387, 3511634511, 931135377
  ]
def negativeCoefficients : Array ℕ := #[
    925703669767751363396812931072, 203302661468515907392518488064, 18008161155719357764372267008, 925703386425762391218100109312, 18008161155719357764372267008, 17534262177937269402151944192,
    662510770939359530384011296768, 17534262177937269402151944192, 203302661468515907392518488064, 662510770939359530384011296768, 40392666751998704897004404736, 17534262177937269402151944192,
    17534262177937269402151944192, 19429858089065622851033235456, 1199039765235730193733459640320, 334143272900371905372928081920, 17303848060912116528240918528, 4624563253340530477119144198144,
    465413844396946582483721256960, 1199039424839242794190113865728, 466010528812840103743315771392, 466010528812840103743315771392, 333546588484478384113333567488, 17303848060912116528240918528,
    886770314060456503657942220800, 151641385686485633484026019840, 886770317602231365810176131072, 151641385686485633484026019840, 129390517709809872925957816320, 465413844396946582483721256960,
    129390560875191005406308597760, 199153580079075928860203679744, 199153627560995174588589539328, 71063700880962870940746645504, 17640643456887844514423635968, 17640647662745493320201404416,
    21393151303900477875600490496, 309330783684242741326384201728, 92895787295008926958375403520, 4810674699205819431773011968, 1199039424839242794190113865728, 129390560875191005406308597760,
    309330684144988252516229578752, 129556446209646378490162839552, 129556446209646378490162839552, 92729901960553553874521161728, 4810674699205819431773011968, 886770044885566980088165040128,
    151641385686485633484026019840, 886770048427341842240398950400, 151641385686485633484026019840, 595449687801313993626742685696, 17640643456887844514423635968, 17640647662745493320201404416,
    13539969179683846756709171200, 812398150781030805402550272, 3874831748740263550176460800, 151641385686485633484026019840, 151641385686485633484026019840, 3874831748740263550176460800,
    129556402988925013788683403264, 466010528812840103743315771392, 129556446209646378490162839552, 17176415997496059132465119232
  ]
def negativeScales : Array ℕ := #[
    33, 37, 32, 33, 32, 33,
    38, 33, 37, 38, 33, 33,
    33, 33, 46, 30, 29, 53,
    32, 51, 34, 34, 34, 29,
    34, 31, 34, 31, 30, 32,
    29, 33, 33, 21, 28, 28,
    9, 44, 27, 26, 51, 29,
    49, 31, 31, 31, 26, 34,
    31, 34, 31, 22, 28, 28,
    7, 4, 26, 31, 31, 26,
    32, 34, 31, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33546465192978579, 37359543853597396, 32862637531741823, 33546464751394346, 32862637531741823, 33824163382775796,
    38063858661473286, 33824163382775796, 37359543853597396, 38063858661473286, 33028080053763105, 33824163382775796,
    33824163382775796, 33972262035823556, 46919722358236849, 30076381581326938, 29805079560225814, 53867159972051847,
    32554428878133102, 51919721948668742, 34556277302525558, 34556277302525558, 34073803037225162, 29805079560225814,
    34484475226410453, 31936578304938546, 34484475232172600, 31936578304938546, 30707646646165271, 32554428878133102,
    29707647127456111, 33329796166238042, 33329796510203343, 21843099482180234, 28832889843427055, 28832890187392365,
    9111135670234708, 44965065178460250, 27229599830564903, 26958297820731294, 51919721948668742, 29707647127456111,
    49965064714216626, 31709495551852277, 31709495551852277, 31227021286463126, 26958297820731294, 34484474788487204,
    31936578304938546, 34484474794249353, 31936578304938546, 22909894370446650, 28832889843427055, 28832890187392365,
    7451211111832378, 4392317422778766, 26646192229648104, 31936578304938546, 31936578304938546, 26646192229648104,
    32709495070561436, 34556277302525558, 31709495551852277, 29794415694943711
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
noncomputable def negativeCeiling : ℝ := 5479230467 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 925703669767751363396812931072, coefficient := (-925703669767751363396812931072) }, { argument := 203302661468515907392518488064, coefficient := (-203302661468515907392518488064) }, { argument := 18008161155719357764372267008, coefficient := (-18008161155719357764372267008) }, { argument := 925703386425762391218100109312, coefficient := (-925703386425762391218100109312) }, { argument := 18008161155719357764372267008, coefficient := (-18008161155719357764372267008) }, { argument := 17534262177937269402151944192, coefficient := (-17534262177937269402151944192) }, { argument := 662510770939359530384011296768, coefficient := (-662510770939359530384011296768) }, { argument := 17534262177937269402151944192, coefficient := (-17534262177937269402151944192) }, { argument := 203302661468515907392518488064, coefficient := (-203302661468515907392518488064) }, { argument := 662510770939359530384011296768, coefficient := (-662510770939359530384011296768) }, { argument := 40392666751998704897004404736, coefficient := (-40392666751998704897004404736) }, { argument := 17534262177937269402151944192, coefficient := (-17534262177937269402151944192) }, { argument := 17534262177937269402151944192, coefficient := (-17534262177937269402151944192) }, { argument := 19429858089065622851033235456, coefficient := (-19429858089065622851033235456) }, { argument := 1199039765235730193733459640320, coefficient := (-1199039765235730193733459640320) }, { argument := 334143272900371905372928081920, coefficient := (-334143272900371905372928081920) }, { argument := 17303848060912116528240918528, coefficient := (-17303848060912116528240918528) }, { argument := 4624563253340530477119144198144, coefficient := (-4624563253340530477119144198144) }, { argument := 465413844396946582483721256960, coefficient := (-465413844396946582483721256960) }, { argument := 1199039424839242794190113865728, coefficient := (-1199039424839242794190113865728) }, { argument := 466010528812840103743315771392, coefficient := (-466010528812840103743315771392) }, { argument := 466010528812840103743315771392, coefficient := (-466010528812840103743315771392) }, { argument := 333546588484478384113333567488, coefficient := (-333546588484478384113333567488) }, { argument := 17303848060912116528240918528, coefficient := (-17303848060912116528240918528) }, { argument := 886770314060456503657942220800, coefficient := (-886770314060456503657942220800) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 886770317602231365810176131072, coefficient := (-886770317602231365810176131072) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 129390517709809872925957816320, coefficient := (-129390517709809872925957816320) }, { argument := 465413844396946582483721256960, coefficient := (-465413844396946582483721256960) }, { argument := 129390560875191005406308597760, coefficient := (-129390560875191005406308597760) }, { argument := 199153580079075928860203679744, coefficient := (-199153580079075928860203679744) }, { argument := 199153627560995174588589539328, coefficient := (-199153627560995174588589539328) }, { argument := 71063700880962870940746645504, coefficient := (-71063700880962870940746645504) }, { argument := 17640643456887844514423635968, coefficient := (-17640643456887844514423635968) }, { argument := 17640647662745493320201404416, coefficient := (-17640647662745493320201404416) }, { argument := 21393151303900477875600490496, coefficient := (-21393151303900477875600490496) }, { argument := 309330783684242741326384201728, coefficient := (-309330783684242741326384201728) }, { argument := 92895787295008926958375403520, coefficient := (-92895787295008926958375403520) }, { argument := 4810674699205819431773011968, coefficient := (-4810674699205819431773011968) }, { argument := 1199039424839242794190113865728, coefficient := (-1199039424839242794190113865728) }, { argument := 129390560875191005406308597760, coefficient := (-129390560875191005406308597760) }, { argument := 309330684144988252516229578752, coefficient := (-309330684144988252516229578752) }, { argument := 129556446209646378490162839552, coefficient := (-129556446209646378490162839552) }, { argument := 129556446209646378490162839552, coefficient := (-129556446209646378490162839552) }, { argument := 92729901960553553874521161728, coefficient := (-92729901960553553874521161728) }, { argument := 4810674699205819431773011968, coefficient := (-4810674699205819431773011968) }, { argument := 886770044885566980088165040128, coefficient := (-886770044885566980088165040128) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 886770048427341842240398950400, coefficient := (-886770048427341842240398950400) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 595449687801313993626742685696, coefficient := (-595449687801313993626742685696) }, { argument := 17640643456887844514423635968, coefficient := (-17640643456887844514423635968) }, { argument := 17640647662745493320201404416, coefficient := (-17640647662745493320201404416) }, { argument := 13539969179683846756709171200, coefficient := (-13539969179683846756709171200) }, { argument := 812398150781030805402550272, coefficient := (-812398150781030805402550272) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 151641385686485633484026019840, coefficient := (-151641385686485633484026019840) }, { argument := 3874831748740263550176460800, coefficient := (-3874831748740263550176460800) }, { argument := 129556402988925013788683403264, coefficient := (-129556402988925013788683403264) }, { argument := 466010528812840103743315771392, coefficient := (-466010528812840103743315771392) }, { argument := 129556446209646378490162839552, coefficient := (-129556446209646378490162839552) }, { argument := 17176415997496059132465119232, coefficient := (-17176415997496059132465119232) }] }

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

end TermShard1


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22
