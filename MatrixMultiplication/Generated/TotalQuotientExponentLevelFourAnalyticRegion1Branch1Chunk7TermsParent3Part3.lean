import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

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
def constantNumerator : ℤ := (-12505665777257838579778258041044992)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    584771626665, 22885014247767, 22885014247767, 584771626665, 286045842657, 61623,
    1599, 1063495566063, 99261, 17874228483, 99261, 103443,
    61623, 3075, 37457831655, 1465910745369, 1465910745369, 37457831655,
    517370827065, 1723941, 44733, 1923488762391, 2776887, 32329091403,
    2776887, 2893881, 1723941, 86025, 21516776955, 21516782085,
    12876736235313, 724220273107683, 2309455995, 221448714102771, 89978805, 149964675,
    4588919055, 149964675, 89978805, 73512683685, 4708890795, 181055247500771,
    4588919055, 149964675, 4708890795, 149964675, 4588919055, 149964675,
    12876736235313, 362373763168275, 16381045695, 13997095660813069, 184871801415, 16381045695,
    6998548813342541, 16381045695, 16381045695, 679111351527, 4212268893, 184871801415,
    679111351527, 181188436353315, 16381045695, 4212268893
  ]
def negativeCoefficients : Array ℕ := #[
    1348391567332010394904512430080, 52769250118969319947084637405184, 52769250118969319947084637405184, 1348391567332010394904512430080, 1319153613210567402967089020928, 4656102236382018352057417728,
    241634048195474006294396928, 4904507632672257548026959101952, 7499949111297981656906858496, 1318885273363642875855463514112, 7499949111297981656906858496, 7815932097399755357445685248,
    4656102236382018352057417728, 232340430957186544513843200, 86371879261985161974707650560, 3380160044340344035778167308288, 3380160044340344035778167308288, 86371879261985161974707650560,
    2385951809517874510540056821760, 8141081196844779039344295936, 422491239756415678688526336, 8870526232120774779563843518464, 13113478095516440488524644352, 2385465900986818653871241428992,
    13113478095516440488524644352, 13665966639813291760655794176, 8141081196844779039344295936, 406241576688861229508198400, 198457238889988250787265904640, 198457286205886799852265799680,
    7248958063887973787061190656, 815399538025480000984886280192, 85203887378518491736666275840, 7978530770519319824373097955328, 53114111612582955887791964160, 2766359979822028952489164800,
    84650615382554085946168442880, 88523519354304926479653273600, 53114111612582955887791964160, 1356069662108758592510188584960, 86863703366411709108159774720, 815400345177945202790462652416,
    84650615382554085946168442880, 2766359979822028952489164800, 86863703366411709108159774720, 2766359979822028952489164800, 84650615382554085946168442880, 88523519354304926479653273600,
    7248958063887973787061190656, 815993172386743828996109107200, 18886059849712913323728568320, 31518657401153462009536930906112, 213142675446760021796365271040, 18886059849712913323728568320,
    31518661827903694611980365070336, 18886059849712913323728568320, 18886059849712913323728568320, 782962081198098206649432932352, 19425661559704710847263670272, 213142675446760021796365271040,
    782962081198098206649432932352, 816000174444632265128662794240, 18886059849712913323728568320, 19425661559704710847263670272
  ]
def negativeScales : Array ℕ := #[
    39, 44, 44, 39, 38, 15,
    10, 39, 16, 34, 16, 16,
    15, 11, 35, 40, 40, 35,
    38, 20, 15, 40, 21, 34,
    21, 21, 20, 16, 34, 34,
    43, 49, 31, 47, 26, 27,
    32, 27, 26, 36, 32, 47,
    32, 27, 32, 27, 32, 27,
    43, 48, 33, 53, 37, 33,
    52, 33, 33, 39, 31, 37,
    39, 47, 33, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39089082356654021, 44379468423668582, 44379468423668582, 39089082356654021, 38057455420393904, 15911181303864252,
    10642954223498123, 39951951167832807, 16598939368622512, 34057161920120094, 16598939368622512, 16658476495620780,
    15911181303864252, 11586370695117825, 35124548336678809, 40414934403693378, 40414934403693378, 35124548336678809,
    38912407756428473, 20717278970040312, 15449051894878119, 40806862540384876, 21405037040014770, 34912113915922234,
    21405037040014770, 21464574166992205, 20717278970040312, 16392468366511711, 34324742938511756, 34324743282477058,
    43549832204799645, 49363421891183790, 31104905910933069, 47653965948325354, 26423081870959341, 27160047465125530,
    32095507212930820, 27160047465125530, 26423081870959341, 36097274139105008, 32132740119129795, 47363423319286490,
    32095507212930820, 27160047465125530, 32132740119129795, 27160047465125530, 32095507212930820, 27160047465125530,
    43549832204799645, 48364471832600630, 33931308411770332, 53635977023209774, 37427734230313817, 33931308411770332,
    52635977225834210, 33931308411770332, 33931308411770332, 39304857191316076, 31971950403721980, 37427734230313817,
    39304857191316076, 47364484212349863, 33931308411770332, 31971950403721980
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
noncomputable def negativeCeiling : ℝ := 29958661391 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1348391567332010394904512430080, coefficient := (-1348391567332010394904512430080) }, { argument := 52769250118969319947084637405184, coefficient := (-52769250118969319947084637405184) }, { argument := 52769250118969319947084637405184, coefficient := (-52769250118969319947084637405184) }, { argument := 1348391567332010394904512430080, coefficient := (-1348391567332010394904512430080) }, { argument := 1319153613210567402967089020928, coefficient := (-1319153613210567402967089020928) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 241634048195474006294396928, coefficient := (-241634048195474006294396928) }, { argument := 4904507632672257548026959101952, coefficient := (-4904507632672257548026959101952) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 1318885273363642875855463514112, coefficient := (-1318885273363642875855463514112) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 7815932097399755357445685248, coefficient := (-7815932097399755357445685248) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 86371879261985161974707650560, coefficient := (-86371879261985161974707650560) }, { argument := 3380160044340344035778167308288, coefficient := (-3380160044340344035778167308288) }, { argument := 3380160044340344035778167308288, coefficient := (-3380160044340344035778167308288) }, { argument := 86371879261985161974707650560, coefficient := (-86371879261985161974707650560) }, { argument := 2385951809517874510540056821760, coefficient := (-2385951809517874510540056821760) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 422491239756415678688526336, coefficient := (-422491239756415678688526336) }, { argument := 8870526232120774779563843518464, coefficient := (-8870526232120774779563843518464) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }, { argument := 2385465900986818653871241428992, coefficient := (-2385465900986818653871241428992) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }, { argument := 13665966639813291760655794176, coefficient := (-13665966639813291760655794176) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 406241576688861229508198400, coefficient := (-406241576688861229508198400) }, { argument := 198457238889988250787265904640, coefficient := (-198457238889988250787265904640) }, { argument := 198457286205886799852265799680, coefficient := (-198457286205886799852265799680) }, { argument := 7248958063887973787061190656, coefficient := (-7248958063887973787061190656) }, { argument := 815399538025480000984886280192, coefficient := (-815399538025480000984886280192) }, { argument := 85203887378518491736666275840, coefficient := (-85203887378518491736666275840) }, { argument := 7978530770519319824373097955328, coefficient := (-7978530770519319824373097955328) }, { argument := 53114111612582955887791964160, coefficient := (-53114111612582955887791964160) }, { argument := 2766359979822028952489164800, coefficient := (-2766359979822028952489164800) }, { argument := 84650615382554085946168442880, coefficient := (-84650615382554085946168442880) }, { argument := 88523519354304926479653273600, coefficient := (-88523519354304926479653273600) }, { argument := 53114111612582955887791964160, coefficient := (-53114111612582955887791964160) }, { argument := 1356069662108758592510188584960, coefficient := (-1356069662108758592510188584960) }, { argument := 86863703366411709108159774720, coefficient := (-86863703366411709108159774720) }, { argument := 815400345177945202790462652416, coefficient := (-815400345177945202790462652416) }, { argument := 84650615382554085946168442880, coefficient := (-84650615382554085946168442880) }, { argument := 2766359979822028952489164800, coefficient := (-2766359979822028952489164800) }, { argument := 86863703366411709108159774720, coefficient := (-86863703366411709108159774720) }, { argument := 2766359979822028952489164800, coefficient := (-2766359979822028952489164800) }, { argument := 84650615382554085946168442880, coefficient := (-84650615382554085946168442880) }, { argument := 88523519354304926479653273600, coefficient := (-88523519354304926479653273600) }, { argument := 7248958063887973787061190656, coefficient := (-7248958063887973787061190656) }, { argument := 815993172386743828996109107200, coefficient := (-815993172386743828996109107200) }, { argument := 18886059849712913323728568320, coefficient := (-18886059849712913323728568320) }, { argument := 31518657401153462009536930906112, coefficient := (-31518657401153462009536930906112) }, { argument := 213142675446760021796365271040, coefficient := (-213142675446760021796365271040) }, { argument := 18886059849712913323728568320, coefficient := (-18886059849712913323728568320) }, { argument := 31518661827903694611980365070336, coefficient := (-31518661827903694611980365070336) }, { argument := 18886059849712913323728568320, coefficient := (-18886059849712913323728568320) }, { argument := 18886059849712913323728568320, coefficient := (-18886059849712913323728568320) }, { argument := 782962081198098206649432932352, coefficient := (-782962081198098206649432932352) }, { argument := 19425661559704710847263670272, coefficient := (-19425661559704710847263670272) }, { argument := 213142675446760021796365271040, coefficient := (-213142675446760021796365271040) }, { argument := 782962081198098206649432932352, coefficient := (-782962081198098206649432932352) }, { argument := 816000174444632265128662794240, coefficient := (-816000174444632265128662794240) }, { argument := 18886059849712913323728568320, coefficient := (-18886059849712913323728568320) }, { argument := 19425661559704710847263670272, coefficient := (-19425661559704710847263670272) }] }

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
def constantNumerator : ℤ := (-2441102718724968558248146210127872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    16381045695, 18781194020198445, 52605, 1365, 67505244899084775, 84735,
    4696442695456635, 84735, 88305, 52605, 2625, 36503491995,
    1428562700901, 1428562700901, 36503491995, 286045842657, 61623, 1599,
    1063495566063, 99261, 17874228483, 99261, 103443, 61623,
    3075, 199930344510581, 199930456435595, 8452300305, 55611, 1443,
    31423754943, 89577, 528161139, 89577, 93351, 55611,
    2775, 142010727903, 142010761761, 257, 225, 675,
    1425, 3675, 3075, 86025, 2625, 3075,
    2775, 1425, 1425, 2775, 86025, 2775,
    225, 3675, 8554245, 4044227355, 153515645745, 16176920515,
    8554245, 1192924575, 46685055585, 46685055585
  ]
def negativeCoefficients : Array ℕ := #[
    18886059849712913323728568320, 5286436149433669039230466129920, 248420088831357686466478080, 12892060498234131433390080, 19001037235817016784094389862400, 400149723925959387182530560,
    5287724393306347303392761610240, 400149723925959387182530560, 417008572269804020595425280, 248420088831357686466478080, 12396212017532818685952000, 84171321828558788421211914240,
    3294041317096004060344328650752, 3294041317096004060344328650752, 84171321828558788421211914240, 1319153613210567402967089020928, 4656102236382018352057417728, 241634048195474006294396928,
    4904507632672257548026959101952, 7499949111297981656906858496, 1318885273363642875855463514112, 7499949111297981656906858496, 7815932097399755357445685248, 4656102236382018352057417728,
    232340430957186544513843200, 450203112518953741036539609088, 450203364551679412955313602560, 77958710280236092802665021440, 262615522478863839978848256, 13628749669561796086726656,
    289832982634243239469796818944, 423015422436014209307246592, 77942826886495493893486804992, 423015422436014209307246592, 440837633542364250343735296, 262615522478863839978848256,
    13104566989963265468006400, 163727222084240306899494371328, 163727261119856609878119284736, 19884411881021420665567182848, 17000519338330722769305600, 12750389503748042076979200,
    13458744476178488859033600, 17354696824545946160332800, 232340430957186544513843200, 406241576688861229508198400, 12396212017532818685952000, 232340430957186544513843200,
    13104566989963265468006400, 13458744476178488859033600, 13458744476178488859033600, 13104566989963265468006400, 406241576688861229508198400, 13104566989963265468006400,
    17000519338330722769305600, 17354696824545946160332800, 157797968258809563363409920, 18650706748395076242552913920, 176991489273017105869040517120, 18650719540059169855520112640,
    157797968258809563363409920, 2750696791782966941869670400, 107648409055424969292298321920, 107648409055424969292298321920
  ]
def negativeScales : Array ℕ := #[
    33, 54, 15, 10, 55, 16,
    52, 16, 16, 15, 11, 35,
    40, 40, 35, 38, 15, 10,
    39, 16, 34, 16, 16, 15,
    11, 47, 47, 32, 15, 10,
    34, 16, 28, 16, 16, 15,
    11, 37, 37, 8, 7, 9,
    10, 11, 11, 16, 11, 11,
    11, 10, 10, 11, 16, 11,
    7, 11, 23, 31, 37, 33,
    23, 30, 35, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33931308411770332, 54060138303887048, 15682912310909503, 10414685235807227, 55905849121446044, 16370670380943905,
    52060489829296228, 16370670380943905, 16430207507921289, 15682912310909503, 11358101707440849, 35087315430479834,
    40377701497494393, 40377701497494393, 35087315430479834, 38057455420393904, 15911181303864252, 10642954223498123,
    39951951167832807, 16598939368622512, 34057161920120094, 16598939368622512, 16658476495620780, 15911181303864252,
    11586370695117825, 47506490782759891, 47506491590409264, 32976696896480184, 15763082659843835, 10494855584491427,
    34871136535457419, 16450840729627935, 28976402930173505, 16450840729627935, 16510377856605633, 15763082659843835,
    11438272056124861, 37047208962982847, 37047209306948149, 8005624549193879, 7813781192070436, 9398743691938200,
    10476746203939589, 11843528536141147, 11586370695117825, 16392468366511711, 11358101707440849, 11586370695117825,
    11438272056124861, 10476746203939589, 10476746203939589, 11438272056124861, 16392468366511711, 11438272056124861,
    7813781192070436, 11843528536141147, 23028209096999409, 31913216963258337, 37159594740975035, 33913217952736435,
    23028209096999409, 30151855682674544, 35442241749689136, 35442241749689136
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
noncomputable def negativeCeiling : ℝ := 2736143569 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18886059849712913323728568320, coefficient := (-18886059849712913323728568320) }, { argument := 5286436149433669039230466129920, coefficient := (-5286436149433669039230466129920) }, { argument := 248420088831357686466478080, coefficient := (-248420088831357686466478080) }, { argument := 12892060498234131433390080, coefficient := (-12892060498234131433390080) }, { argument := 19001037235817016784094389862400, coefficient := (-19001037235817016784094389862400) }, { argument := 400149723925959387182530560, coefficient := (-400149723925959387182530560) }, { argument := 5287724393306347303392761610240, coefficient := (-5287724393306347303392761610240) }, { argument := 400149723925959387182530560, coefficient := (-400149723925959387182530560) }, { argument := 417008572269804020595425280, coefficient := (-417008572269804020595425280) }, { argument := 248420088831357686466478080, coefficient := (-248420088831357686466478080) }, { argument := 12396212017532818685952000, coefficient := (-12396212017532818685952000) }, { argument := 84171321828558788421211914240, coefficient := (-84171321828558788421211914240) }, { argument := 3294041317096004060344328650752, coefficient := (-3294041317096004060344328650752) }, { argument := 3294041317096004060344328650752, coefficient := (-3294041317096004060344328650752) }, { argument := 84171321828558788421211914240, coefficient := (-84171321828558788421211914240) }, { argument := 1319153613210567402967089020928, coefficient := (-1319153613210567402967089020928) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 241634048195474006294396928, coefficient := (-241634048195474006294396928) }, { argument := 4904507632672257548026959101952, coefficient := (-4904507632672257548026959101952) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 1318885273363642875855463514112, coefficient := (-1318885273363642875855463514112) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 7815932097399755357445685248, coefficient := (-7815932097399755357445685248) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 450203112518953741036539609088, coefficient := (-450203112518953741036539609088) }, { argument := 450203364551679412955313602560, coefficient := (-450203364551679412955313602560) }, { argument := 77958710280236092802665021440, coefficient := (-77958710280236092802665021440) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 289832982634243239469796818944, coefficient := (-289832982634243239469796818944) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 77942826886495493893486804992, coefficient := (-77942826886495493893486804992) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 163727222084240306899494371328, coefficient := (-163727222084240306899494371328) }, { argument := 163727261119856609878119284736, coefficient := (-163727261119856609878119284736) }, { argument := 19884411881021420665567182848, coefficient := (-19884411881021420665567182848) }, { argument := 17000519338330722769305600, coefficient := (-17000519338330722769305600) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 17354696824545946160332800, coefficient := (-17354696824545946160332800) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 406241576688861229508198400, coefficient := (-406241576688861229508198400) }, { argument := 12396212017532818685952000, coefficient := (-12396212017532818685952000) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 406241576688861229508198400, coefficient := (-406241576688861229508198400) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 17000519338330722769305600, coefficient := (-17000519338330722769305600) }, { argument := 17354696824545946160332800, coefficient := (-17354696824545946160332800) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 18650706748395076242552913920, coefficient := (-18650706748395076242552913920) }, { argument := 176991489273017105869040517120, coefficient := (-176991489273017105869040517120) }, { argument := 18650719540059169855520112640, coefficient := (-18650719540059169855520112640) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 2750696791782966941869670400, coefficient := (-2750696791782966941869670400) }, { argument := 107648409055424969292298321920, coefficient := (-107648409055424969292298321920) }, { argument := 107648409055424969292298321920, coefficient := (-107648409055424969292298321920) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
