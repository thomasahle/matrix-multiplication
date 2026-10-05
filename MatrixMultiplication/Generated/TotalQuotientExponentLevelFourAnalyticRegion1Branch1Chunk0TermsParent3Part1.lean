import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0

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
def constantNumerator : ℤ := (-307371475045518342660163675095040)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    693, 693, 234595, 1234034365, 676409825, 161983975,
    7633768025, 676409825, 1295871625, 676409825, 676409825, 28042018745,
    173933955, 7633768025, 28042018745, 1234034365, 676409825, 173933955,
    676409825, 645889641, 59451985137, 1542666281, 72409308583, 95763976059,
    5285785325, 95763976059, 99798641717, 59451985137, 2966665925, 8625627345,
    9385411375, 8625627345, 9385411375, 338204685, 2463997445, 676409825,
    27, 27, 8489885, 45, 45, 37,
    11125325, 455806625, 9385411375, 455806625, 11125325, 1156355949,
    11557724073, 23115442497, 1156355949, 338204685, 2463997445, 676409825,
    1205074787, 12044666599, 24089327311, 1205074787, 14020999941, 102150294077,
    28042018745, 1377, 1377, 86966919
  ]
def negativeCoefficients : Array ℕ := #[
    13404569487887008289142079488, 13404569487887008289142079488, 1107843565048804418907013120, 5690979027329419930721320960, 6238779465358832454703513600, 11952307723468664664909414400,
    70409082537621109131653939200, 6238779465358832454703513600, 11952306109378558215323648000, 6238779465358832454703513600, 6238779465358832454703513600, 258641971549590454050708520960,
    6417030307226227667695042560, 70409082537621109131653939200, 258641971549590454050708520960, 5690979027329419930721320960, 6238779465358832454703513600, 6417030307226227667695042560,
    6238779465358832454703513600, 11914560907387139831529209856, 137086944312027886891170791424, 7114292519187075966408065024, 166964497998107677559688790016, 220816694730152704034281095168,
    12188191139855583280522854400, 220816694730152704034281095168, 230120000332166572605737795584, 137086944312027886891170791424, 6840665883833726890776985600, 79557370054202902003329269760,
    86565140830553732091478016000, 79557370054202902003329269760, 86565140830553732091478016000, 6238775268724555685780520960, 22726365133094613426959810560, 6238779465358832454703513600,
    8356095265176316855569088512, 8356095265176316855569088512, 40092348367417757855079464960, 435213295061266502894223360, 435213295061266502894223360, 715684085211860471426056192,
    51306505752960679333068800, 8408148158476301952352256000, 86565140830553732091478016000, 8408148158476301952352256000, 51306505752960679333068800, 5332750562328633627321040896,
    213202378049182971122279251968, 213202325946354334929650712576, 5332750562328633627321040896, 6238775268724555685780520960, 22726365133094613426959810560, 6238779465358832454703513600,
    5557426546367262553379176448, 222184882204910630376501673984, 222184827906919449412436492288, 5557426546367262553379176448, 258641797569123722859072454656, 942170165946293830929105289216,
    258641971549590454050708520960, 13317526828874754988563234816, 13317526828874754988563234816, 6417025990688114419659964416
  ]
def negativeScales : Array ℕ := #[
    9, 9, 17, 30, 29, 27,
    32, 29, 30, 29, 29, 34,
    27, 32, 34, 30, 29, 27,
    29, 29, 35, 30, 36, 36,
    32, 36, 36, 35, 31, 33,
    33, 33, 33, 28, 31, 29,
    4, 4, 23, 5, 5, 5,
    23, 28, 33, 28, 23, 30,
    33, 34, 30, 28, 31, 29,
    30, 33, 34, 30, 33, 36,
    34, 10, 10, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9436711542137242, 9436711542137242, 17839812740923619, 30200735424749731, 29333322374458612, 27271275854112640,
    32829748201748899, 29333322374458612, 30271275659284996, 29333322374458612, 29333322374458612, 34706871161665405,
    27373964358955960, 32829748201748899, 34706871161665405, 30200735424749731, 29333322374458612, 27373964358955960,
    29333322374458612, 29266712441071953, 35791005932628015, 30522778857037273, 36075456123851762, 36478764002173522,
    32299470687053702, 36478764002173522, 36538301129151684, 35791005932628015, 31466195328670420, 33005982242313032,
    33127772835661011, 33005982242313032, 33127772835661011, 28333321404001886, 31198353614041909, 29333322374458612,
    4754887502413606, 4754887502413606, 23017313581164518, 5491853096329881, 5491853096329881, 5209453365628950,
    23407344145822237, 28763846653257832, 33127772835661011, 28763846653257832, 23407344145822237, 30106938409967018,
    33428138281672220, 34428137929103443, 30106938409967018, 28333321404001886, 31198353614041909, 29333322374458612,
    30166475536944382, 33487675408649743, 34487675056080966, 30166475536944382, 33706870191208677, 36571902401166234,
    34706871161665405, 10427312844134984, 10427312844134984, 26373963388499234
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
noncomputable def negativeCeiling : ℝ := 1006141779 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13404569487887008289142079488, coefficient := (-13404569487887008289142079488) }, { argument := 13404569487887008289142079488, coefficient := (-13404569487887008289142079488) }, { argument := 1107843565048804418907013120, coefficient := (-1107843565048804418907013120) }, { argument := 5690979027329419930721320960, coefficient := (-5690979027329419930721320960) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 11952307723468664664909414400, coefficient := (-11952307723468664664909414400) }, { argument := 70409082537621109131653939200, coefficient := (-70409082537621109131653939200) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 11952306109378558215323648000, coefficient := (-11952306109378558215323648000) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 258641971549590454050708520960, coefficient := (-258641971549590454050708520960) }, { argument := 6417030307226227667695042560, coefficient := (-6417030307226227667695042560) }, { argument := 70409082537621109131653939200, coefficient := (-70409082537621109131653939200) }, { argument := 258641971549590454050708520960, coefficient := (-258641971549590454050708520960) }, { argument := 5690979027329419930721320960, coefficient := (-5690979027329419930721320960) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 6417030307226227667695042560, coefficient := (-6417030307226227667695042560) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 11914560907387139831529209856, coefficient := (-11914560907387139831529209856) }, { argument := 137086944312027886891170791424, coefficient := (-137086944312027886891170791424) }, { argument := 7114292519187075966408065024, coefficient := (-7114292519187075966408065024) }, { argument := 166964497998107677559688790016, coefficient := (-166964497998107677559688790016) }, { argument := 220816694730152704034281095168, coefficient := (-220816694730152704034281095168) }, { argument := 12188191139855583280522854400, coefficient := (-12188191139855583280522854400) }, { argument := 220816694730152704034281095168, coefficient := (-220816694730152704034281095168) }, { argument := 230120000332166572605737795584, coefficient := (-230120000332166572605737795584) }, { argument := 137086944312027886891170791424, coefficient := (-137086944312027886891170791424) }, { argument := 6840665883833726890776985600, coefficient := (-6840665883833726890776985600) }, { argument := 79557370054202902003329269760, coefficient := (-79557370054202902003329269760) }, { argument := 86565140830553732091478016000, coefficient := (-86565140830553732091478016000) }, { argument := 79557370054202902003329269760, coefficient := (-79557370054202902003329269760) }, { argument := 86565140830553732091478016000, coefficient := (-86565140830553732091478016000) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 8356095265176316855569088512, coefficient := (-8356095265176316855569088512) }, { argument := 8356095265176316855569088512, coefficient := (-8356095265176316855569088512) }, { argument := 40092348367417757855079464960, coefficient := (-40092348367417757855079464960) }, { argument := 435213295061266502894223360, coefficient := (-435213295061266502894223360) }, { argument := 435213295061266502894223360, coefficient := (-435213295061266502894223360) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 86565140830553732091478016000, coefficient := (-86565140830553732091478016000) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 5332750562328633627321040896, coefficient := (-5332750562328633627321040896) }, { argument := 213202378049182971122279251968, coefficient := (-213202378049182971122279251968) }, { argument := 213202325946354334929650712576, coefficient := (-213202325946354334929650712576) }, { argument := 5332750562328633627321040896, coefficient := (-5332750562328633627321040896) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 5557426546367262553379176448, coefficient := (-5557426546367262553379176448) }, { argument := 222184882204910630376501673984, coefficient := (-222184882204910630376501673984) }, { argument := 222184827906919449412436492288, coefficient := (-222184827906919449412436492288) }, { argument := 5557426546367262553379176448, coefficient := (-5557426546367262553379176448) }, { argument := 258641797569123722859072454656, coefficient := (-258641797569123722859072454656) }, { argument := 942170165946293830929105289216, coefficient := (-942170165946293830929105289216) }, { argument := 258641971549590454050708520960, coefficient := (-258641971549590454050708520960) }, { argument := 13317526828874754988563234816, coefficient := (-13317526828874754988563234816) }, { argument := 13317526828874754988563234816, coefficient := (-13317526828874754988563234816) }, { argument := 6417025990688114419659964416, coefficient := (-6417025990688114419659964416) }] }

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
def constantNumerator : ℤ := (-205194860182921202952222483152896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    633599343, 173933955, 45, 45, 3, 717886407,
    7175241339, 14350479171, 717886407, 3816881445, 27807971165, 7633768025,
    27, 27, 14020999941, 102150294077, 28042018745, 22059,
    22059, 643, 1413, 1413, 1163, 616914429,
    2974100829, 77172277, 20658863227, 4790617503, 4941254985, 4790617503,
    4992452689, 2974100829, 148408225, 827133279, 455806625, 827133279,
    455806625, 8489885, 1377, 1377, 643, 19,
    35822675, 358045975, 716091775, 35822675, 338204685, 2463997445,
    676409825, 45, 45, 86966919, 633599343, 173933955,
    1413, 1413, 19, 45, 45, 37,
    338204685, 2463997445, 676409825, 1377
  ]
def negativeCoefficients : Array ℕ := #[
    23375689851183030953444376576, 6417030307226227667695042560, 13926825441960528092615147520, 13926825441960528092615147520, 928455029464035206174343168, 3310666705980973292797820928,
    132359840647634037834277453824, 132359808301268304584578695168, 3310666705980973292797820928, 70409035175605699882380165120, 256483263644924922961403576320, 70409082537621109131653939200,
    8356095265176316855569088512, 8356095265176316855569088512, 258641797569123722859072454656, 942170165946293830929105289216, 258641971549590454050708520960, 213341557239032839718748291072,
    213341557239032839718748291072, 12437428832195304949377138688, 13665697464923768190878613504, 13665697464923768190878613504, 22495691651389019682932523008, 5690031293570830973515333632,
    3428904802623150910397743104, 177947155425552741856968704, 23818047675139902084902551552, 5523205939554656256868220928, 5696879131952283085292175360, 5523205939554656256868220928,
    5755906065880379073142718464, 3428904802623150910397743104, 171103034063031482554777600, 15257915912561199121761828864, 8408148158476301952352256000, 15257915912561199121761828864,
    8408148158476301952352256000, 40092348367417757855079464960, 13317526828874754988563234816, 13317526828874754988563234816, 12437428832195304949377138688, 735026898325694538221355008,
    165202929440168327983923200, 6604782467446808275163545600, 6604780853356701825577779200, 165202929440168327983923200, 6238775268724555685780520960, 22726365133094613426959810560,
    6238779465358832454703513600, 435213295061266502894223360, 435213295061266502894223360, 6417025990688114419659964416, 23375689851183030953444376576, 6417030307226227667695042560,
    13665697464923768190878613504, 13665697464923768190878613504, 735026898325694538221355008, 435213295061266502894223360, 435213295061266502894223360, 715684085211860471426056192,
    6238775268724555685780520960, 22726365133094613426959810560, 6238779465358832454703513600, 13317526828874754988563234816
  ]
def negativeScales : Array ℕ := #[
    29, 27, 5, 5, 1, 29,
    32, 33, 29, 31, 34, 32,
    4, 4, 33, 36, 34, 14,
    14, 9, 10, 10, 10, 29,
    31, 26, 34, 32, 32, 32,
    32, 31, 27, 29, 28, 29,
    28, 23, 10, 10, 9, 4,
    25, 28, 29, 25, 28, 31,
    29, 5, 5, 26, 29, 27,
    10, 10, 4, 5, 5, 5,
    28, 31, 29, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29238995598539255, 27373964358955960, 5491853096329881, 5491853096329881, 1584962500724866, 29419180339884460,
    32740380211771605, 33740379859202826, 29419180339884460, 31829747231292150, 34694779440225398, 32829748201748899,
    4754887502413606, 4754887502413606, 33706870191208677, 36571902401166234, 34706871161665405, 14429079770309174,
    14429079770309174, 9328674927327948, 10464545750334019, 10464545750334019, 10183635381473219, 29200495148929183,
    31469806412954510, 26201579337900298, 34266041819635619, 32157564483036986, 32202230359499130, 32157564483036986,
    32217101610014350, 31469806412954510, 27144995809533930, 29623544573947581, 28763846653257832, 29623544573947581,
    28763846653257832, 23017313581164518, 10427312844134984, 10427312844134984, 9328674927327948, 4247927513443586,
    25094369736463962, 28415569608169157, 29415569255600380, 25094369736463962, 28333321404001886, 31198353614041909,
    29333322374458612, 5491853096329881, 5491853096329881, 26373963388499234, 29238995598539255, 27373964358955960,
    10464545750334019, 10464545750334019, 4247927513443586, 5491853096329881, 5491853096329881, 5209453365628950,
    28333321404001886, 31198353614041909, 29333322374458612, 10427312844134984
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
noncomputable def negativeCeiling : ℝ := 1096748343 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23375689851183030953444376576, coefficient := (-23375689851183030953444376576) }, { argument := 6417030307226227667695042560, coefficient := (-6417030307226227667695042560) }, { argument := 13926825441960528092615147520, coefficient := (-13926825441960528092615147520) }, { argument := 13926825441960528092615147520, coefficient := (-13926825441960528092615147520) }, { argument := 928455029464035206174343168, coefficient := (-928455029464035206174343168) }, { argument := 3310666705980973292797820928, coefficient := (-3310666705980973292797820928) }, { argument := 132359840647634037834277453824, coefficient := (-132359840647634037834277453824) }, { argument := 132359808301268304584578695168, coefficient := (-132359808301268304584578695168) }, { argument := 3310666705980973292797820928, coefficient := (-3310666705980973292797820928) }, { argument := 70409035175605699882380165120, coefficient := (-70409035175605699882380165120) }, { argument := 256483263644924922961403576320, coefficient := (-256483263644924922961403576320) }, { argument := 70409082537621109131653939200, coefficient := (-70409082537621109131653939200) }, { argument := 8356095265176316855569088512, coefficient := (-8356095265176316855569088512) }, { argument := 8356095265176316855569088512, coefficient := (-8356095265176316855569088512) }, { argument := 258641797569123722859072454656, coefficient := (-258641797569123722859072454656) }, { argument := 942170165946293830929105289216, coefficient := (-942170165946293830929105289216) }, { argument := 258641971549590454050708520960, coefficient := (-258641971549590454050708520960) }, { argument := 213341557239032839718748291072, coefficient := (-213341557239032839718748291072) }, { argument := 213341557239032839718748291072, coefficient := (-213341557239032839718748291072) }, { argument := 12437428832195304949377138688, coefficient := (-12437428832195304949377138688) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 22495691651389019682932523008, coefficient := (-22495691651389019682932523008) }, { argument := 5690031293570830973515333632, coefficient := (-5690031293570830973515333632) }, { argument := 3428904802623150910397743104, coefficient := (-3428904802623150910397743104) }, { argument := 177947155425552741856968704, coefficient := (-177947155425552741856968704) }, { argument := 23818047675139902084902551552, coefficient := (-23818047675139902084902551552) }, { argument := 5523205939554656256868220928, coefficient := (-5523205939554656256868220928) }, { argument := 5696879131952283085292175360, coefficient := (-5696879131952283085292175360) }, { argument := 5523205939554656256868220928, coefficient := (-5523205939554656256868220928) }, { argument := 5755906065880379073142718464, coefficient := (-5755906065880379073142718464) }, { argument := 3428904802623150910397743104, coefficient := (-3428904802623150910397743104) }, { argument := 171103034063031482554777600, coefficient := (-171103034063031482554777600) }, { argument := 15257915912561199121761828864, coefficient := (-15257915912561199121761828864) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 15257915912561199121761828864, coefficient := (-15257915912561199121761828864) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 40092348367417757855079464960, coefficient := (-40092348367417757855079464960) }, { argument := 13317526828874754988563234816, coefficient := (-13317526828874754988563234816) }, { argument := 13317526828874754988563234816, coefficient := (-13317526828874754988563234816) }, { argument := 12437428832195304949377138688, coefficient := (-12437428832195304949377138688) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 165202929440168327983923200, coefficient := (-165202929440168327983923200) }, { argument := 6604782467446808275163545600, coefficient := (-6604782467446808275163545600) }, { argument := 6604780853356701825577779200, coefficient := (-6604780853356701825577779200) }, { argument := 165202929440168327983923200, coefficient := (-165202929440168327983923200) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 435213295061266502894223360, coefficient := (-435213295061266502894223360) }, { argument := 435213295061266502894223360, coefficient := (-435213295061266502894223360) }, { argument := 6417025990688114419659964416, coefficient := (-6417025990688114419659964416) }, { argument := 23375689851183030953444376576, coefficient := (-23375689851183030953444376576) }, { argument := 6417030307226227667695042560, coefficient := (-6417030307226227667695042560) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 13665697464923768190878613504, coefficient := (-13665697464923768190878613504) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 435213295061266502894223360, coefficient := (-435213295061266502894223360) }, { argument := 435213295061266502894223360, coefficient := (-435213295061266502894223360) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 13317526828874754988563234816, coefficient := (-13317526828874754988563234816) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0
