import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 12, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1522624308170010663676806009192448)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10395525, 870408315, 435204315, 5197605, 57825, 1158813,
    1945233, 1866591, 57825, 1866591, 1246707, 30069,
    1158813, 6939, 3891391525, 325822845915, 162911481915, 1945636805,
    925160025, 68320647075, 712094678625, 68320647075, 925160025, 155932875,
    13056124725, 6528064725, 77964075, 65011245, 4800910335, 50039085525,
    4800910335, 65011245, 1537442577, 28557, 56862753519, 449397,
    13527, 113716909113, 13527, 13527, 1158813, 13527,
    449397, 1158813, 3083483079, 13527, 13527, 28557,
    924407089791, 1521513321, 5033299676033, 669425811, 127534509, 2673668505,
    1329713625, 924507753087, 1521513321, 127436205, 10639714286739, 419407724528493,
    618873935, 5817414989, 68695006785, 4827216693
  ]
def negativeCoefficients : Array ℕ := #[
    1534108713494795892503347200, 128449595411470132971904696320, 128449641897265198719974768640, 1534062227699730144433274880, 546141683743874468963942400, 10944679342227244358037405696,
    18372206241143937135947022336, 17629453551252267858156060672, 546141683743874468963942400, 17629453551252267858156060672, 11774814701517933550862598144, 567987351093629447722500096,
    10944679342227244358037405696, 524296016394119490205384704, 35891751776138662235026227200, 3005185325980853319321853624320, 3005186413554767045052743024640, 35890664202224936504136826880,
    2133273776050216326974668800, 315073372885689515503307980800, 3283957073211456617397092352000, 315073372885689515503307980800, 2133273776050216326974668800, 2876453837802742298443776000,
    240842991396506499322321305600, 240843078557372247599952691200, 2876366676936994020812390400, 4796983193712918875791687680, 708489314164577505131762810880, 7384465634897113258579407667200,
    708489314164577505131762810880, 4796983193712918875791687680, 14180404872971745493008777216, 269713239302616916735033344, 524466330745710100768308068352, 2122217330302169950099341312,
    255517805655110763222663168, 524426679815200113469163569152, 255517805655110763222663168, 255517805655110763222663168, 10944679342227244358037405696, 255517805655110763222663168,
    2122217330302169950099341312, 10944679342227244358037405696, 14220055803481732792153276416, 255517805655110763222663168, 255517805655110763222663168, 269713239302616916735033344,
    4163159425121392237096206336, 14033483418613444334340538368, 45335933090852514072925044736, 12348726611852460368987160576, 588149112022301868489179136, 12330119662418156668342763520,
    12264443465849797538217984000, 4163612772303747723036721152, 14033483418613444334340538368, 587695764839946382548664320, 47917013297086303030732652544, 1888844471902828709979019542528,
    22832418185669120511359057920, 26828091368161216600846893056, 316799802326159047095106928640, 712371447392876559954402607104
  ]
def negativeScales : Array ℕ := #[
    23, 29, 28, 22, 15, 20,
    20, 20, 15, 20, 20, 14,
    20, 12, 31, 38, 37, 30,
    29, 35, 39, 35, 29, 27,
    33, 32, 26, 25, 32, 35,
    32, 25, 30, 14, 35, 18,
    13, 36, 13, 13, 20, 13,
    18, 20, 31, 13, 13, 14,
    39, 30, 42, 29, 26, 31,
    30, 39, 30, 26, 43, 48,
    29, 32, 35, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23309459283953801, 29697117097868714, 28697117619978681, 22309415567467788, 15819405741365596, 20144216343831399,
    20891511544639398, 20831974415136888, 15819405741365596, 20831974415136888, 20249691013388697, 14875989271598903,
    20144216343831399, 12760512051639823, 31857638997635853, 38245296809480528, 37245297331590494, 30857595281148186,
    29785127689858793, 35991602608572119, 39373278115432779, 35991602608572119, 29785127689858793, 27216349879562319,
    33604007693415917, 32604008215525883, 26216306163076306, 25954185958193574, 32160660845500612, 35542336373058610,
    32160660845500612, 25954185958193574, 30517885381235758, 14801556808026795, 35726764910703915, 18777630968521050,
    13723554295483443, 36726655835325515, 13723554295483443, 13723554295483443, 20144216343831399, 13723554295483443,
    18777630968521050, 20144216343831399, 31521913783354549, 13723554295483443, 13723554295483443, 14801556808026795,
    39749737368661492, 30502859818832503, 42194641635202797, 29318348937078543, 26926312438440099, 31316173457847202,
    30308468425819081, 39749894462363619, 30502859818832503, 26925199975639476, 43274524643525267, 48575346761239328,
    29205070320601560, 32437731077391864, 35999486210434834, 32168544444576446
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
noncomputable def negativeCeiling : ℝ := 1336663871 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1534108713494795892503347200, coefficient := (-1534108713494795892503347200) }, { argument := 128449595411470132971904696320, coefficient := (-128449595411470132971904696320) }, { argument := 128449641897265198719974768640, coefficient := (-128449641897265198719974768640) }, { argument := 1534062227699730144433274880, coefficient := (-1534062227699730144433274880) }, { argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 18372206241143937135947022336, coefficient := (-18372206241143937135947022336) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 11774814701517933550862598144, coefficient := (-11774814701517933550862598144) }, { argument := 567987351093629447722500096, coefficient := (-567987351093629447722500096) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 524296016394119490205384704, coefficient := (-524296016394119490205384704) }, { argument := 35891751776138662235026227200, coefficient := (-35891751776138662235026227200) }, { argument := 3005185325980853319321853624320, coefficient := (-3005185325980853319321853624320) }, { argument := 3005186413554767045052743024640, coefficient := (-3005186413554767045052743024640) }, { argument := 35890664202224936504136826880, coefficient := (-35890664202224936504136826880) }, { argument := 2133273776050216326974668800, coefficient := (-2133273776050216326974668800) }, { argument := 315073372885689515503307980800, coefficient := (-315073372885689515503307980800) }, { argument := 3283957073211456617397092352000, coefficient := (-3283957073211456617397092352000) }, { argument := 315073372885689515503307980800, coefficient := (-315073372885689515503307980800) }, { argument := 2133273776050216326974668800, coefficient := (-2133273776050216326974668800) }, { argument := 2876453837802742298443776000, coefficient := (-2876453837802742298443776000) }, { argument := 240842991396506499322321305600, coefficient := (-240842991396506499322321305600) }, { argument := 240843078557372247599952691200, coefficient := (-240843078557372247599952691200) }, { argument := 2876366676936994020812390400, coefficient := (-2876366676936994020812390400) }, { argument := 4796983193712918875791687680, coefficient := (-4796983193712918875791687680) }, { argument := 708489314164577505131762810880, coefficient := (-708489314164577505131762810880) }, { argument := 7384465634897113258579407667200, coefficient := (-7384465634897113258579407667200) }, { argument := 708489314164577505131762810880, coefficient := (-708489314164577505131762810880) }, { argument := 4796983193712918875791687680, coefficient := (-4796983193712918875791687680) }, { argument := 14180404872971745493008777216, coefficient := (-14180404872971745493008777216) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 524466330745710100768308068352, coefficient := (-524466330745710100768308068352) }, { argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 524426679815200113469163569152, coefficient := (-524426679815200113469163569152) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 14220055803481732792153276416, coefficient := (-14220055803481732792153276416) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 4163159425121392237096206336, coefficient := (-4163159425121392237096206336) }, { argument := 14033483418613444334340538368, coefficient := (-14033483418613444334340538368) }, { argument := 45335933090852514072925044736, coefficient := (-45335933090852514072925044736) }, { argument := 12348726611852460368987160576, coefficient := (-12348726611852460368987160576) }, { argument := 588149112022301868489179136, coefficient := (-588149112022301868489179136) }, { argument := 12330119662418156668342763520, coefficient := (-12330119662418156668342763520) }, { argument := 12264443465849797538217984000, coefficient := (-12264443465849797538217984000) }, { argument := 4163612772303747723036721152, coefficient := (-4163612772303747723036721152) }, { argument := 14033483418613444334340538368, coefficient := (-14033483418613444334340538368) }, { argument := 587695764839946382548664320, coefficient := (-587695764839946382548664320) }, { argument := 47917013297086303030732652544, coefficient := (-47917013297086303030732652544) }, { argument := 1888844471902828709979019542528, coefficient := (-1888844471902828709979019542528) }, { argument := 22832418185669120511359057920, coefficient := (-22832418185669120511359057920) }, { argument := 26828091368161216600846893056, coefficient := (-26828091368161216600846893056) }, { argument := 316799802326159047095106928640, coefficient := (-316799802326159047095106928640) }, { argument := 712371447392876559954402607104, coefficient := (-712371447392876559954402607104) }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2226645298838391274641452427116544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    209703819733735, 68695006785, 618873935, 4827216693, 4827216693, 4827216693,
    4827216693, 4827216693, 5319899673881, 5817414989, 124881466375, 13247229253907,
    53181967293, 497868461372537, 1753251669, 4090920561, 53181967293, 53181967293,
    1753251669, 656300541429, 26298775035, 13247229253907, 53181967293, 4090920561,
    26298775035, 4090920561, 53181967293, 53181967293, 536893335187, 315330925,
    26402385555, 13201197555, 157660685, 925160025, 68320647075, 712094678625,
    68320647075, 925160025, 630683200631, 47937, 23192954540937, 754377,
    22707, 185540308858751, 22707, 22707, 1945233, 22707,
    754377, 1945233, 5048793073793, 22707, 22707, 47937,
    8334775, 615501325, 6415267375, 615501325, 8334775, 676338507,
    45999, 24684578229, 723879, 21789
  ]
def negativeCoefficients : Array ℕ := #[
    1888844088822037223425829765120, 316799802326159047095106928640, 22832418185669120511359057920, 22261607731027392498575081472, 22261607731027392498575081472, 22261607731027392498575081472,
    712371447392876559954402607104, 22261607731027392498575081472, 47917396377877789583922429952, 26828091368161216600846893056, 17997316013821796028514304000, 1909126935410787166155024891904,
    245258534997590738805951823872, 17937601736935038517667027746816, 129367139339388521567974588416, 9433020576830413030998147072, 245258534997590738805951823872, 245258534997590738805951823872,
    129367139339388521567974588416, 3026652030794443952517405474816, 242563386261353477939952353280, 1909126935410787166155024891904, 245258534997590738805951823872, 9433020576830413030998147072,
    242563386261353477939952353280, 9433020576830413030998147072, 245258534997590738805951823872, 245258534997590738805951823872, 19343620994287008066899542016, 2908414436000550546204262400,
    243519024634245460425902653440, 243519112763565272573285498880, 2908326306680738398821416960, 2133273776050216326974668800, 315073372885689515503307980800, 3283957073211456617397092352000,
    315073372885689515503307980800, 2133273776050216326974668800, 45445514037609653883807727616, 452752164178644365217890304, 1671228502850955621057567916032, 3562444660247754347372347392,
    428923102906084135469580288, 1671198531676955483113617620992, 428923102906084135469580288, 428923102906084135469580288, 18372206241143937135947022336, 428923102906084135469580288,
    3562444660247754347372347392, 18372206241143937135947022336, 45475485211609791827758022656, 428923102906084135469580288, 428923102906084135469580288, 452752164178644365217890304,
    153749461336952528070246400, 22707990838608253369607782400, 236681590862086963416006656000, 22707990838608253369607782400, 153749461336952528070246400, 12476243345823816091604877312,
    434448271691041620369604608, 455350097157825569089665368064, 3418421927253195907645046784, 411582573180986798244888576
  ]
def negativeScales : Array ℕ := #[
    47, 35, 29, 32, 32, 32,
    32, 32, 42, 32, 36, 43,
    35, 48, 30, 31, 35, 35,
    30, 39, 34, 43, 35, 31,
    34, 31, 35, 35, 38, 28,
    34, 33, 27, 29, 35, 39,
    35, 29, 39, 15, 44, 19,
    14, 47, 14, 14, 20, 14,
    19, 20, 42, 14, 14, 15,
    22, 29, 32, 29, 22, 29,
    15, 34, 19, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47575346468643075, 35999486210434834, 29205070320601560, 32168544444576446, 32168544444576446, 32168544444576446,
    32168544444576446, 32168544444576446, 42274536177352418, 32437731077391864, 36861768428773150, 43590755875506175,
    35630218094855190, 48822757956892738, 30707385955450916, 31929778384079696, 35630218094855190, 35630218094855190,
    30707385955450916, 39255565667044321, 34614276550981749, 43590755875506175, 35630218094855190, 31929778384079696,
    34614276550981749, 31929778384079696, 35630218094855190, 35630218094855190, 38965844553228639, 28232291423431341,
    34619949237288353, 33619949759398319, 27232247706945328, 29785127689858793, 35991602608572119, 39373278115432779,
    35991602608572119, 29785127689858793, 39198124548732952, 15548852004421171, 44398751849554443, 19524926165175017,
    14470849492418713, 47398725976580311, 14470849492418713, 14470849492418713, 20891511544639398, 14470849492418713,
    19524926165175017, 20891511544639398, 42199075687986212, 14470849492418713, 14470849492418713, 15548852004421171,
    22990711843434617, 29197186721525726, 32578862249085787, 29197186721525726, 22990711843434617, 29333170254330149,
    15489314877442711, 34522890943674555, 19465389038197124, 14411312365441260
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
noncomputable def negativeCeiling : ℝ := 4148654561 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1888844088822037223425829765120, coefficient := (-1888844088822037223425829765120) }, { argument := 316799802326159047095106928640, coefficient := (-316799802326159047095106928640) }, { argument := 22832418185669120511359057920, coefficient := (-22832418185669120511359057920) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 712371447392876559954402607104, coefficient := (-712371447392876559954402607104) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 47917396377877789583922429952, coefficient := (-47917396377877789583922429952) }, { argument := 26828091368161216600846893056, coefficient := (-26828091368161216600846893056) }, { argument := 17997316013821796028514304000, coefficient := (-17997316013821796028514304000) }, { argument := 1909126935410787166155024891904, coefficient := (-1909126935410787166155024891904) }, { argument := 245258534997590738805951823872, coefficient := (-245258534997590738805951823872) }, { argument := 17937601736935038517667027746816, coefficient := (-17937601736935038517667027746816) }, { argument := 129367139339388521567974588416, coefficient := (-129367139339388521567974588416) }, { argument := 9433020576830413030998147072, coefficient := (-9433020576830413030998147072) }, { argument := 245258534997590738805951823872, coefficient := (-245258534997590738805951823872) }, { argument := 245258534997590738805951823872, coefficient := (-245258534997590738805951823872) }, { argument := 129367139339388521567974588416, coefficient := (-129367139339388521567974588416) }, { argument := 3026652030794443952517405474816, coefficient := (-3026652030794443952517405474816) }, { argument := 242563386261353477939952353280, coefficient := (-242563386261353477939952353280) }, { argument := 1909126935410787166155024891904, coefficient := (-1909126935410787166155024891904) }, { argument := 245258534997590738805951823872, coefficient := (-245258534997590738805951823872) }, { argument := 9433020576830413030998147072, coefficient := (-9433020576830413030998147072) }, { argument := 242563386261353477939952353280, coefficient := (-242563386261353477939952353280) }, { argument := 9433020576830413030998147072, coefficient := (-9433020576830413030998147072) }, { argument := 245258534997590738805951823872, coefficient := (-245258534997590738805951823872) }, { argument := 245258534997590738805951823872, coefficient := (-245258534997590738805951823872) }, { argument := 19343620994287008066899542016, coefficient := (-19343620994287008066899542016) }, { argument := 2908414436000550546204262400, coefficient := (-2908414436000550546204262400) }, { argument := 243519024634245460425902653440, coefficient := (-243519024634245460425902653440) }, { argument := 243519112763565272573285498880, coefficient := (-243519112763565272573285498880) }, { argument := 2908326306680738398821416960, coefficient := (-2908326306680738398821416960) }, { argument := 2133273776050216326974668800, coefficient := (-2133273776050216326974668800) }, { argument := 315073372885689515503307980800, coefficient := (-315073372885689515503307980800) }, { argument := 3283957073211456617397092352000, coefficient := (-3283957073211456617397092352000) }, { argument := 315073372885689515503307980800, coefficient := (-315073372885689515503307980800) }, { argument := 2133273776050216326974668800, coefficient := (-2133273776050216326974668800) }, { argument := 45445514037609653883807727616, coefficient := (-45445514037609653883807727616) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 1671228502850955621057567916032, coefficient := (-1671228502850955621057567916032) }, { argument := 3562444660247754347372347392, coefficient := (-3562444660247754347372347392) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 1671198531676955483113617620992, coefficient := (-1671198531676955483113617620992) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 18372206241143937135947022336, coefficient := (-18372206241143937135947022336) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 3562444660247754347372347392, coefficient := (-3562444660247754347372347392) }, { argument := 18372206241143937135947022336, coefficient := (-18372206241143937135947022336) }, { argument := 45475485211609791827758022656, coefficient := (-45475485211609791827758022656) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 153749461336952528070246400, coefficient := (-153749461336952528070246400) }, { argument := 22707990838608253369607782400, coefficient := (-22707990838608253369607782400) }, { argument := 236681590862086963416006656000, coefficient := (-236681590862086963416006656000) }, { argument := 22707990838608253369607782400, coefficient := (-22707990838608253369607782400) }, { argument := 153749461336952528070246400, coefficient := (-153749461336952528070246400) }, { argument := 12476243345823816091604877312, coefficient := (-12476243345823816091604877312) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 455350097157825569089665368064, coefficient := (-455350097157825569089665368064) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
