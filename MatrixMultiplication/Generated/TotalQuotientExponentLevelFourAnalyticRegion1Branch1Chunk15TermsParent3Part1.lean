import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

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
def constantNumerator : ℤ := (-91859517332977690405591010884190208)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    9604957287, 558168971365695, 39127850252424279, 193432061181, 192944203833381061, 61211110843,
    7343711449, 193429927165, 384445383431, 61211110843, 5933114025461, 379543885089,
    1222747430162151, 193429927165, 7343711449, 379543885089, 7343711449, 193429927165,
    193444865277, 558168971365695, 25773430280818629, 33637907857, 124827287194996955, 351967377333,
    15588298763, 998618297453148261, 15588298763, 30356160749, 573485307123, 30356160749,
    351967377333, 573485307123, 12886772614887551, 30356160749, 30356160749, 33637907857,
    585, 16965, 15015, 975, 585, 975,
    29835, 975, 585, 477945, 30615, 16965,
    29835, 975, 30615, 975, 29835, 975,
    585, 16948628697, 169400757669, 338801432541, 16948628697, 1339896784989543,
    3045, 2523, 9785522691849921, 16965
  ]
def negativeCoefficients : Array ℕ := #[
    88590094456100311457800912896, 314221196431539631726358691840, 44054042954156637689316529668096, 1784095864128017580905094709248, 434471722243655986105958298288128, 1129145696188288726154805772288,
    67733782825436867051537825792, 1784076181304516980223844024320, 1772941399617698874385051418624, 1129145696188288726154805772288, 27361658996953930871832779423744, 1750337228244552451126204563456,
    44054118966771958600024266375168, 1784076181304516980223844024320, 67733782825436867051537825792, 1750337228244552451126204563456, 67733782825436867051537825792, 1784076181304516980223844024320,
    1784213961069021184992598818816, 314221196431539631726358691840, 14509151376094279455546695221248, 155127469353275678359948361728, 562172124097058173400733376839680, 1623163032989152829668727980032,
    143776678912792092138488725504, 562172124036919705368562533138432, 143776678912792092138488725504, 139993082099297563398002180096, 5289468345265351179200190480384, 139993082099297563398002180096,
    1623163032989152829668727980032, 5289468345265351179200190480384, 14509216086603971759317213773824, 139993082099297563398002180096, 139993082099297563398002180096, 155127469353275678359948361728,
    176805401118639516800778240, 2563678316220272993611284480, 4538005295378414264553308160, 147337834265532930667315200, 2828886417898232268812451840, 147337834265532930667315200,
    4508537728525307678419845120, 4714810696497053781354086400, 2828886417898232268812451840, 72225006356964242613117911040, 4626407995937734022953697280, 2563678316220272993611284480,
    4508537728525307678419845120, 147337834265532930667315200, 4626407995937734022953697280, 147337834265532930667315200, 4508537728525307678419845120, 4714810696497053781354086400,
    176805401118639516800778240, 39080876996736048720242540544, 1562446211306266813596331671552, 1562445829472499545863895384064, 39080876996736048720242540544, 12068717323187662905903893446656,
    1840589560363272918490152960, 95316245090240918993240064, 44070076348640837170819095330816, 2563678316220272993611284480
  ]
def negativeScales : Array ℕ := #[
    33, 48, 55, 37, 57, 35,
    32, 37, 38, 35, 42, 38,
    50, 37, 32, 38, 32, 37,
    37, 48, 54, 34, 56, 38,
    33, 59, 33, 34, 39, 34,
    38, 39, 53, 34, 34, 34,
    9, 14, 13, 9, 9, 9,
    14, 9, 9, 18, 14, 14,
    14, 9, 14, 9, 14, 9,
    9, 33, 37, 38, 33, 50,
    11, 11, 53, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33161132052263290, 48987695275016067, 55119045366607630, 37493035983732633, 57420961318138546, 35833074500151989,
    32773862227482370, 37493020067284943, 38483987698775227, 35833074500151989, 42431926648125250, 38465475751904655,
    50119047855889457, 37493020067284943, 32773862227482370, 38465475751904655, 32773862227482370, 37493020067284943,
    37493131478731408, 48987695275016067, 54516734081774574, 34969368941813935, 56792710954875164, 38356650760291283,
    33859744438319124, 59792710954720831, 33859744438319124, 34821270289411344, 39060965568167172, 34821270289411344,
    38356650760291283, 39060965568167172, 53516740516149736, 34821270289411344, 34821270289411344, 34969368941813935,
    9192292814470767, 14050273809598340, 13874116857170113, 9929258415949272, 9192292814470767, 9929258415949272,
    14864718158730226, 9929258415949272, 9192292814470767, 18866485084981325, 14901951067164140, 14050273809598340,
    14864718158730226, 9929258415949272, 14901951067164140, 9929258415949272, 14864718158730226, 9929258415949272,
    9192292814470767, 33980449516674841, 37301649371104442, 38301649018535665, 33980449516674841, 50251043294501751,
    11572226512796267, 11300924490976301, 53119570337504343, 14050273809598340
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
noncomputable def negativeCeiling : ℝ := 1229709475983 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 88590094456100311457800912896, coefficient := (-88590094456100311457800912896) }, { argument := 314221196431539631726358691840, coefficient := (-314221196431539631726358691840) }, { argument := 44054042954156637689316529668096, coefficient := (-44054042954156637689316529668096) }, { argument := 1784095864128017580905094709248, coefficient := (-1784095864128017580905094709248) }, { argument := 434471722243655986105958298288128, coefficient := (-434471722243655986105958298288128) }, { argument := 1129145696188288726154805772288, coefficient := (-1129145696188288726154805772288) }, { argument := 67733782825436867051537825792, coefficient := (-67733782825436867051537825792) }, { argument := 1784076181304516980223844024320, coefficient := (-1784076181304516980223844024320) }, { argument := 1772941399617698874385051418624, coefficient := (-1772941399617698874385051418624) }, { argument := 1129145696188288726154805772288, coefficient := (-1129145696188288726154805772288) }, { argument := 27361658996953930871832779423744, coefficient := (-27361658996953930871832779423744) }, { argument := 1750337228244552451126204563456, coefficient := (-1750337228244552451126204563456) }, { argument := 44054118966771958600024266375168, coefficient := (-44054118966771958600024266375168) }, { argument := 1784076181304516980223844024320, coefficient := (-1784076181304516980223844024320) }, { argument := 67733782825436867051537825792, coefficient := (-67733782825436867051537825792) }, { argument := 1750337228244552451126204563456, coefficient := (-1750337228244552451126204563456) }, { argument := 67733782825436867051537825792, coefficient := (-67733782825436867051537825792) }, { argument := 1784076181304516980223844024320, coefficient := (-1784076181304516980223844024320) }, { argument := 1784213961069021184992598818816, coefficient := (-1784213961069021184992598818816) }, { argument := 314221196431539631726358691840, coefficient := (-314221196431539631726358691840) }, { argument := 14509151376094279455546695221248, coefficient := (-14509151376094279455546695221248) }, { argument := 155127469353275678359948361728, coefficient := (-155127469353275678359948361728) }, { argument := 562172124097058173400733376839680, coefficient := (-562172124097058173400733376839680) }, { argument := 1623163032989152829668727980032, coefficient := (-1623163032989152829668727980032) }, { argument := 143776678912792092138488725504, coefficient := (-143776678912792092138488725504) }, { argument := 562172124036919705368562533138432, coefficient := (-562172124036919705368562533138432) }, { argument := 143776678912792092138488725504, coefficient := (-143776678912792092138488725504) }, { argument := 139993082099297563398002180096, coefficient := (-139993082099297563398002180096) }, { argument := 5289468345265351179200190480384, coefficient := (-5289468345265351179200190480384) }, { argument := 139993082099297563398002180096, coefficient := (-139993082099297563398002180096) }, { argument := 1623163032989152829668727980032, coefficient := (-1623163032989152829668727980032) }, { argument := 5289468345265351179200190480384, coefficient := (-5289468345265351179200190480384) }, { argument := 14509216086603971759317213773824, coefficient := (-14509216086603971759317213773824) }, { argument := 139993082099297563398002180096, coefficient := (-139993082099297563398002180096) }, { argument := 139993082099297563398002180096, coefficient := (-139993082099297563398002180096) }, { argument := 155127469353275678359948361728, coefficient := (-155127469353275678359948361728) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 2563678316220272993611284480, coefficient := (-2563678316220272993611284480) }, { argument := 4538005295378414264553308160, coefficient := (-4538005295378414264553308160) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 2828886417898232268812451840, coefficient := (-2828886417898232268812451840) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 4508537728525307678419845120, coefficient := (-4508537728525307678419845120) }, { argument := 4714810696497053781354086400, coefficient := (-4714810696497053781354086400) }, { argument := 2828886417898232268812451840, coefficient := (-2828886417898232268812451840) }, { argument := 72225006356964242613117911040, coefficient := (-72225006356964242613117911040) }, { argument := 4626407995937734022953697280, coefficient := (-4626407995937734022953697280) }, { argument := 2563678316220272993611284480, coefficient := (-2563678316220272993611284480) }, { argument := 4508537728525307678419845120, coefficient := (-4508537728525307678419845120) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 4626407995937734022953697280, coefficient := (-4626407995937734022953697280) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 4508537728525307678419845120, coefficient := (-4508537728525307678419845120) }, { argument := 4714810696497053781354086400, coefficient := (-4714810696497053781354086400) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 39080876996736048720242540544, coefficient := (-39080876996736048720242540544) }, { argument := 1562446211306266813596331671552, coefficient := (-1562446211306266813596331671552) }, { argument := 1562445829472499545863895384064, coefficient := (-1562445829472499545863895384064) }, { argument := 39080876996736048720242540544, coefficient := (-39080876996736048720242540544) }, { argument := 12068717323187662905903893446656, coefficient := (-12068717323187662905903893446656) }, { argument := 1840589560363272918490152960, coefficient := (-1840589560363272918490152960) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 44070076348640837170819095330816, coefficient := (-44070076348640837170819095330816) }, { argument := 2563678316220272993611284480, coefficient := (-2563678316220272993611284480) }] }

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
def constantNumerator : ℤ := (-105301137831156650681252767273582592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2679566438196849, 67947, 67947, 48633, 2523, 750638567,
    7502597659, 15005191651, 750638567, 53891030103, 2695, 2233,
    193432061181, 15015, 13476671403, 60137, 60137, 43043,
    2233, 505642105641815, 505642152944809, 152526270695013, 2678592182100675, 13476671403,
    105714694870664137, 4264748381, 511748015, 13476642731, 26783151985, 4264748381,
    413346576499, 26441910183, 5357193696048483, 13476642731, 511748015, 26441910183,
    511748015, 13476642731, 13476843435, 152526270695013, 3221678778768129, 67275799273,
    998618297549333319, 703934582637, 31176589907, 15603410897538167, 31176589907, 60712306661,
    1146970333947, 60712306661, 703934582637, 1146970333947, 25773545179080433, 60712306661,
    60712306661, 67275799273, 52882940701211977, 175, 145, 24127609199522187,
    975, 52878286520579679, 3905, 3905
  ]
def negativeCoefficients : Array ℕ := #[
    12067694412577816356061502767104, 2566965083292350266680016896, 2566965083292350266680016896, 1837302793291195645421420544, 95316245090240918993240064, 3461709384326270049811693568,
    138398498903585405400141266944, 138398465081480146253678379008, 3461709384326270049811693568, 497057020089309148508244148224, 3258055083861425625833144320, 168720709699966684194930688,
    1784095864128017580905094709248, 4538005295378414264553308160, 497201416673242476782599274496, 4543823250885309667456581632, 4543823250885309667456581632, 3252237128354530222929870848,
    168720709699966684194930688, 142325599909456937948429680640, 142325613224066072442730184704, 85864656983283993843446317056, 12063306753186123695547796684800, 497201416673242476782599274496,
    119024165106777173056569619775488, 314682887692296619674287734784, 18880169325867753452056084480, 497200358863150313982071406592, 494061950154560963677530357760, 314682887692296619674287734784,
    7624898510421060071749933072384, 487767149965815495459474505728, 12063327766637759124163509878784, 497200358863150313982071406592, 18880169325867753452056084480, 487767149965815495459474505728,
    18880169325867753452056084480, 497200358863150313982071406592, 497207763533795453585766481920, 85864656983283993843446317056, 14509151347567580384706359721984, 155127431442910763877606096896,
    562172124091067079289488726294528, 1623162636317285797646171111424, 143776643776356317740220284928, 562172124030893003546864077766656, 143776643776356317740220284928, 139993047887504835694425014272,
    5289467052614371900021788377088, 139993047887504835694425014272, 1623162636317285797646171111424, 5289467052614371900021788377088, 14509216058065410207058384388096, 139993047887504835694425014272,
    139993047887504835694425014272, 155127431442910763877606096896, 119081796018117148031584405815296, 105781009216280052786790400, 5477945120128788447887360, 434644367201236290597641684779008,
    147337834265532930667315200, 119071315735036481905454210875392, 147526728924847716475863040, 147526728924847716475863040
  ]
def negativeScales : Array ℕ := #[
    51, 16, 16, 15, 11, 29,
    32, 33, 29, 35, 11, 11,
    37, 13, 33, 15, 15, 15,
    11, 48, 48, 47, 51, 33,
    56, 31, 28, 33, 34, 31,
    38, 34, 52, 33, 28, 34,
    28, 33, 33, 47, 51, 35,
    59, 39, 34, 53, 34, 35,
    40, 35, 39, 40, 54, 35,
    35, 35, 55, 7, 7, 54,
    9, 55, 11, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    51250921010536667, 16052122233990708, 16052122233990708, 15569647968694305, 11300924490976301, 29483543175343454,
    32804743047759886, 33804742695191104, 29483543175343454, 35649326112357917, 11396069557639874, 11124767535822474,
    37493035983732633, 13874116857170113, 33649745158813920, 15875965281657251, 15875965281657251, 15393491013538097,
    11124767535822474, 48845109934083774, 48845110069048393, 47116051078228316, 51250396369683867, 33649745158813920,
    56552953545564044, 31989813499532049, 28930858367860654, 33649742089436104, 34640606703635472, 31989813499532049,
    38588560981632235, 34622107350842923, 52250398882757328, 33649742089436104, 28930858367860654, 34622107350842923,
    28930858367860654, 33649742089436104, 33649763574943683, 47116051078228316, 51516734078938066, 35969368589245074,
    59792710954859789, 39356650407722506, 34859744085750333, 53792710954705365, 34859744085750333, 35821269936842560,
    40060965215598395, 35821269936842560, 39356650407722506, 40060965215598395, 54516740513312061, 35821269936842560,
    35821269936842560, 35969368589245074, 55553651922297046, 7451211111832378, 7179909090014935, 54421534484440348,
    9929258415949272, 55553524946400517, 11931106840579056, 11931106840579056
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
noncomputable def negativeCeiling : ℝ := 337194330481 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12067694412577816356061502767104, coefficient := (-12067694412577816356061502767104) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 1837302793291195645421420544, coefficient := (-1837302793291195645421420544) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 3461709384326270049811693568, coefficient := (-3461709384326270049811693568) }, { argument := 138398498903585405400141266944, coefficient := (-138398498903585405400141266944) }, { argument := 138398465081480146253678379008, coefficient := (-138398465081480146253678379008) }, { argument := 3461709384326270049811693568, coefficient := (-3461709384326270049811693568) }, { argument := 497057020089309148508244148224, coefficient := (-497057020089309148508244148224) }, { argument := 3258055083861425625833144320, coefficient := (-3258055083861425625833144320) }, { argument := 168720709699966684194930688, coefficient := (-168720709699966684194930688) }, { argument := 1784095864128017580905094709248, coefficient := (-1784095864128017580905094709248) }, { argument := 4538005295378414264553308160, coefficient := (-4538005295378414264553308160) }, { argument := 497201416673242476782599274496, coefficient := (-497201416673242476782599274496) }, { argument := 4543823250885309667456581632, coefficient := (-4543823250885309667456581632) }, { argument := 4543823250885309667456581632, coefficient := (-4543823250885309667456581632) }, { argument := 3252237128354530222929870848, coefficient := (-3252237128354530222929870848) }, { argument := 168720709699966684194930688, coefficient := (-168720709699966684194930688) }, { argument := 142325599909456937948429680640, coefficient := (-142325599909456937948429680640) }, { argument := 142325613224066072442730184704, coefficient := (-142325613224066072442730184704) }, { argument := 85864656983283993843446317056, coefficient := (-85864656983283993843446317056) }, { argument := 12063306753186123695547796684800, coefficient := (-12063306753186123695547796684800) }, { argument := 497201416673242476782599274496, coefficient := (-497201416673242476782599274496) }, { argument := 119024165106777173056569619775488, coefficient := (-119024165106777173056569619775488) }, { argument := 314682887692296619674287734784, coefficient := (-314682887692296619674287734784) }, { argument := 18880169325867753452056084480, coefficient := (-18880169325867753452056084480) }, { argument := 497200358863150313982071406592, coefficient := (-497200358863150313982071406592) }, { argument := 494061950154560963677530357760, coefficient := (-494061950154560963677530357760) }, { argument := 314682887692296619674287734784, coefficient := (-314682887692296619674287734784) }, { argument := 7624898510421060071749933072384, coefficient := (-7624898510421060071749933072384) }, { argument := 487767149965815495459474505728, coefficient := (-487767149965815495459474505728) }, { argument := 12063327766637759124163509878784, coefficient := (-12063327766637759124163509878784) }, { argument := 497200358863150313982071406592, coefficient := (-497200358863150313982071406592) }, { argument := 18880169325867753452056084480, coefficient := (-18880169325867753452056084480) }, { argument := 487767149965815495459474505728, coefficient := (-487767149965815495459474505728) }, { argument := 18880169325867753452056084480, coefficient := (-18880169325867753452056084480) }, { argument := 497200358863150313982071406592, coefficient := (-497200358863150313982071406592) }, { argument := 497207763533795453585766481920, coefficient := (-497207763533795453585766481920) }, { argument := 85864656983283993843446317056, coefficient := (-85864656983283993843446317056) }, { argument := 14509151347567580384706359721984, coefficient := (-14509151347567580384706359721984) }, { argument := 155127431442910763877606096896, coefficient := (-155127431442910763877606096896) }, { argument := 562172124091067079289488726294528, coefficient := (-562172124091067079289488726294528) }, { argument := 1623162636317285797646171111424, coefficient := (-1623162636317285797646171111424) }, { argument := 143776643776356317740220284928, coefficient := (-143776643776356317740220284928) }, { argument := 562172124030893003546864077766656, coefficient := (-562172124030893003546864077766656) }, { argument := 143776643776356317740220284928, coefficient := (-143776643776356317740220284928) }, { argument := 139993047887504835694425014272, coefficient := (-139993047887504835694425014272) }, { argument := 5289467052614371900021788377088, coefficient := (-5289467052614371900021788377088) }, { argument := 139993047887504835694425014272, coefficient := (-139993047887504835694425014272) }, { argument := 1623162636317285797646171111424, coefficient := (-1623162636317285797646171111424) }, { argument := 5289467052614371900021788377088, coefficient := (-5289467052614371900021788377088) }, { argument := 14509216058065410207058384388096, coefficient := (-14509216058065410207058384388096) }, { argument := 139993047887504835694425014272, coefficient := (-139993047887504835694425014272) }, { argument := 139993047887504835694425014272, coefficient := (-139993047887504835694425014272) }, { argument := 155127431442910763877606096896, coefficient := (-155127431442910763877606096896) }, { argument := 119081796018117148031584405815296, coefficient := (-119081796018117148031584405815296) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 434644367201236290597641684779008, coefficient := (-434644367201236290597641684779008) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 119071315735036481905454210875392, coefficient := (-119071315735036481905454210875392) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
