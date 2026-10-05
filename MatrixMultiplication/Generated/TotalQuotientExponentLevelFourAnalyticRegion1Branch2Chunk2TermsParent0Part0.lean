import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-124299948325889190287366015680512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    242365, 8437059, 35, 31, 1451, 395,
    4218531, 1451, 35, 35, 15, 35,
    395, 15, 121181, 31, 517165145, 18800776825,
    11553725385, 9099468075, 11855783565, 377572725, 11553725385, 6569765415,
    11855783565, 185086149795, 226543635, 9400390975, 11553725385, 377572725,
    226543635, 377572725, 5814619965, 6569765415, 517165145, 1833841121,
    54566295, 1572182899, 1350225555, 42956445, 1572183333, 22058715,
    22058715, 746513355, 40634475, 1350225555, 746513355, 1833840687,
    42956445, 40634475, 54566295, 31820135, 3336283765, 35961804375,
    1668143155, 31820135, 154966945, 2711728355, 2711729685, 154965615,
    1945295681, 154966945, 50568161, 7517295911
  ]
def negativeCoefficients : Array ℕ := #[
    1144536352620701562217431040, 39842884635593685977020760064, 676998458984192337835458560, 599627206528856070654263296, 28066421828173230919978582016, 7640411179964456384143032320,
    39842898802693134585956401152, 28066421828173230919978582016, 676998458984192337835458560, 676998458984192337835458560, 580284393415022003858964480, 676998458984192337835458560,
    7640411179964456384143032320, 580284393415022003858964480, 1144522185521252953281789952, 599627206528856070654263296, 596250817103618184335851520, 21675819904856539362702131200,
    13320538454688522351421685760, 83927779393207755876178329600, 13668787826052928164530749440, 435311714205507266386329600, 13320538454688522351421685760, 7574423827175826435122135040,
    13668787826052928164530749440, 213389802303539661982578769920, 8357984912745739514617528320, 21675825813579250472792883200, 13320538454688522351421685760, 435311714205507266386329600,
    8357984912745739514617528320, 435311714205507266386329600, 13407600797529623804698951680, 7574423827175826435122135040, 596250817103618184335851520, 8457099457732907690973200384,
    8052563831324297102371061760, 14500827787457876271816507392, 199258122038939521916117975040, 6339252377851042399738920960, 14500831790401340266789208064, 6510583523198367870002135040,
    6510583523198367870002135040, 110165926458330277379246653440, 5996590087156391459212492800, 199258122038939521916117975040, 110165926458330277379246653440, 8457097456261175693486850048,
    6339252377851042399738920960, 5996590087156391459212492800, 8052563831324297102371061760, 73372235841985985401323520, 7692946596278392547736289280, 82922275216804184472944640000,
    7692952464648850996587397120, 73372235841985985401323520, 5717271148599248062502666240, 200090235848425604605773086720, 200090333985104076740587683840, 5717222080260011995095367680,
    8971092893774884101762842624, 5717271148599248062502666240, 233204481061285118338924544, 34667408449140073741150060544
  ]
def negativeScales : Array ℕ := #[
    17, 23, 5, 4, 10, 8,
    22, 10, 5, 5, 3, 5,
    8, 3, 16, 4, 28, 34,
    33, 33, 33, 28, 33, 32,
    33, 37, 27, 33, 33, 28,
    27, 28, 32, 32, 28, 30,
    25, 30, 30, 25, 30, 24,
    24, 29, 25, 30, 29, 30,
    25, 25, 25, 24, 31, 35,
    30, 24, 27, 31, 31, 27,
    30, 27, 25, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17886821851721764, 23008308759543553, 5129283016944967, 4954196321574415, 10502831804067043, 8625708843075807,
    22008309272528510, 10502831804067043, 5129283016944967, 5129283016944967, 3906890600547867, 5129283016944967,
    8625708843075807, 3906890600547867, 16886803993895011, 4954196321574415, 28946049815013747, 34130073222394696,
    33427639058340018, 33083135066551531, 33464871964539053, 28492179310534916, 33427639058340018, 32613194711504187,
    33464871964539053, 37429405984514207, 27755213716620416, 33130073615666269, 33427639058340018, 28492179310534916,
    27755213716620416, 28492179310534916, 32437037756342276, 32613194711504187, 28946049815013747, 30772221507527126,
    25701506753689064, 30550121916451324, 30330553283409649, 25356371267565381, 30550122314706236, 24394845415380021,
    24394845415380021, 29475592829264495, 25276200918881397, 30330553283409649, 29475592829264495, 30772221166096388,
    25356371267565381, 25276200918881397, 25701506753689064, 24923436627275891, 31635594855297861, 35065746358423336,
    30635595955820999, 24923436627275891, 27207385275435475, 31336565518993377, 31336566226580451, 27207372893487580,
    30857342314577970, 27207385275435475, 25591725977495892, 32807566649971723
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
noncomputable def negativeCeiling : ℝ := 21695991 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1144536352620701562217431040, coefficient := (-1144536352620701562217431040) }, { argument := 39842884635593685977020760064, coefficient := (-39842884635593685977020760064) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 599627206528856070654263296, coefficient := (-599627206528856070654263296) }, { argument := 28066421828173230919978582016, coefficient := (-28066421828173230919978582016) }, { argument := 7640411179964456384143032320, coefficient := (-7640411179964456384143032320) }, { argument := 39842898802693134585956401152, coefficient := (-39842898802693134585956401152) }, { argument := 28066421828173230919978582016, coefficient := (-28066421828173230919978582016) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 7640411179964456384143032320, coefficient := (-7640411179964456384143032320) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 1144522185521252953281789952, coefficient := (-1144522185521252953281789952) }, { argument := 599627206528856070654263296, coefficient := (-599627206528856070654263296) }, { argument := 596250817103618184335851520, coefficient := (-596250817103618184335851520) }, { argument := 21675819904856539362702131200, coefficient := (-21675819904856539362702131200) }, { argument := 13320538454688522351421685760, coefficient := (-13320538454688522351421685760) }, { argument := 83927779393207755876178329600, coefficient := (-83927779393207755876178329600) }, { argument := 13668787826052928164530749440, coefficient := (-13668787826052928164530749440) }, { argument := 435311714205507266386329600, coefficient := (-435311714205507266386329600) }, { argument := 13320538454688522351421685760, coefficient := (-13320538454688522351421685760) }, { argument := 7574423827175826435122135040, coefficient := (-7574423827175826435122135040) }, { argument := 13668787826052928164530749440, coefficient := (-13668787826052928164530749440) }, { argument := 213389802303539661982578769920, coefficient := (-213389802303539661982578769920) }, { argument := 8357984912745739514617528320, coefficient := (-8357984912745739514617528320) }, { argument := 21675825813579250472792883200, coefficient := (-21675825813579250472792883200) }, { argument := 13320538454688522351421685760, coefficient := (-13320538454688522351421685760) }, { argument := 435311714205507266386329600, coefficient := (-435311714205507266386329600) }, { argument := 8357984912745739514617528320, coefficient := (-8357984912745739514617528320) }, { argument := 435311714205507266386329600, coefficient := (-435311714205507266386329600) }, { argument := 13407600797529623804698951680, coefficient := (-13407600797529623804698951680) }, { argument := 7574423827175826435122135040, coefficient := (-7574423827175826435122135040) }, { argument := 596250817103618184335851520, coefficient := (-596250817103618184335851520) }, { argument := 8457099457732907690973200384, coefficient := (-8457099457732907690973200384) }, { argument := 8052563831324297102371061760, coefficient := (-8052563831324297102371061760) }, { argument := 14500827787457876271816507392, coefficient := (-14500827787457876271816507392) }, { argument := 199258122038939521916117975040, coefficient := (-199258122038939521916117975040) }, { argument := 6339252377851042399738920960, coefficient := (-6339252377851042399738920960) }, { argument := 14500831790401340266789208064, coefficient := (-14500831790401340266789208064) }, { argument := 6510583523198367870002135040, coefficient := (-6510583523198367870002135040) }, { argument := 6510583523198367870002135040, coefficient := (-6510583523198367870002135040) }, { argument := 110165926458330277379246653440, coefficient := (-110165926458330277379246653440) }, { argument := 5996590087156391459212492800, coefficient := (-5996590087156391459212492800) }, { argument := 199258122038939521916117975040, coefficient := (-199258122038939521916117975040) }, { argument := 110165926458330277379246653440, coefficient := (-110165926458330277379246653440) }, { argument := 8457097456261175693486850048, coefficient := (-8457097456261175693486850048) }, { argument := 6339252377851042399738920960, coefficient := (-6339252377851042399738920960) }, { argument := 5996590087156391459212492800, coefficient := (-5996590087156391459212492800) }, { argument := 8052563831324297102371061760, coefficient := (-8052563831324297102371061760) }, { argument := 73372235841985985401323520, coefficient := (-73372235841985985401323520) }, { argument := 7692946596278392547736289280, coefficient := (-7692946596278392547736289280) }, { argument := 82922275216804184472944640000, coefficient := (-82922275216804184472944640000) }, { argument := 7692952464648850996587397120, coefficient := (-7692952464648850996587397120) }, { argument := 73372235841985985401323520, coefficient := (-73372235841985985401323520) }, { argument := 5717271148599248062502666240, coefficient := (-5717271148599248062502666240) }, { argument := 200090235848425604605773086720, coefficient := (-200090235848425604605773086720) }, { argument := 200090333985104076740587683840, coefficient := (-200090333985104076740587683840) }, { argument := 5717222080260011995095367680, coefficient := (-5717222080260011995095367680) }, { argument := 8971092893774884101762842624, coefficient := (-8971092893774884101762842624) }, { argument := 5717271148599248062502666240, coefficient := (-5717271148599248062502666240) }, { argument := 233204481061285118338924544, coefficient := (-233204481061285118338924544) }, { argument := 34667408449140073741150060544, coefficient := (-34667408449140073741150060544) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-290494592664506843661066798366720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    510575303, 1945295069, 1022781837, 458375911, 154966945, 50568161,
    50568161, 884879779, 884880213, 50567727, 927627015, 25372956909,
    7421013723, 517165145, 31820135, 516960269, 16066355, 516960269,
    18795313465, 11548501047, 36397786935, 11850422643, 377401995, 11548501047,
    6566794713, 11850422643, 185002457949, 226441197, 9397659295, 11548501047,
    377401995, 226441197, 377401995, 5811990723, 6566794713, 516960269,
    7136225219, 1492526877, 20532788167, 36932101233, 1174967967, 20532797085,
    603361929, 603361929, 20419037913, 1111456185, 36932101233, 20419037913,
    7136216301, 1174967967, 1111456185, 1492526877, 100946209, 2711728355,
    884879779, 165437273303, 8934431317, 12921112865, 17897407143, 8021007029,
    2711728355, 884879779, 510575303, 8934431317
  ]
def negativeCoefficients : Array ℕ := #[
    4709225972398854325166669824, 8971090071423040824201445376, 4716748697594379651564699648, 4227771559885233435692761088, 5717271148599248062502666240, 233204481061285118338924544,
    233204481061285118338924544, 8161575409606833872077586432, 8161579412550297867050287104, 233202479589553120852574208, 8555849070782065671269253120, 29253027655848973308404957184,
    8555846307229219128657051648, 596250817103618184335851520, 73372235841985985401323520, 596014611157440351954796544, 74092984720590955788369920, 596014611157440351954796544,
    21669521079625130499207331840, 13314515203060987625704783872, 83927582554919274349194117120, 13662607103794608217226477568, 435114875917025739402117120, 13314515203060987625704783872,
    7570998840956247865596837888, 13662607103794608217226477568, 213293312174526017454917812224, 8354205617606894196520648704, 21669526988347841609298083840, 13314515203060987625704783872,
    435114875917025739402117120, 8354205617606894196520648704, 435114875917025739402117120, 13401538178244392773585207296, 7570998840956247865596837888, 596014611157440351954796544,
    32910030066811224280820350976, 27532261323151974878498783232, 189381544218170428607940263936, 681277019549483974121150742528, 21674333382055810010733084672, 189381626472202253278830919680,
    22260126176165426497509654528, 22260126176165426497509654528, 376664766612483400997334417408, 20502747793836577037179944960, 681277019549483974121150742528, 376664766612483400997334417408,
    32909988939795311945375023104, 21674333382055810010733084672, 20502747793836577037179944960, 27532261323151974878498783232, 14897031061073566421800189952, 200090235848425604605773086720,
    8161575409606833872077586432, 190736190054548916733611081728, 164811167948834774320018358272, 14897028885510687228679946240, 165074444574951123799762796544, 147961463877388407616374308864,
    200090235848425604605773086720, 8161575409606833872077586432, 4709225972398854325166669824, 164811167948834774320018358272
  ]
def negativeScales : Array ℕ := #[
    28, 30, 29, 28, 27, 25,
    25, 29, 29, 25, 29, 34,
    32, 28, 24, 28, 23, 28,
    34, 33, 35, 33, 28, 33,
    32, 33, 37, 27, 33, 33,
    28, 27, 28, 32, 32, 28,
    32, 30, 34, 35, 30, 34,
    29, 29, 34, 30, 35, 34,
    32, 30, 30, 30, 26, 31,
    29, 37, 33, 33, 34, 32,
    31, 29, 28, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28927548521136028, 30857341860698621, 29929851307294249, 28771955987686142, 27207385275435475, 25591725977495892,
    25591725977495892, 29720906221166773, 29720906928753850, 25591713595547996, 29788969595379464, 34562572606604990,
    32788969129386593, 28946049815013747, 24923436627275891, 28945478175176391, 23937539332217928, 28945478175176391,
    34129653925474550, 33426986556151521, 35083131682952468, 33464219462350555, 28491526808346416, 33426986556151521,
    32612542209315549, 33464219462350555, 37428753482325710, 27754561214428378, 33129654318860438, 33426986556151521,
    28491526808346416, 27754561214428378, 28491526808346416, 32436385254153779, 32612542209315549, 28945478175176391,
    32732514001517022, 30475109765352829, 34257210494565821, 35104156295148294, 30129974279304026, 34257211121171009,
    29168448427118662, 29168448427118662, 34249195841003024, 30049803930620043, 35104156295148294, 34249195841003024,
    32732512198608333, 30129974279304026, 30049803930620043, 30475109765352829, 26589011490875994, 31336565518993377,
    29720906221166773, 37267493356572787, 33056728757595047, 33589011280184750, 34059031543464467, 32901136235340787,
    31336565518993377, 29720906221166773, 28927548521136028, 33056728757595047
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
noncomputable def negativeCeiling : ℝ := 15007603 / 8000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4709225972398854325166669824, coefficient := (-4709225972398854325166669824) }, { argument := 8971090071423040824201445376, coefficient := (-8971090071423040824201445376) }, { argument := 4716748697594379651564699648, coefficient := (-4716748697594379651564699648) }, { argument := 4227771559885233435692761088, coefficient := (-4227771559885233435692761088) }, { argument := 5717271148599248062502666240, coefficient := (-5717271148599248062502666240) }, { argument := 233204481061285118338924544, coefficient := (-233204481061285118338924544) }, { argument := 233204481061285118338924544, coefficient := (-233204481061285118338924544) }, { argument := 8161575409606833872077586432, coefficient := (-8161575409606833872077586432) }, { argument := 8161579412550297867050287104, coefficient := (-8161579412550297867050287104) }, { argument := 233202479589553120852574208, coefficient := (-233202479589553120852574208) }, { argument := 8555849070782065671269253120, coefficient := (-8555849070782065671269253120) }, { argument := 29253027655848973308404957184, coefficient := (-29253027655848973308404957184) }, { argument := 8555846307229219128657051648, coefficient := (-8555846307229219128657051648) }, { argument := 596250817103618184335851520, coefficient := (-596250817103618184335851520) }, { argument := 73372235841985985401323520, coefficient := (-73372235841985985401323520) }, { argument := 596014611157440351954796544, coefficient := (-596014611157440351954796544) }, { argument := 74092984720590955788369920, coefficient := (-74092984720590955788369920) }, { argument := 596014611157440351954796544, coefficient := (-596014611157440351954796544) }, { argument := 21669521079625130499207331840, coefficient := (-21669521079625130499207331840) }, { argument := 13314515203060987625704783872, coefficient := (-13314515203060987625704783872) }, { argument := 83927582554919274349194117120, coefficient := (-83927582554919274349194117120) }, { argument := 13662607103794608217226477568, coefficient := (-13662607103794608217226477568) }, { argument := 435114875917025739402117120, coefficient := (-435114875917025739402117120) }, { argument := 13314515203060987625704783872, coefficient := (-13314515203060987625704783872) }, { argument := 7570998840956247865596837888, coefficient := (-7570998840956247865596837888) }, { argument := 13662607103794608217226477568, coefficient := (-13662607103794608217226477568) }, { argument := 213293312174526017454917812224, coefficient := (-213293312174526017454917812224) }, { argument := 8354205617606894196520648704, coefficient := (-8354205617606894196520648704) }, { argument := 21669526988347841609298083840, coefficient := (-21669526988347841609298083840) }, { argument := 13314515203060987625704783872, coefficient := (-13314515203060987625704783872) }, { argument := 435114875917025739402117120, coefficient := (-435114875917025739402117120) }, { argument := 8354205617606894196520648704, coefficient := (-8354205617606894196520648704) }, { argument := 435114875917025739402117120, coefficient := (-435114875917025739402117120) }, { argument := 13401538178244392773585207296, coefficient := (-13401538178244392773585207296) }, { argument := 7570998840956247865596837888, coefficient := (-7570998840956247865596837888) }, { argument := 596014611157440351954796544, coefficient := (-596014611157440351954796544) }, { argument := 32910030066811224280820350976, coefficient := (-32910030066811224280820350976) }, { argument := 27532261323151974878498783232, coefficient := (-27532261323151974878498783232) }, { argument := 189381544218170428607940263936, coefficient := (-189381544218170428607940263936) }, { argument := 681277019549483974121150742528, coefficient := (-681277019549483974121150742528) }, { argument := 21674333382055810010733084672, coefficient := (-21674333382055810010733084672) }, { argument := 189381626472202253278830919680, coefficient := (-189381626472202253278830919680) }, { argument := 22260126176165426497509654528, coefficient := (-22260126176165426497509654528) }, { argument := 22260126176165426497509654528, coefficient := (-22260126176165426497509654528) }, { argument := 376664766612483400997334417408, coefficient := (-376664766612483400997334417408) }, { argument := 20502747793836577037179944960, coefficient := (-20502747793836577037179944960) }, { argument := 681277019549483974121150742528, coefficient := (-681277019549483974121150742528) }, { argument := 376664766612483400997334417408, coefficient := (-376664766612483400997334417408) }, { argument := 32909988939795311945375023104, coefficient := (-32909988939795311945375023104) }, { argument := 21674333382055810010733084672, coefficient := (-21674333382055810010733084672) }, { argument := 20502747793836577037179944960, coefficient := (-20502747793836577037179944960) }, { argument := 27532261323151974878498783232, coefficient := (-27532261323151974878498783232) }, { argument := 14897031061073566421800189952, coefficient := (-14897031061073566421800189952) }, { argument := 200090235848425604605773086720, coefficient := (-200090235848425604605773086720) }, { argument := 8161575409606833872077586432, coefficient := (-8161575409606833872077586432) }, { argument := 190736190054548916733611081728, coefficient := (-190736190054548916733611081728) }, { argument := 164811167948834774320018358272, coefficient := (-164811167948834774320018358272) }, { argument := 14897028885510687228679946240, coefficient := (-14897028885510687228679946240) }, { argument := 165074444574951123799762796544, coefficient := (-165074444574951123799762796544) }, { argument := 147961463877388407616374308864, coefficient := (-147961463877388407616374308864) }, { argument := 200090235848425604605773086720, coefficient := (-200090235848425604605773086720) }, { argument := 8161575409606833872077586432, coefficient := (-8161575409606833872077586432) }, { argument := 4709225972398854325166669824, coefficient := (-4709225972398854325166669824) }, { argument := 164811167948834774320018358272, coefficient := (-164811167948834774320018358272) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2
