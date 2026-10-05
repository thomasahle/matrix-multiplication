import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-260426859966103355815652084416512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8934435699, 510570921, 22953834435, 627845720961, 183630616167, 18800776825,
    3336283765, 18795313465, 1684528345, 730259565, 19974455439, 5842074633,
    11553725385, 11548501047, 242365, 1833840545, 436530219, 1572182677,
    10801800951, 343651449, 1572183111, 176469663, 176469663, 5972104911,
    325075695, 10801800951, 5972104911, 1833840111, 343651449, 325075695,
    436530219, 807569889, 2711729685, 884880213, 165437344647, 8934435699,
    12921116337, 17897415921, 8021010963, 2711729685, 884880213, 9099468075,
    35961804375, 36397786935, 18157531875, 374998155, 10257152793, 2999984271,
    11855783565, 11850422643, 8437059, 377572725, 377401995, 35,
    16066355, 1684528345, 18157531875, 842264815, 16066355, 1022781837,
    17897407143, 17897415921, 1022773059, 374998155
  ]
def negativeCoefficients : Array ℕ := #[
    164811248782467305315273539584, 4709185555582588827539079168, 211711754666373242035875348480, 723856833271326722503722663936, 211711686283140039289960660992, 21675819904856539362702131200,
    7692946596278392547736289280, 21669521079625130499207331840, 7768515816281127248598138880, 6735455651466732549722603520, 23028979218434298136403902464, 6735453475903853356602359808,
    13320538454688522351421685760, 13314515203060987625704783872, 1144536352620701562217431040, 8457096801401761076797767680, 8052561230333382709324283904, 14500825739869284090056278016,
    199258057678249448743492386816, 6339250330262450217978691584, 14500829742812748085028978688, 6510581420269543467113250816, 6510581420269543467113250816, 110165890874560959193521586176,
    5996588150248263719709573120, 199258057678249448743492386816, 110165890874560959193521586176, 8457094799930029079311417344, 6339250330262450217978691584, 5996588150248263719709573120,
    8052561230333382709324283904, 14897035064017030416772890624, 200090333985104076740587683840, 8161579412550297867050287104, 190736272308580741404501737472, 164811248782467305315273539584,
    14897032888454151223652646912, 165074525537710863310984839168, 147961536446879593589750366208, 200090333985104076740587683840, 8161579412550297867050287104, 83927779393207755876178329600,
    82922275216804184472944640000, 83927582554919274349194117120, 83736835877087133239869440000, 6917494993398265861877268480, 23651384062175765653604007936, 6917492759036389933807828992,
    13668787826052928164530749440, 13662607103794608217226477568, 39842884635593685977020760064, 435311714205507266386329600, 435114875917025739402117120, 676998458984192337835458560,
    74092984720590955788369920, 7768515816281127248598138880, 83736835877087133239869440000, 7768521742297660927791595520, 74092984720590955788369920, 4716748697594379651564699648,
    165074444574951123799762796544, 165074525537710863310984839168, 4716708216214509895953678336, 6917494993398265861877268480
  ]
def negativeScales : Array ℕ := #[
    33, 28, 34, 39, 37, 34,
    31, 34, 30, 29, 34, 32,
    33, 33, 17, 30, 28, 30,
    33, 28, 30, 27, 27, 32,
    28, 33, 32, 30, 28, 28,
    28, 29, 31, 29, 37, 33,
    33, 34, 32, 31, 29, 33,
    35, 35, 34, 28, 33, 31,
    33, 33, 23, 28, 28, 5,
    23, 30, 34, 29, 23, 29,
    34, 34, 29, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33056729465182121, 28927536139186609, 34418016124660002, 39191619136398634, 37418015658667136, 34130073222394696,
    31635594855297861, 34129653925474550, 30649697558422482, 29443834108815757, 34217437120554365, 32443833642822890,
    33427639058340018, 33426986556151521, 17886821851721764, 30772221054384010, 28701506287696197, 30550121712735636,
    33330552817416783, 28356370801572515, 30550122110990604, 27394844949387155, 27394844949387155, 32475592363271629,
    28276200452888531, 33330552817416783, 32475592363271629, 30772220712953165, 28356370801572515, 28276200452888531,
    28701506287696197, 29589011878538870, 31336566226580451, 29720906928753850, 37267493978727702, 33056729465182121,
    33589011667847683, 34059032251051542, 32901136942927919, 31336566226580451, 29720906928753850, 33083135066551531,
    35065746358423336, 35083131682952468, 34079849061541519, 28482308256630504, 33255911268369001, 31482307790637638,
    33464871964539053, 33464219462350555, 23008308759543553, 28492179310534916, 28491526808346416, 5129283016944967,
    23937539332217928, 30649697558422482, 34079849061541519, 29649698658945621, 23937539332217928, 29929851307294249,
    34059031543464467, 34059032251051542, 29929838925344772, 28482308256630504
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
noncomputable def negativeCeiling : ℝ := 172379423 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 164811248782467305315273539584, coefficient := (-164811248782467305315273539584) }, { argument := 4709185555582588827539079168, coefficient := (-4709185555582588827539079168) }, { argument := 211711754666373242035875348480, coefficient := (-211711754666373242035875348480) }, { argument := 723856833271326722503722663936, coefficient := (-723856833271326722503722663936) }, { argument := 211711686283140039289960660992, coefficient := (-211711686283140039289960660992) }, { argument := 21675819904856539362702131200, coefficient := (-21675819904856539362702131200) }, { argument := 7692946596278392547736289280, coefficient := (-7692946596278392547736289280) }, { argument := 21669521079625130499207331840, coefficient := (-21669521079625130499207331840) }, { argument := 7768515816281127248598138880, coefficient := (-7768515816281127248598138880) }, { argument := 6735455651466732549722603520, coefficient := (-6735455651466732549722603520) }, { argument := 23028979218434298136403902464, coefficient := (-23028979218434298136403902464) }, { argument := 6735453475903853356602359808, coefficient := (-6735453475903853356602359808) }, { argument := 13320538454688522351421685760, coefficient := (-13320538454688522351421685760) }, { argument := 13314515203060987625704783872, coefficient := (-13314515203060987625704783872) }, { argument := 1144536352620701562217431040, coefficient := (-1144536352620701562217431040) }, { argument := 8457096801401761076797767680, coefficient := (-8457096801401761076797767680) }, { argument := 8052561230333382709324283904, coefficient := (-8052561230333382709324283904) }, { argument := 14500825739869284090056278016, coefficient := (-14500825739869284090056278016) }, { argument := 199258057678249448743492386816, coefficient := (-199258057678249448743492386816) }, { argument := 6339250330262450217978691584, coefficient := (-6339250330262450217978691584) }, { argument := 14500829742812748085028978688, coefficient := (-14500829742812748085028978688) }, { argument := 6510581420269543467113250816, coefficient := (-6510581420269543467113250816) }, { argument := 6510581420269543467113250816, coefficient := (-6510581420269543467113250816) }, { argument := 110165890874560959193521586176, coefficient := (-110165890874560959193521586176) }, { argument := 5996588150248263719709573120, coefficient := (-5996588150248263719709573120) }, { argument := 199258057678249448743492386816, coefficient := (-199258057678249448743492386816) }, { argument := 110165890874560959193521586176, coefficient := (-110165890874560959193521586176) }, { argument := 8457094799930029079311417344, coefficient := (-8457094799930029079311417344) }, { argument := 6339250330262450217978691584, coefficient := (-6339250330262450217978691584) }, { argument := 5996588150248263719709573120, coefficient := (-5996588150248263719709573120) }, { argument := 8052561230333382709324283904, coefficient := (-8052561230333382709324283904) }, { argument := 14897035064017030416772890624, coefficient := (-14897035064017030416772890624) }, { argument := 200090333985104076740587683840, coefficient := (-200090333985104076740587683840) }, { argument := 8161579412550297867050287104, coefficient := (-8161579412550297867050287104) }, { argument := 190736272308580741404501737472, coefficient := (-190736272308580741404501737472) }, { argument := 164811248782467305315273539584, coefficient := (-164811248782467305315273539584) }, { argument := 14897032888454151223652646912, coefficient := (-14897032888454151223652646912) }, { argument := 165074525537710863310984839168, coefficient := (-165074525537710863310984839168) }, { argument := 147961536446879593589750366208, coefficient := (-147961536446879593589750366208) }, { argument := 200090333985104076740587683840, coefficient := (-200090333985104076740587683840) }, { argument := 8161579412550297867050287104, coefficient := (-8161579412550297867050287104) }, { argument := 83927779393207755876178329600, coefficient := (-83927779393207755876178329600) }, { argument := 82922275216804184472944640000, coefficient := (-82922275216804184472944640000) }, { argument := 83927582554919274349194117120, coefficient := (-83927582554919274349194117120) }, { argument := 83736835877087133239869440000, coefficient := (-83736835877087133239869440000) }, { argument := 6917494993398265861877268480, coefficient := (-6917494993398265861877268480) }, { argument := 23651384062175765653604007936, coefficient := (-23651384062175765653604007936) }, { argument := 6917492759036389933807828992, coefficient := (-6917492759036389933807828992) }, { argument := 13668787826052928164530749440, coefficient := (-13668787826052928164530749440) }, { argument := 13662607103794608217226477568, coefficient := (-13662607103794608217226477568) }, { argument := 39842884635593685977020760064, coefficient := (-39842884635593685977020760064) }, { argument := 435311714205507266386329600, coefficient := (-435311714205507266386329600) }, { argument := 435114875917025739402117120, coefficient := (-435114875917025739402117120) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 74092984720590955788369920, coefficient := (-74092984720590955788369920) }, { argument := 7768515816281127248598138880, coefficient := (-7768515816281127248598138880) }, { argument := 83736835877087133239869440000, coefficient := (-83736835877087133239869440000) }, { argument := 7768521742297660927791595520, coefficient := (-7768521742297660927791595520) }, { argument := 74092984720590955788369920, coefficient := (-74092984720590955788369920) }, { argument := 4716748697594379651564699648, coefficient := (-4716748697594379651564699648) }, { argument := 165074444574951123799762796544, coefficient := (-165074444574951123799762796544) }, { argument := 165074525537710863310984839168, coefficient := (-165074525537710863310984839168) }, { argument := 4716708216214509895953678336, coefficient := (-4716708216214509895953678336) }, { argument := 6917494993398265861877268480, coefficient := (-6917494993398265861877268480) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-249899454006099986879565984169984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10257152793, 2999984271, 458375911, 8021007029, 8021010963, 458371977,
    12690727035, 347123644521, 101525783487, 11553725385, 11548501047, 690786075,
    18894755145, 5526286815, 6569765415, 6566794713, 31, 154966945,
    2711728355, 2711729685, 154965615, 22953834435, 627845720961, 183630616167,
    11855783565, 11850422643, 12690727035, 347123644521, 101525783487, 185086149795,
    185002457949, 1451, 226543635, 226441197, 395, 1945295247,
    154965615, 50567727, 7517286993, 510570921, 1945294635, 1022773059,
    458371977, 154965615, 50567727, 9400390975, 1668143155, 9397659295,
    842264815, 4218531, 11553725385, 11548501047, 1451, 35,
    50568161, 884879779, 884880213, 50567727, 730259565, 19974455439,
    5842074633, 377572725, 377401995, 690786075
  ]
def negativeCoefficients : Array ℕ := #[
    23651384062175765653604007936, 6917492759036389933807828992, 4227771559885233435692761088, 147961463877388407616374308864, 147961536446879593589750366208, 4227735275139640449004732416,
    117051296861975919715449569280, 400206314525763613559667818496, 117051259054221019143116685312, 13320538454688522351421685760, 13314515203060987625704783872, 6371376967603665925413273600,
    21784169530951363102003691520, 6371374909638780202191421440, 7574423827175826435122135040, 7570998840956247865596837888, 599627206528856070654263296, 5717271148599248062502666240,
    200090235848425604605773086720, 200090333985104076740587683840, 5717222080260011995095367680, 211711754666373242035875348480, 723856833271326722503722663936, 211711686283140039289960660992,
    13668787826052928164530749440, 13662607103794608217226477568, 117051296861975919715449569280, 400206314525763613559667818496, 117051259054221019143116685312, 213389802303539661982578769920,
    213293312174526017454917812224, 28066421828173230919978582016, 8357984912745739514617528320, 8354205617606894196520648704, 7640411179964456384143032320, 8971090892303152104276492288,
    5717222080260011995095367680, 233202479589553120852574208, 34667367322124161405704732672, 4709185555582588827539079168, 8971088069951308826715095040, 4716708216214509895953678336,
    4227735275139640449004732416, 5717222080260011995095367680, 233202479589553120852574208, 21675825813579250472792883200, 7692952464648850996587397120, 21669526988347841609298083840,
    7768521742297660927791595520, 39842898802693134585956401152, 13320538454688522351421685760, 13314515203060987625704783872, 28066421828173230919978582016, 676998458984192337835458560,
    233204481061285118338924544, 8161575409606833872077586432, 8161579412550297867050287104, 233202479589553120852574208, 6735455651466732549722603520, 23028979218434298136403902464,
    6735453475903853356602359808, 435311714205507266386329600, 435114875917025739402117120, 6371376967603665925413273600
  ]
def negativeScales : Array ℕ := #[
    33, 31, 28, 32, 32, 28,
    33, 38, 36, 33, 33, 29,
    34, 32, 32, 32, 4, 27,
    31, 31, 27, 34, 39, 37,
    33, 33, 33, 38, 36, 37,
    37, 10, 27, 27, 8, 30,
    27, 25, 32, 28, 30, 29,
    28, 27, 25, 33, 30, 33,
    29, 22, 33, 33, 10, 5,
    25, 29, 29, 25, 29, 34,
    32, 28, 28, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33255911268369001, 31482307790637638, 28771955987686142, 32901136235340787, 32901136942927919, 28771943605738152,
    33563055670516683, 38336658682253363, 36563055204523817, 33427639058340018, 33426986556151521, 29363663760131738,
    34137266771870382, 32363663294138872, 32613194711504187, 32612542209315549, 4954196321574415, 27207385275435475,
    31336565518993377, 31336566226580451, 27207372893487580, 34418016124660002, 39191619136398634, 37418015658667136,
    33464871964539053, 33464219462350555, 33563055670516683, 38336658682253363, 36563055204523817, 37429405984514207,
    37428753482325710, 10502831804067043, 27755213716620416, 27754561214428378, 8625708843075807, 30857341992709296,
    27207372893487580, 25591713595547996, 32807564938457057, 28927536139186609, 30857341538829845, 29929838925344772,
    28771943605738152, 27207372893487580, 25591713595547996, 33130073615666269, 30635595955820999, 33129654318860438,
    29649698658945621, 22008309272528510, 33427639058340018, 33426986556151521, 10502831804067043, 5129283016944967,
    25591725977495892, 29720906221166773, 29720906928753850, 25591713595547996, 29443834108815757, 34217437120554365,
    32443833642822890, 28492179310534916, 28491526808346416, 29363663760131738
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
noncomputable def negativeCeiling : ℝ := 860907337 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23651384062175765653604007936, coefficient := (-23651384062175765653604007936) }, { argument := 6917492759036389933807828992, coefficient := (-6917492759036389933807828992) }, { argument := 4227771559885233435692761088, coefficient := (-4227771559885233435692761088) }, { argument := 147961463877388407616374308864, coefficient := (-147961463877388407616374308864) }, { argument := 147961536446879593589750366208, coefficient := (-147961536446879593589750366208) }, { argument := 4227735275139640449004732416, coefficient := (-4227735275139640449004732416) }, { argument := 117051296861975919715449569280, coefficient := (-117051296861975919715449569280) }, { argument := 400206314525763613559667818496, coefficient := (-400206314525763613559667818496) }, { argument := 117051259054221019143116685312, coefficient := (-117051259054221019143116685312) }, { argument := 13320538454688522351421685760, coefficient := (-13320538454688522351421685760) }, { argument := 13314515203060987625704783872, coefficient := (-13314515203060987625704783872) }, { argument := 6371376967603665925413273600, coefficient := (-6371376967603665925413273600) }, { argument := 21784169530951363102003691520, coefficient := (-21784169530951363102003691520) }, { argument := 6371374909638780202191421440, coefficient := (-6371374909638780202191421440) }, { argument := 7574423827175826435122135040, coefficient := (-7574423827175826435122135040) }, { argument := 7570998840956247865596837888, coefficient := (-7570998840956247865596837888) }, { argument := 599627206528856070654263296, coefficient := (-599627206528856070654263296) }, { argument := 5717271148599248062502666240, coefficient := (-5717271148599248062502666240) }, { argument := 200090235848425604605773086720, coefficient := (-200090235848425604605773086720) }, { argument := 200090333985104076740587683840, coefficient := (-200090333985104076740587683840) }, { argument := 5717222080260011995095367680, coefficient := (-5717222080260011995095367680) }, { argument := 211711754666373242035875348480, coefficient := (-211711754666373242035875348480) }, { argument := 723856833271326722503722663936, coefficient := (-723856833271326722503722663936) }, { argument := 211711686283140039289960660992, coefficient := (-211711686283140039289960660992) }, { argument := 13668787826052928164530749440, coefficient := (-13668787826052928164530749440) }, { argument := 13662607103794608217226477568, coefficient := (-13662607103794608217226477568) }, { argument := 117051296861975919715449569280, coefficient := (-117051296861975919715449569280) }, { argument := 400206314525763613559667818496, coefficient := (-400206314525763613559667818496) }, { argument := 117051259054221019143116685312, coefficient := (-117051259054221019143116685312) }, { argument := 213389802303539661982578769920, coefficient := (-213389802303539661982578769920) }, { argument := 213293312174526017454917812224, coefficient := (-213293312174526017454917812224) }, { argument := 28066421828173230919978582016, coefficient := (-28066421828173230919978582016) }, { argument := 8357984912745739514617528320, coefficient := (-8357984912745739514617528320) }, { argument := 8354205617606894196520648704, coefficient := (-8354205617606894196520648704) }, { argument := 7640411179964456384143032320, coefficient := (-7640411179964456384143032320) }, { argument := 8971090892303152104276492288, coefficient := (-8971090892303152104276492288) }, { argument := 5717222080260011995095367680, coefficient := (-5717222080260011995095367680) }, { argument := 233202479589553120852574208, coefficient := (-233202479589553120852574208) }, { argument := 34667367322124161405704732672, coefficient := (-34667367322124161405704732672) }, { argument := 4709185555582588827539079168, coefficient := (-4709185555582588827539079168) }, { argument := 8971088069951308826715095040, coefficient := (-8971088069951308826715095040) }, { argument := 4716708216214509895953678336, coefficient := (-4716708216214509895953678336) }, { argument := 4227735275139640449004732416, coefficient := (-4227735275139640449004732416) }, { argument := 5717222080260011995095367680, coefficient := (-5717222080260011995095367680) }, { argument := 233202479589553120852574208, coefficient := (-233202479589553120852574208) }, { argument := 21675825813579250472792883200, coefficient := (-21675825813579250472792883200) }, { argument := 7692952464648850996587397120, coefficient := (-7692952464648850996587397120) }, { argument := 21669526988347841609298083840, coefficient := (-21669526988347841609298083840) }, { argument := 7768521742297660927791595520, coefficient := (-7768521742297660927791595520) }, { argument := 39842898802693134585956401152, coefficient := (-39842898802693134585956401152) }, { argument := 13320538454688522351421685760, coefficient := (-13320538454688522351421685760) }, { argument := 13314515203060987625704783872, coefficient := (-13314515203060987625704783872) }, { argument := 28066421828173230919978582016, coefficient := (-28066421828173230919978582016) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 233204481061285118338924544, coefficient := (-233204481061285118338924544) }, { argument := 8161575409606833872077586432, coefficient := (-8161575409606833872077586432) }, { argument := 8161579412550297867050287104, coefficient := (-8161579412550297867050287104) }, { argument := 233202479589553120852574208, coefficient := (-233202479589553120852574208) }, { argument := 6735455651466732549722603520, coefficient := (-6735455651466732549722603520) }, { argument := 23028979218434298136403902464, coefficient := (-23028979218434298136403902464) }, { argument := 6735453475903853356602359808, coefficient := (-6735453475903853356602359808) }, { argument := 435311714205507266386329600, coefficient := (-435311714205507266386329600) }, { argument := 435114875917025739402117120, coefficient := (-435114875917025739402117120) }, { argument := 6371376967603665925413273600, coefficient := (-6371376967603665925413273600) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2
