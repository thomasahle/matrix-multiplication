import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

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
def constantNumerator : ℤ := (-4415920061108589391684280283824128)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2518586325, 16219755379, 587809303693, 4702476157685, 129756314891, 3082725,
    227651175, 2372770125, 227651175, 3082725, 4415439955, 160017005485,
    1280136514325, 35323049195, 4288676733, 7268727939, 4288676733, 37796003227151,
    1055189451373041, 3114122725, 2758222985, 129102630685, 35145099325, 527594888772369,
    129102630685, 3114122725, 3114122725, 1334624025, 3114122725, 35145099325,
    1334624025, 18897838527727, 2758222985, 19304406327919, 1499827969183629, 23168818917,
    13962554675022815, 23774539673, 757150945, 23168818917, 13174426443, 23774539673,
    371155393239, 454290567, 749914405068763, 23168818917, 757150945, 454290567,
    757150945, 11660124553, 13174426443, 19304406327919, 132082397338905, 4772979015,
    2142482717604171, 118105842435, 3757451565, 2142483759178221, 1929502155, 1929502155,
    65298415035, 3554346075, 118105842435, 65298415035
  ]
def negativeCoefficients : Array ℕ := #[
    23229858682409834360969625600, 299201676414586872307294142464, 10843167789370185802924202917888, 10843171774192029588486482821120, 299197691592743086745014239232, 909859825994020440086937600,
    134381534825736513091377561600, 1400636263731802304050888704000, 134381534825736513091377561600, 909859825994020440086937600, 81450490822716619270421217280, 2951792747623172565234362613760,
    2951793832395487034770613862400, 81449406050402149734169968640, 79112122108523791015401750528, 268168728064310586404763598848, 79112122108523791015401750528, 10638629128118206742770221056,
    297009426250556597276975824896, 7180678115274748717118259200, 6360029187814777435161886720, 297690398436104582529674117120, 81039081586672164093191782400, 297009518059727414027121328128,
    297690398436104582529674117120, 7180678115274748717118259200, 7180678115274748717118259200, 6154866955949784614672793600, 7180678115274748717118259200, 81039081586672164093191782400,
    6154866955949784614672793600, 10638537318947389992624717824, 6360029187814777435161886720, 21734829286256163353270419456, 1688656170783809830544260202496, 213694636526009750922184359936,
    15720439007893231626841814466560, 219281424409042685586816630784, 6983484853791168330790338560, 213694636526009750922184359936, 121512636455966328955751890944, 219281424409042685586816630784,
    3423304275328430715753423962112, 134082909192790431951174500352, 1688657117613724121785878708224, 213694636526009750922184359936, 6983484853791168330790338560, 134082909192790431951174500352,
    6983484853791168330790338560, 215091333496767984588342427648, 121512636455966328955751890944, 21734829286256163353270419456, 297423117718847175236454973440, 22011480589722825767056834560,
    9648884368649872126185691938816, 544667062252077582278448906240, 17328186847228607518746869760, 9648889059482375584964061167616, 17796516221478029343577866240, 17796516221478029343577866240,
    301135787642378233366330736640, 16391528098729763869084876800, 544667062252077582278448906240, 301135787642378233366330736640
  ]
def negativeScales : Array ℕ := #[
    31, 33, 39, 42, 36, 21,
    27, 31, 27, 21, 32, 37,
    40, 35, 31, 32, 31, 45,
    49, 31, 31, 36, 35, 48,
    36, 31, 31, 30, 31, 35,
    30, 44, 31, 44, 50, 34,
    53, 34, 29, 34, 33, 34,
    38, 28, 49, 34, 29, 28,
    29, 33, 33, 44, 46, 32,
    50, 36, 31, 50, 30, 30,
    35, 31, 36, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31229967034462231, 33917033016250977, 39096557237533371, 42096557767718071, 36917013802048500, 21555774766318130,
    27762249665102408, 31143925192366123, 27762249665102408, 21555774766318130, 32039910049339919, 37219434276531092,
    40219434806715792, 35039890835139436, 31997885451121588, 32759055762191544, 31997885451121588, 45103298916944225,
    49906423475500224, 31536178654942314, 31361091948383354, 36909727447257614, 35032604481060943, 48906423921454509,
    36909727447257614, 31536178654942314, 31536178654942314, 30313786233604997, 31536178654942314, 35032604481060943,
    30313786233604997, 44103286466730446, 31361091948383354, 44133995421022584, 50413718455872442, 34431465450304806,
    53632412448282844, 34468698356503850, 29496005702499731, 34431465450304806, 33617021103469855, 34468698356503850,
    38433232376478996, 28759040108606943, 49413719264791666, 34431465450304806, 29496005702499731, 28759040108606943,
    29496005702499731, 33440864148307066, 33617021103469855, 44133995421022584, 46908431544489885, 32152242847400894,
    50928204997336003, 36781289377635471, 31807107362098456, 50928205698706206, 30845581510758487, 30845581510758487,
    35926328930001426, 31726937012802925, 36781289377635471, 35926328930001426
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
noncomputable def negativeCeiling : ℝ := 21235536343 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23229858682409834360969625600, coefficient := (-23229858682409834360969625600) }, { argument := 299201676414586872307294142464, coefficient := (-299201676414586872307294142464) }, { argument := 10843167789370185802924202917888, coefficient := (-10843167789370185802924202917888) }, { argument := 10843171774192029588486482821120, coefficient := (-10843171774192029588486482821120) }, { argument := 299197691592743086745014239232, coefficient := (-299197691592743086745014239232) }, { argument := 909859825994020440086937600, coefficient := (-909859825994020440086937600) }, { argument := 134381534825736513091377561600, coefficient := (-134381534825736513091377561600) }, { argument := 1400636263731802304050888704000, coefficient := (-1400636263731802304050888704000) }, { argument := 134381534825736513091377561600, coefficient := (-134381534825736513091377561600) }, { argument := 909859825994020440086937600, coefficient := (-909859825994020440086937600) }, { argument := 81450490822716619270421217280, coefficient := (-81450490822716619270421217280) }, { argument := 2951792747623172565234362613760, coefficient := (-2951792747623172565234362613760) }, { argument := 2951793832395487034770613862400, coefficient := (-2951793832395487034770613862400) }, { argument := 81449406050402149734169968640, coefficient := (-81449406050402149734169968640) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 268168728064310586404763598848, coefficient := (-268168728064310586404763598848) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 10638629128118206742770221056, coefficient := (-10638629128118206742770221056) }, { argument := 297009426250556597276975824896, coefficient := (-297009426250556597276975824896) }, { argument := 7180678115274748717118259200, coefficient := (-7180678115274748717118259200) }, { argument := 6360029187814777435161886720, coefficient := (-6360029187814777435161886720) }, { argument := 297690398436104582529674117120, coefficient := (-297690398436104582529674117120) }, { argument := 81039081586672164093191782400, coefficient := (-81039081586672164093191782400) }, { argument := 297009518059727414027121328128, coefficient := (-297009518059727414027121328128) }, { argument := 297690398436104582529674117120, coefficient := (-297690398436104582529674117120) }, { argument := 7180678115274748717118259200, coefficient := (-7180678115274748717118259200) }, { argument := 7180678115274748717118259200, coefficient := (-7180678115274748717118259200) }, { argument := 6154866955949784614672793600, coefficient := (-6154866955949784614672793600) }, { argument := 7180678115274748717118259200, coefficient := (-7180678115274748717118259200) }, { argument := 81039081586672164093191782400, coefficient := (-81039081586672164093191782400) }, { argument := 6154866955949784614672793600, coefficient := (-6154866955949784614672793600) }, { argument := 10638537318947389992624717824, coefficient := (-10638537318947389992624717824) }, { argument := 6360029187814777435161886720, coefficient := (-6360029187814777435161886720) }, { argument := 21734829286256163353270419456, coefficient := (-21734829286256163353270419456) }, { argument := 1688656170783809830544260202496, coefficient := (-1688656170783809830544260202496) }, { argument := 213694636526009750922184359936, coefficient := (-213694636526009750922184359936) }, { argument := 15720439007893231626841814466560, coefficient := (-15720439007893231626841814466560) }, { argument := 219281424409042685586816630784, coefficient := (-219281424409042685586816630784) }, { argument := 6983484853791168330790338560, coefficient := (-6983484853791168330790338560) }, { argument := 213694636526009750922184359936, coefficient := (-213694636526009750922184359936) }, { argument := 121512636455966328955751890944, coefficient := (-121512636455966328955751890944) }, { argument := 219281424409042685586816630784, coefficient := (-219281424409042685586816630784) }, { argument := 3423304275328430715753423962112, coefficient := (-3423304275328430715753423962112) }, { argument := 134082909192790431951174500352, coefficient := (-134082909192790431951174500352) }, { argument := 1688657117613724121785878708224, coefficient := (-1688657117613724121785878708224) }, { argument := 213694636526009750922184359936, coefficient := (-213694636526009750922184359936) }, { argument := 6983484853791168330790338560, coefficient := (-6983484853791168330790338560) }, { argument := 134082909192790431951174500352, coefficient := (-134082909192790431951174500352) }, { argument := 6983484853791168330790338560, coefficient := (-6983484853791168330790338560) }, { argument := 215091333496767984588342427648, coefficient := (-215091333496767984588342427648) }, { argument := 121512636455966328955751890944, coefficient := (-121512636455966328955751890944) }, { argument := 21734829286256163353270419456, coefficient := (-21734829286256163353270419456) }, { argument := 297423117718847175236454973440, coefficient := (-297423117718847175236454973440) }, { argument := 22011480589722825767056834560, coefficient := (-22011480589722825767056834560) }, { argument := 9648884368649872126185691938816, coefficient := (-9648884368649872126185691938816) }, { argument := 544667062252077582278448906240, coefficient := (-544667062252077582278448906240) }, { argument := 17328186847228607518746869760, coefficient := (-17328186847228607518746869760) }, { argument := 9648889059482375584964061167616, coefficient := (-9648889059482375584964061167616) }, { argument := 17796516221478029343577866240, coefficient := (-17796516221478029343577866240) }, { argument := 17796516221478029343577866240, coefficient := (-17796516221478029343577866240) }, { argument := 301135787642378233366330736640, coefficient := (-301135787642378233366330736640) }, { argument := 16391528098729763869084876800, coefficient := (-16391528098729763869084876800) }, { argument := 544667062252077582278448906240, coefficient := (-544667062252077582278448906240) }, { argument := 301135787642378233366330736640, coefficient := (-301135787642378233366330736640) }] }

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
def constantNumerator : ℤ := (-1924260603635388695251749032689664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    132081333812343, 3757451565, 3554346075, 4772979015, 157218975, 11610209925,
    121011276375, 11610209925, 157218975, 16219755379, 587809303693, 4702476157685,
    129756314891, 6376724346191, 173554514445061, 51013787816579, 391241515, 14178722005,
    113429817725, 3129890435, 6908108031, 11708310273, 6908108031, 535,
    535, 85720527, 7208174129, 3604086195, 42861133, 5137875,
    379418625, 3954616875, 379418625, 5137875, 81086985, 6818543095,
    3409270725, 40544315, 3082725, 227651175, 2372770125, 227651175,
    3082725, 391241515, 14178722005, 113429817725, 3129890435, 5137875,
    379418625, 3954616875, 379418625, 5137875, 167674935, 6076595145,
    48612779025, 1341381615, 214005825, 362710975, 214005825, 108888237,
    9156329299, 4578163545, 54445223, 79123275
  ]
def negativeCoefficients : Array ℕ := #[
    297420722869933014324099416064, 17328186847228607518746869760, 16391528098729763869084876800, 22011480589722825767056834560, 1450089097677970076388556800, 214170571128517567739382988800,
    2232264045322559922081103872000, 214170571128517567739382988800, 1450089097677970076388556800, 299201676414586872307294142464, 10843167789370185802924202917888, 10843171774192029588486482821120,
    299197691592743086745014239232, 229745707114801258672987045888, 781620046583244084976084320256, 229745675801502733146924253184, 7217132098215396644214538240, 261551256118508961476462510080,
    261551352237574800549294899200, 7217035979149557571382149120, 127432100881394609479898628096, 431960406283230824807673102336, 127432100881394609479898628096, 10348405015901225735484866560,
    10348405015901225735484866560, 197658077929063701182152704, 16620917924549657377330167808, 16620913914688664354716385280, 197662087790056723795935232, 47388532603855231254528000,
    6999038272173776723509248000, 72949805402698036669317120000, 6999038272173776723509248000, 47388532603855231254528000, 186973857500465663280414720, 15722489928628054275852861440,
    15722486135516304119326310400, 186977650612215819806965760, 909859825994020440086937600, 134381534825736513091377561600, 1400636263731802304050888704000, 134381534825736513091377561600,
    909859825994020440086937600, 7217132098215396644214538240, 261551256118508961476462510080, 261551352237574800549294899200, 7217035979149557571382149120, 47388532603855231254528000,
    6999038272173776723509248000, 72949805402698036669317120000, 6999038272173776723509248000, 47388532603855231254528000, 6186113227041768552183889920, 224186790958721966979825008640,
    224186873346492686185109913600, 6186030839271049346898984960, 3947710684058073403962163200, 13381673057101326666904371200, 3947710684058073403962163200, 251079180072053890690842624,
    21113057904157672884716699648, 21113052810550465531666759680, 251084273679261243740782592, 1459566804198741122639462400
  ]
def negativeScales : Array ℕ := #[
    46, 31, 31, 32, 27, 33,
    36, 33, 27, 33, 39, 42,
    36, 42, 47, 45, 28, 33,
    36, 31, 32, 33, 32, 9,
    9, 26, 32, 31, 25, 22,
    28, 31, 28, 22, 26, 32,
    31, 25, 21, 27, 31, 27,
    21, 28, 33, 36, 31, 22,
    28, 31, 28, 22, 27, 32,
    35, 30, 27, 28, 27, 26,
    33, 32, 25, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    46908419927871447, 31807107362098456, 31726937012802925, 32152242847400894, 27228200108288044, 33434675006780699,
    36816350535235970, 33434675006780699, 27228200108288044, 33917033016250977, 39096557237533371, 42096557767718071,
    36917013802048500, 42535952656199502, 47302382221004179, 45535952459566693, 28543484223221510, 33723008450534821,
    36723008980719522, 31543465009021026, 32685643498365071, 33446813832000410, 32685643498365071, 9063395081288510,
    9063395081288510, 26353137383777438, 32746986717180977, 31746986369125152, 25353166651227324, 22292740360482754,
    28499215258975648, 31880890789620445, 28499215258975648, 22292740360482754, 26272967035093454, 32666816368318971,
    31666816020263148, 25272996302543340, 21555774766318130, 27762249665102408, 31143925192366123, 27762249665102408,
    21555774766318130, 28543484223221510, 33723008450534821, 36723008980719522, 31543465009021026, 22292740360482754,
    28499215258975648, 31880890789620445, 28499215258975648, 22292740360482754, 27321091801883972, 32500616029075422,
    35500616559260122, 30321072587683489, 27673074824848482, 28434245158497339, 27673074824848482, 26698272869895627,
    33092122203019146, 32092121854963323, 25698302137345560, 26237598806290293
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
noncomputable def negativeCeiling : ℝ := 3635481971 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 297420722869933014324099416064, coefficient := (-297420722869933014324099416064) }, { argument := 17328186847228607518746869760, coefficient := (-17328186847228607518746869760) }, { argument := 16391528098729763869084876800, coefficient := (-16391528098729763869084876800) }, { argument := 22011480589722825767056834560, coefficient := (-22011480589722825767056834560) }, { argument := 1450089097677970076388556800, coefficient := (-1450089097677970076388556800) }, { argument := 214170571128517567739382988800, coefficient := (-214170571128517567739382988800) }, { argument := 2232264045322559922081103872000, coefficient := (-2232264045322559922081103872000) }, { argument := 214170571128517567739382988800, coefficient := (-214170571128517567739382988800) }, { argument := 1450089097677970076388556800, coefficient := (-1450089097677970076388556800) }, { argument := 299201676414586872307294142464, coefficient := (-299201676414586872307294142464) }, { argument := 10843167789370185802924202917888, coefficient := (-10843167789370185802924202917888) }, { argument := 10843171774192029588486482821120, coefficient := (-10843171774192029588486482821120) }, { argument := 299197691592743086745014239232, coefficient := (-299197691592743086745014239232) }, { argument := 229745707114801258672987045888, coefficient := (-229745707114801258672987045888) }, { argument := 781620046583244084976084320256, coefficient := (-781620046583244084976084320256) }, { argument := 229745675801502733146924253184, coefficient := (-229745675801502733146924253184) }, { argument := 7217132098215396644214538240, coefficient := (-7217132098215396644214538240) }, { argument := 261551256118508961476462510080, coefficient := (-261551256118508961476462510080) }, { argument := 261551352237574800549294899200, coefficient := (-261551352237574800549294899200) }, { argument := 7217035979149557571382149120, coefficient := (-7217035979149557571382149120) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 431960406283230824807673102336, coefficient := (-431960406283230824807673102336) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 197658077929063701182152704, coefficient := (-197658077929063701182152704) }, { argument := 16620917924549657377330167808, coefficient := (-16620917924549657377330167808) }, { argument := 16620913914688664354716385280, coefficient := (-16620913914688664354716385280) }, { argument := 197662087790056723795935232, coefficient := (-197662087790056723795935232) }, { argument := 47388532603855231254528000, coefficient := (-47388532603855231254528000) }, { argument := 6999038272173776723509248000, coefficient := (-6999038272173776723509248000) }, { argument := 72949805402698036669317120000, coefficient := (-72949805402698036669317120000) }, { argument := 6999038272173776723509248000, coefficient := (-6999038272173776723509248000) }, { argument := 47388532603855231254528000, coefficient := (-47388532603855231254528000) }, { argument := 186973857500465663280414720, coefficient := (-186973857500465663280414720) }, { argument := 15722489928628054275852861440, coefficient := (-15722489928628054275852861440) }, { argument := 15722486135516304119326310400, coefficient := (-15722486135516304119326310400) }, { argument := 186977650612215819806965760, coefficient := (-186977650612215819806965760) }, { argument := 909859825994020440086937600, coefficient := (-909859825994020440086937600) }, { argument := 134381534825736513091377561600, coefficient := (-134381534825736513091377561600) }, { argument := 1400636263731802304050888704000, coefficient := (-1400636263731802304050888704000) }, { argument := 134381534825736513091377561600, coefficient := (-134381534825736513091377561600) }, { argument := 909859825994020440086937600, coefficient := (-909859825994020440086937600) }, { argument := 7217132098215396644214538240, coefficient := (-7217132098215396644214538240) }, { argument := 261551256118508961476462510080, coefficient := (-261551256118508961476462510080) }, { argument := 261551352237574800549294899200, coefficient := (-261551352237574800549294899200) }, { argument := 7217035979149557571382149120, coefficient := (-7217035979149557571382149120) }, { argument := 47388532603855231254528000, coefficient := (-47388532603855231254528000) }, { argument := 6999038272173776723509248000, coefficient := (-6999038272173776723509248000) }, { argument := 72949805402698036669317120000, coefficient := (-72949805402698036669317120000) }, { argument := 6999038272173776723509248000, coefficient := (-6999038272173776723509248000) }, { argument := 47388532603855231254528000, coefficient := (-47388532603855231254528000) }, { argument := 6186113227041768552183889920, coefficient := (-6186113227041768552183889920) }, { argument := 224186790958721966979825008640, coefficient := (-224186790958721966979825008640) }, { argument := 224186873346492686185109913600, coefficient := (-224186873346492686185109913600) }, { argument := 6186030839271049346898984960, coefficient := (-6186030839271049346898984960) }, { argument := 3947710684058073403962163200, coefficient := (-3947710684058073403962163200) }, { argument := 13381673057101326666904371200, coefficient := (-13381673057101326666904371200) }, { argument := 3947710684058073403962163200, coefficient := (-3947710684058073403962163200) }, { argument := 251079180072053890690842624, coefficient := (-251079180072053890690842624) }, { argument := 21113057904157672884716699648, coefficient := (-21113057904157672884716699648) }, { argument := 21113052810550465531666759680, coefficient := (-21113052810550465531666759680) }, { argument := 251084273679261243740782592, coefficient := (-251084273679261243740782592) }, { argument := 1459566804198741122639462400, coefficient := (-1459566804198741122639462400) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
