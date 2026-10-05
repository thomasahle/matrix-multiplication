import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 20, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

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
def constantNumerator : ℤ := (-2772680023561829347153201558716416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    68284246821, 36108243, 4555450075, 88843540225, 177687015275, 569433975,
    1911309, 903617811, 34300611609, 3614473723, 1911309, 9053236225,
    176562478675, 353124827825, 1131659925, 231789747, 27091721475, 7417269405,
    186090541, 32638532563, 8159634119, 46521657, 22160853, 10477082187,
    397701685953, 41908357491, 22160853, 1441598125, 28115044375, 56230068125,
    180200625, 36108243, 17071049997, 648003446343, 68284246821, 36108243,
    139719690275, 2724910100825, 5449818202675, 17465044575, 193946523, 22668583275,
    6206286645, 8937908375, 174313275125, 348626422375, 1117243875, 5425772241,
    634167439425, 173624653215, 51079923, 1533815433, 1149221295, 524189583,
    363677625, 43641315, 1149221295, 2283895485, 363677625, 35247635415,
    2254801275, 383454009, 1149221295, 43641315
  ]
def negativeCoefficients : Array ℕ := #[
    629811012686501019806091706368, 5328636140578515209372565504, 21008305418521495609330892800, 819437024566447456981404876800, 819436723999811205976398233600, 21008405607400245944333107200,
    141029711875110917558501376, 16668806499962647681041432576, 158183650980733449463488577536, 16668817932332287362536046592, 141029711875110917558501376, 20875341460176422852309811200,
    814250714284381333835952947200, 814250415620065565432243814400, 20875441014948345653546188800, 8551532283637772641112162304, 31234628285346627651738009600, 8551529402486932628601569280,
    214547786522822146068054016, 37629666070693529538934079488, 37629670582075377065526296576, 214543275140974619475836928, 1635182334984394152232353792, 193268053742810158247750664192,
    1834075304614449995130718912512, 193268186296501385906161188864, 1635182334984394152232353792, 13296395834507275702108160000, 518631028206612314545192960000, 518630837974564054415441920000,
    13296459245190029078691840000, 5328636140578515209372565504, 629810580728318417786376290304, 5976776866785550333782622470144, 629811012686501019806091706368, 5328636140578515209372565504,
    322171671070111290262080716800, 12566429813446216381430025420800, 12566425204123687038486157721600, 322173207510954404576703283200, 114485819960538343929991397376, 418161554187497708970206822400,
    114485781388396485803318968320, 20609413543486277338267648000, 803878093720249087545049088000, 803877798860574284343934976000, 20609511830044545071972352000, 200175663863929086109298982912,
    731145278434542488092724428800, 200175596421479831122571427840, 942258266885790220909805568, 28293900748856999828130889728, 21199391112922066362008862720, 154713457339288497995328258048,
    13417336147419029343043584000, 805040168845141760582615040, 21199391112922066362008862720, 21065217751447876068578426880, 13417336147419029343043584000, 325102054851963080981946040320,
    20796871028499495481717555200, 28293911872243676274990514176, 21199391112922066362008862720, 805040168845141760582615040
  ]
def negativeScales : Array ℕ := #[
    35, 25, 32, 36, 37, 29,
    20, 29, 34, 31, 20, 33,
    37, 38, 30, 27, 34, 32,
    27, 34, 32, 25, 24, 33,
    38, 35, 24, 30, 34, 35,
    27, 25, 33, 39, 35, 25,
    37, 41, 42, 34, 27, 34,
    32, 33, 37, 38, 30, 32,
    39, 37, 25, 30, 30, 28,
    28, 25, 30, 31, 28, 35,
    31, 28, 30, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35990833756401869, 25105824885748244, 32084946452227257, 36370547831214722, 37370547302039127, 29084953332442057,
    20866129608350967, 29751137466966286, 34997515272732868, 31751138456444292, 20866129608350967, 33075786452941781,
    37361387831929245, 38361387302753650, 30075793333156581, 27788241511112828, 34657133017763469, 32788241025045228,
    27471429484032813, 34925857150586521, 32925857323549751, 25471399147590036, 24401510077872360, 33286517938606346,
    38532895721848765, 35286518928084347, 24401510077872360, 30425021893824897, 34710623272905095, 35710622743729499,
    27425028774039697, 25105824885748244, 33990832766923542, 39237210529723871, 35990833756401869, 25105824885748244,
    37023744393501500, 41309345772488964, 42309345243313368, 34023751273716300, 27531083671109095, 34399975178240832,
    32531083185041501, 33057290109324391, 37342891488311855, 38342890959136260, 30057296989539192, 32337181342506095,
    39206072849638567, 37337180856438501, 25606253014482033, 30514477744966008, 30098009485267503, 28965513456489788,
    28438084926865155, 25379191237811559, 30098009485267503, 31088849485982027, 28438084926865155, 35036807426541747,
    31070353142364638, 28514478312143075, 30098009485267503, 25379191237811559
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
noncomputable def negativeCeiling : ℝ := 21421775431 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 629811012686501019806091706368, coefficient := (-629811012686501019806091706368) }, { argument := 5328636140578515209372565504, coefficient := (-5328636140578515209372565504) }, { argument := 21008305418521495609330892800, coefficient := (-21008305418521495609330892800) }, { argument := 819437024566447456981404876800, coefficient := (-819437024566447456981404876800) }, { argument := 819436723999811205976398233600, coefficient := (-819436723999811205976398233600) }, { argument := 21008405607400245944333107200, coefficient := (-21008405607400245944333107200) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 16668806499962647681041432576, coefficient := (-16668806499962647681041432576) }, { argument := 158183650980733449463488577536, coefficient := (-158183650980733449463488577536) }, { argument := 16668817932332287362536046592, coefficient := (-16668817932332287362536046592) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 20875341460176422852309811200, coefficient := (-20875341460176422852309811200) }, { argument := 814250714284381333835952947200, coefficient := (-814250714284381333835952947200) }, { argument := 814250415620065565432243814400, coefficient := (-814250415620065565432243814400) }, { argument := 20875441014948345653546188800, coefficient := (-20875441014948345653546188800) }, { argument := 8551532283637772641112162304, coefficient := (-8551532283637772641112162304) }, { argument := 31234628285346627651738009600, coefficient := (-31234628285346627651738009600) }, { argument := 8551529402486932628601569280, coefficient := (-8551529402486932628601569280) }, { argument := 214547786522822146068054016, coefficient := (-214547786522822146068054016) }, { argument := 37629666070693529538934079488, coefficient := (-37629666070693529538934079488) }, { argument := 37629670582075377065526296576, coefficient := (-37629670582075377065526296576) }, { argument := 214543275140974619475836928, coefficient := (-214543275140974619475836928) }, { argument := 1635182334984394152232353792, coefficient := (-1635182334984394152232353792) }, { argument := 193268053742810158247750664192, coefficient := (-193268053742810158247750664192) }, { argument := 1834075304614449995130718912512, coefficient := (-1834075304614449995130718912512) }, { argument := 193268186296501385906161188864, coefficient := (-193268186296501385906161188864) }, { argument := 1635182334984394152232353792, coefficient := (-1635182334984394152232353792) }, { argument := 13296395834507275702108160000, coefficient := (-13296395834507275702108160000) }, { argument := 518631028206612314545192960000, coefficient := (-518631028206612314545192960000) }, { argument := 518630837974564054415441920000, coefficient := (-518630837974564054415441920000) }, { argument := 13296459245190029078691840000, coefficient := (-13296459245190029078691840000) }, { argument := 5328636140578515209372565504, coefficient := (-5328636140578515209372565504) }, { argument := 629810580728318417786376290304, coefficient := (-629810580728318417786376290304) }, { argument := 5976776866785550333782622470144, coefficient := (-5976776866785550333782622470144) }, { argument := 629811012686501019806091706368, coefficient := (-629811012686501019806091706368) }, { argument := 5328636140578515209372565504, coefficient := (-5328636140578515209372565504) }, { argument := 322171671070111290262080716800, coefficient := (-322171671070111290262080716800) }, { argument := 12566429813446216381430025420800, coefficient := (-12566429813446216381430025420800) }, { argument := 12566425204123687038486157721600, coefficient := (-12566425204123687038486157721600) }, { argument := 322173207510954404576703283200, coefficient := (-322173207510954404576703283200) }, { argument := 114485819960538343929991397376, coefficient := (-114485819960538343929991397376) }, { argument := 418161554187497708970206822400, coefficient := (-418161554187497708970206822400) }, { argument := 114485781388396485803318968320, coefficient := (-114485781388396485803318968320) }, { argument := 20609413543486277338267648000, coefficient := (-20609413543486277338267648000) }, { argument := 803878093720249087545049088000, coefficient := (-803878093720249087545049088000) }, { argument := 803877798860574284343934976000, coefficient := (-803877798860574284343934976000) }, { argument := 20609511830044545071972352000, coefficient := (-20609511830044545071972352000) }, { argument := 200175663863929086109298982912, coefficient := (-200175663863929086109298982912) }, { argument := 731145278434542488092724428800, coefficient := (-731145278434542488092724428800) }, { argument := 200175596421479831122571427840, coefficient := (-200175596421479831122571427840) }, { argument := 942258266885790220909805568, coefficient := (-942258266885790220909805568) }, { argument := 28293900748856999828130889728, coefficient := (-28293900748856999828130889728) }, { argument := 21199391112922066362008862720, coefficient := (-21199391112922066362008862720) }, { argument := 154713457339288497995328258048, coefficient := (-154713457339288497995328258048) }, { argument := 13417336147419029343043584000, coefficient := (-13417336147419029343043584000) }, { argument := 805040168845141760582615040, coefficient := (-805040168845141760582615040) }, { argument := 21199391112922066362008862720, coefficient := (-21199391112922066362008862720) }, { argument := 21065217751447876068578426880, coefficient := (-21065217751447876068578426880) }, { argument := 13417336147419029343043584000, coefficient := (-13417336147419029343043584000) }, { argument := 325102054851963080981946040320, coefficient := (-325102054851963080981946040320) }, { argument := 20796871028499495481717555200, coefficient := (-20796871028499495481717555200) }, { argument := 28293911872243676274990514176, coefficient := (-28293911872243676274990514176) }, { argument := 21199391112922066362008862720, coefficient := (-21199391112922066362008862720) }, { argument := 805040168845141760582615040, coefficient := (-805040168845141760582615040) }] }

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
def constantNumerator : ℤ := (-471871387857890538254468298833920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2254801275, 43641315, 1149221295, 1149221295, 51079923, 3009902769,
    15602453937, 52129270503, 163254944853, 7230405483, 104258503881, 7230405483,
    14080263309, 266002812243, 14080263309, 163254944853, 266002812243, 6019817913,
    14080263309, 14080263309, 15602453937, 433306097, 510889435, 423308389,
    49771046269, 2846383995, 6932895767, 11400132821, 11400132821, 8159634119,
    423308389, 4555450075, 88843540225, 177687015275, 569433975, 193946523,
    22668583275, 6206286645, 175024911, 20457014175, 5600795265, 9654071,
    1693233353, 423308389, 2413467, 1911309, 903617811, 34300611609,
    3614473723, 1911309, 172991775, 3373805325, 6747608175, 21624075,
    1911309, 903617811, 34300611609, 3614473723, 1911309, 8937908375,
    174313275125, 348626422375, 1117243875, 89877657
  ]
def negativeCoefficients : Array ℕ := #[
    20796871028499495481717555200, 805040168845141760582615040, 21199391112922066362008862720, 21199391112922066362008862720, 942258266885790220909805568, 27761453033246359755373412352,
    17988404668605063237847744512, 480807655859008693422652391424, 188220136654428588513089814528, 16672179936755912269224738816, 480807484650165259305876455424, 16672179936755912269224738816,
    16233438359472861946350403584, 613360725041704351378320654336, 16233438359472861946350403584, 188220136654428588513089814528, 613360725041704351378320654336, 27761510102860837794298724352,
    16233438359472861946350403584, 16233438359472861946350403584, 17988404668605063237847744512, 7993086676936966122349002752, 37696986629628284716806307840, 1952165379034321887120326656,
    57382109550312477496698732544, 52506517091267967998408785920, 7993084618972080399127150592, 52573833138820875649688797184, 52573833138820875649688797184, 37629670582075377065526296576,
    1952165379034321887120326656, 21008305418521495609330892800, 819437024566447456981404876800, 819436723999811205976398233600, 21008405607400245944333107200, 114485819960538343929991397376,
    418161554187497708970206822400, 114485781388396485803318968320, 6457279479481583422880612352, 23585331562404596390087884800, 6457277303918704229760368640, 11130386062901327792439296,
    1952165144991256451930390528, 1952165379034321887120326656, 11130152019835892602503168, 141029711875110917558501376, 16668806499962647681041432576, 158183650980733449463488577536,
    16668817932332287362536046592, 141029711875110917558501376, 797783750070436542126489600, 31117861692396738872711577600, 31117850278473843264926515200, 797787554711401744721510400,
    141029711875110917558501376, 16668806499962647681041432576, 158183650980733449463488577536, 16668817932332287362536046592, 141029711875110917558501376, 20609413543486277338267648000,
    803878093720249087545049088000, 803877798860574284343934976000, 20609511830044545071972352000, 6631800546494599191066574848
  ]
def negativeScales : Array ℕ := #[
    31, 25, 30, 30, 25, 31,
    33, 35, 37, 32, 36, 32,
    33, 37, 33, 37, 37, 32,
    33, 33, 33, 28, 28, 28,
    35, 31, 32, 33, 33, 32,
    28, 32, 36, 37, 29, 27,
    34, 32, 27, 34, 32, 23,
    30, 28, 21, 20, 29, 34,
    31, 20, 27, 31, 32, 24,
    20, 29, 34, 31, 20, 33,
    37, 38, 30, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31070353142364638, 25379191237811559, 30098009485267503, 30098009485267503, 25606253014482033, 31487069737334473,
    33861053903450835, 35601374619880598, 37248335734196459, 32751429410372507, 36601374106157095, 32751429410372507,
    33712955262423752, 37952650552972790, 33712955262423752, 37248335734196459, 37952650552972790, 32487072703100172,
    33712955262423752, 33712955262423752, 33861053903450835, 28690811295904872, 28928435867966910, 28657133838966136,
    35534587664023443, 31406483157562663, 32690810924456864, 33408331581955032, 33408331581955032, 32925857323549751,
    28657133838966136, 32084946452227257, 36370547831214722, 37370547302039127, 29084953332442057, 27531083671109095,
    34399975178240832, 32531083185041501, 27382985032119223, 34251876539251692, 32382984546051628, 23202706006317094,
    30657133666002926, 28657133838966136, 21202675669874317, 20866129608350967, 29751137466966286, 34997515272732868,
    31751138456444292, 20866129608350967, 27366128204771312, 31651729583781036, 32651729054605441, 24366135084986112,
    20866129608350967, 29751137466966286, 34997515272732868, 31751138456444292, 20866129608350967, 33057290109324391,
    37342891488311855, 38342890959136260, 30057296989539192, 26421459179933871
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
noncomputable def negativeCeiling : ℝ := 3315569971 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20796871028499495481717555200, coefficient := (-20796871028499495481717555200) }, { argument := 805040168845141760582615040, coefficient := (-805040168845141760582615040) }, { argument := 21199391112922066362008862720, coefficient := (-21199391112922066362008862720) }, { argument := 21199391112922066362008862720, coefficient := (-21199391112922066362008862720) }, { argument := 942258266885790220909805568, coefficient := (-942258266885790220909805568) }, { argument := 27761453033246359755373412352, coefficient := (-27761453033246359755373412352) }, { argument := 17988404668605063237847744512, coefficient := (-17988404668605063237847744512) }, { argument := 480807655859008693422652391424, coefficient := (-480807655859008693422652391424) }, { argument := 188220136654428588513089814528, coefficient := (-188220136654428588513089814528) }, { argument := 16672179936755912269224738816, coefficient := (-16672179936755912269224738816) }, { argument := 480807484650165259305876455424, coefficient := (-480807484650165259305876455424) }, { argument := 16672179936755912269224738816, coefficient := (-16672179936755912269224738816) }, { argument := 16233438359472861946350403584, coefficient := (-16233438359472861946350403584) }, { argument := 613360725041704351378320654336, coefficient := (-613360725041704351378320654336) }, { argument := 16233438359472861946350403584, coefficient := (-16233438359472861946350403584) }, { argument := 188220136654428588513089814528, coefficient := (-188220136654428588513089814528) }, { argument := 613360725041704351378320654336, coefficient := (-613360725041704351378320654336) }, { argument := 27761510102860837794298724352, coefficient := (-27761510102860837794298724352) }, { argument := 16233438359472861946350403584, coefficient := (-16233438359472861946350403584) }, { argument := 16233438359472861946350403584, coefficient := (-16233438359472861946350403584) }, { argument := 17988404668605063237847744512, coefficient := (-17988404668605063237847744512) }, { argument := 7993086676936966122349002752, coefficient := (-7993086676936966122349002752) }, { argument := 37696986629628284716806307840, coefficient := (-37696986629628284716806307840) }, { argument := 1952165379034321887120326656, coefficient := (-1952165379034321887120326656) }, { argument := 57382109550312477496698732544, coefficient := (-57382109550312477496698732544) }, { argument := 52506517091267967998408785920, coefficient := (-52506517091267967998408785920) }, { argument := 7993084618972080399127150592, coefficient := (-7993084618972080399127150592) }, { argument := 52573833138820875649688797184, coefficient := (-52573833138820875649688797184) }, { argument := 52573833138820875649688797184, coefficient := (-52573833138820875649688797184) }, { argument := 37629670582075377065526296576, coefficient := (-37629670582075377065526296576) }, { argument := 1952165379034321887120326656, coefficient := (-1952165379034321887120326656) }, { argument := 21008305418521495609330892800, coefficient := (-21008305418521495609330892800) }, { argument := 819437024566447456981404876800, coefficient := (-819437024566447456981404876800) }, { argument := 819436723999811205976398233600, coefficient := (-819436723999811205976398233600) }, { argument := 21008405607400245944333107200, coefficient := (-21008405607400245944333107200) }, { argument := 114485819960538343929991397376, coefficient := (-114485819960538343929991397376) }, { argument := 418161554187497708970206822400, coefficient := (-418161554187497708970206822400) }, { argument := 114485781388396485803318968320, coefficient := (-114485781388396485803318968320) }, { argument := 6457279479481583422880612352, coefficient := (-6457279479481583422880612352) }, { argument := 23585331562404596390087884800, coefficient := (-23585331562404596390087884800) }, { argument := 6457277303918704229760368640, coefficient := (-6457277303918704229760368640) }, { argument := 11130386062901327792439296, coefficient := (-11130386062901327792439296) }, { argument := 1952165144991256451930390528, coefficient := (-1952165144991256451930390528) }, { argument := 1952165379034321887120326656, coefficient := (-1952165379034321887120326656) }, { argument := 11130152019835892602503168, coefficient := (-11130152019835892602503168) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 16668806499962647681041432576, coefficient := (-16668806499962647681041432576) }, { argument := 158183650980733449463488577536, coefficient := (-158183650980733449463488577536) }, { argument := 16668817932332287362536046592, coefficient := (-16668817932332287362536046592) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 797783750070436542126489600, coefficient := (-797783750070436542126489600) }, { argument := 31117861692396738872711577600, coefficient := (-31117861692396738872711577600) }, { argument := 31117850278473843264926515200, coefficient := (-31117850278473843264926515200) }, { argument := 797787554711401744721510400, coefficient := (-797787554711401744721510400) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 16668806499962647681041432576, coefficient := (-16668806499962647681041432576) }, { argument := 158183650980733449463488577536, coefficient := (-158183650980733449463488577536) }, { argument := 16668817932332287362536046592, coefficient := (-16668817932332287362536046592) }, { argument := 141029711875110917558501376, coefficient := (-141029711875110917558501376) }, { argument := 20609413543486277338267648000, coefficient := (-20609413543486277338267648000) }, { argument := 803878093720249087545049088000, coefficient := (-803878093720249087545049088000) }, { argument := 803877798860574284343934976000, coefficient := (-803877798860574284343934976000) }, { argument := 20609511830044545071972352000, coefficient := (-20609511830044545071972352000) }, { argument := 6631800546494599191066574848, coefficient := (-6631800546494599191066574848) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
