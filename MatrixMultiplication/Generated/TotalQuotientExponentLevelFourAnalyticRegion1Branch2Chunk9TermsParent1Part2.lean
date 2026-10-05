import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 9, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 251834797634507126878433521434624
def positiveArguments : Array ℕ := #[
    19, 3, 1, 1, 1, 1
  ]
def positiveCoefficients : Array ℕ := #[
    3010670175542044828554670112768, 475368975085586025561263702016, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def positiveScales : Array ℕ := #[
    4, 1, 0, 0, 0, 0
  ]
def negativeArguments : Array ℕ := #[
    55990701, 34976527, 67475973, 67475973, 326788603, 67475973,
    128013921, 10764593567, 5382295485, 64008259, 7057, 372257,
    48685, 13967813, 1605, 3745, 48685, 48685,
    1605, 600805, 24075, 372257, 48685, 3745,
    24075, 3745, 48685, 48685, 15183, 10696581,
    899467387, 449733585, 5348399, 6827, 370325, 44499,
    13967261, 1467, 3423, 44499, 44499, 1467,
    549147, 22005, 370325, 44499, 3423, 22005,
    3423, 44499, 44499, 14631, 41469, 1531395,
    12251157, 331755, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    258211532963648366343880704, 322601521078096061127458816, 311178001263883928670830592, 311178001263883928670830592, 3014092862873036700174516224, 311178001263883928670830592,
    590360009639768179379011584, 49642925646987303288012013568, 49642913670438713432085626880, 590371986188358035305398272, 66651480539222172546105344, 7031735919254422073259327488,
    919633648874034708915159040, 65961131950190907721250766848, 485081485120369956350853120, 35370524956693642650583040, 919633648874034708915159040, 919633648874034708915159040,
    485081485120369956350853120, 11348885578961988770458501120, 909527784600693668157849600, 7031735919254422073259327488, 919633648874034708915159040, 35370524956693642650583040,
    909527784600693668157849600, 35370524956693642650583040, 919633648874034708915159040, 919633648874034708915159040, 71699690309409823279546368, 24664636521338023666778112,
    2074030586329658223623143424, 2074030085961725224251555840, 24665136889271023038365696, 64479191957102135747805184, 6995241471074805455047884800, 840562344484865369457033216,
    65958525203892363677092806656, 443373544343665249823490048, 32329320941725591132962816, 840562344484865369457033216, 840562344484865369457033216, 443373544343665249823490048,
    10373093547873668240662069248, 831325395644372343419043840, 6995241471074805455047884800, 840562344484865369457033216, 32329320941725591132962816, 831325395644372343419043840,
    32329320941725591132962816, 840562344484865369457033216, 840562344484865369457033216, 69092944010865779121586176, 3133309050849941077868150784, 115708934720546565312447774720,
    115708906386347668094576492544, 3133337385048838295739432960, 475368975085586025561263702016, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    25, 25, 26, 26, 28, 26,
    26, 33, 32, 25, 12, 18,
    15, 23, 10, 11, 15, 15,
    10, 19, 14, 18, 15, 11,
    14, 11, 15, 15, 13, 23,
    29, 28, 22, 12, 18, 15,
    23, 10, 11, 15, 15, 10,
    19, 14, 18, 15, 11, 14,
    11, 15, 15, 13, 15, 20,
    23, 18, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4247927513443585, 1584962500720924, 0, 0, 0, 0
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25738683907000526, 25059883707941457, 26007870539640660, 26007870539640660, 28283782428377789, 26007870539640660,
    26931725472780020, 33325574798342279, 32325574450286456, 25931754740233760, 12784839295125895, 18505939452244746,
    15571189721489702, 23735602813894843, 10648357582030099, 11870750005906678, 15571189721489702, 15571189721489702,
    10648357582030099, 19196537293689111, 14555248177619742, 18505939452244746, 15571189721489702, 11870750005906678,
    14555248177619742, 11870750005906678, 15571189721489702, 15571189721489702, 13890169263387826, 23350646398915330,
    29744495732307649, 28744495384251824, 22350675666365216, 12737036036709178, 18498432421080211, 15441485295150964,
    23735545798283173, 10518653155673890, 11741045577194516, 15441485295150964, 15441485295150964, 10518653155673890,
    19066832867352835, 14425543751281927, 18498432421080211, 15441485295150964, 11741045577194516, 14425543751281927,
    11741045577194516, 15441485295150964, 15441485295150964, 13836740759098915, 15339745637489356, 20546415021360256,
    23546414668080595, 18339758683576654, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 40753131 / 250000000000
noncomputable def negativeCeiling : ℝ := 166156619 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 322601521078096061127458816, coefficient := (-322601521078096061127458816) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 3014092862873036700174516224, coefficient := (-3014092862873036700174516224) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 590360009639768179379011584, coefficient := (-590360009639768179379011584) }, { argument := 49642925646987303288012013568, coefficient := (-49642925646987303288012013568) }, { argument := 49642913670438713432085626880, coefficient := (-49642913670438713432085626880) }, { argument := 590371986188358035305398272, coefficient := (-590371986188358035305398272) }, { argument := 66651480539222172546105344, coefficient := (-66651480539222172546105344) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 65961131950190907721250766848, coefficient := (-65961131950190907721250766848) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 11348885578961988770458501120, coefficient := (-11348885578961988770458501120) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 71699690309409823279546368, coefficient := (-71699690309409823279546368) }, { argument := 24664636521338023666778112, coefficient := (-24664636521338023666778112) }, { argument := 2074030586329658223623143424, coefficient := (-2074030586329658223623143424) }, { argument := 2074030085961725224251555840, coefficient := (-2074030085961725224251555840) }, { argument := 24665136889271023038365696, coefficient := (-24665136889271023038365696) }, { argument := 64479191957102135747805184, coefficient := (-64479191957102135747805184) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 65958525203892363677092806656, coefficient := (-65958525203892363677092806656) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 10373093547873668240662069248, coefficient := (-10373093547873668240662069248) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 69092944010865779121586176, coefficient := (-69092944010865779121586176) }, { argument := 3133309050849941077868150784, coefficient := (-3133309050849941077868150784) }, { argument := 115708934720546565312447774720, coefficient := (-115708934720546565312447774720) }, { argument := 115708906386347668094576492544, coefficient := (-115708906386347668094576492544) }, { argument := 3133337385048838295739432960, coefficient := (-3133337385048838295739432960) }, { argument := 3010670175542044828554670112768, coefficient := 3010670175542044828554670112768 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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
def constantNumerator : ℤ := (-69893222680305173269512296857600)
def positiveArguments : Array ℕ := #[
    217, 2597, 3885, 1127, 217, 4501,
    2261, 217, 2597, 217, 45, 35,
    5, 47, 555, 39, 35, 555,
    5, 39, 39, 39, 39, 39,
    45, 47, 5, 21, 91, 3,
    3, 7, 91, 91, 3, 1123,
    45, 21, 91, 7, 45, 7,
    91, 91, 3, 41469, 1531395, 12251157,
    331755, 2191, 349787, 13961393, 349787, 8763,
    345051, 29015077, 14507535, 172529
  ]
def positiveCoefficients : Array ℕ := #[
    8394780891403984989159686144, 200933142626508285869564100608, 150293657894490698999471800320, 174394803034327946226414125056, 8394780891403984989159686144, 174124003650734269291279941632,
    174936401801515300096682491904, 8394780891403984989159686144, 200933142626508285869564100608, 8394780891403984989159686144, 6963412720980264046307573760, 5415987671873538702683668480,
    6189700196426901374495621120, 7272897730801609115032354816, 85882090225423256571126743040, 193118646128519322884263378944, 5415987671873538702683668480, 85882090225423256571126743040,
    6189700196426901374495621120, 6034957691516228840133230592, 6034957691516228840133230592, 6034957691516228840133230592, 193118646128519322884263378944, 6034957691516228840133230592,
    6963412720980264046307573760, 7272897730801609115032354816, 193428131138340667952988160, 3249592603124123221610201088, 7040783973435600313488769024, 232113757366008801543585792,
    3713820117856140824697372672, 270799383593676935134183424, 7040783973435600313488769024, 7040783973435600313488769024, 3713820117856140824697372672, 86887916507342628044482281472,
    6963412720980264046307573760, 3249592603124123221610201088, 7040783973435600313488769024, 270799383593676935134183424, 6963412720980264046307573760, 270799383593676935134183424,
    7040783973435600313488769024, 7040783973435600313488769024, 232113757366008801543585792, 6266618101699882155736301568, 231417869441093130624895549440, 231417812772695336189152985088,
    6266674770097676591478865920, 331094558846956565222653952, 52858316958192786891618648064, 527446514858967076791830708224, 52858316958192786891618648064, 331056779915093608060944384,
    6517829109122615802524073984, 548079308490727747352283578368, 548079176264466227002217594880, 6517961335384136152590057472
  ]
def positiveScales : Array ℕ := #[
    7, 11, 11, 10, 7, 12,
    11, 7, 11, 7, 5, 5,
    2, 5, 9, 5, 5, 9,
    2, 5, 5, 5, 5, 5,
    5, 5, 2, 4, 6, 1,
    1, 2, 6, 6, 1, 10,
    5, 4, 6, 2, 5, 2,
    6, 6, 1, 15, 20, 23,
    18, 11, 18, 23, 18, 13,
    18, 24, 23, 17
  ]
def negativeArguments : Array ℕ := #[
    7, 1, 1, 3, 1, 7
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 633825300114114700748351602688, 158456325028528675187087900672, 475368975085586025561263702016, 633825300114114700748351602688, 1109194275199700726309615304704
  ]
def negativeScales : Array ℕ := #[
    2, 0, 0, 1, 0, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7761551232426566, 11342630298678407, 11923698882884927, 10138271800172220, 7761551232426566, 12136029849385551,
    11142745276751528, 7761551232426566, 11342630298678407, 7761551232426566, 5491853096329661, 5129283016944966,
    2321928094887362, 5554588851677541, 9116343961237468, 5285402218862248, 5129283016944966, 9116343961237468,
    2321928094887362, 5285402218862248, 5285402218862248, 5285402218862248, 5285402218862248, 5285402218862248,
    5491853096329661, 5554588851677541, 2321928094887362, 4392317422778759, 6507794640198673, 1584962500720924,
    1584962500720924, 2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924, 10133142212400601,
    5491853096329661, 4392317422778759, 6507794640198673, 2807354922011143, 5491853096329661, 2807354922011143,
    6507794640198673, 6507794640198673, 1584962500720924, 15339745637489354, 20546415021358988, 23546414668079327,
    18339758683576652, 11097373768990222, 18416117146246269, 23734939558036408, 18416117146246269, 13097209143550334,
    18396450088528453, 24790299421688666, 23790299073632843, 17396479355978338
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 0, 0, 1584962500724866, 0, 2807354922807594
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 167174449 / 200000000000
noncomputable def negativeCeiling : ℝ := 84033693 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 150293657894490698999471800320, coefficient := 150293657894490698999471800320 }, { argument := 174394803034327946226414125056, coefficient := 174394803034327946226414125056 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 174124003650734269291279941632, coefficient := 174124003650734269291279941632 }, { argument := 174936401801515300096682491904, coefficient := 174936401801515300096682491904 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 7272897730801609115032354816, coefficient := 7272897730801609115032354816 }, { argument := 85882090225423256571126743040, coefficient := 85882090225423256571126743040 }, { argument := 193118646128519322884263378944, coefficient := 193118646128519322884263378944 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 85882090225423256571126743040, coefficient := 85882090225423256571126743040 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 6034957691516228840133230592, coefficient := 6034957691516228840133230592 }, { argument := 6034957691516228840133230592, coefficient := 6034957691516228840133230592 }, { argument := 6034957691516228840133230592, coefficient := 6034957691516228840133230592 }, { argument := 193118646128519322884263378944, coefficient := 193118646128519322884263378944 }, { argument := 6034957691516228840133230592, coefficient := 6034957691516228840133230592 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 7272897730801609115032354816, coefficient := 7272897730801609115032354816 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 86887916507342628044482281472, coefficient := 86887916507342628044482281472 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 6266618101699882155736301568, coefficient := 6266618101699882155736301568 }, { argument := 231417869441093130624895549440, coefficient := 231417869441093130624895549440 }, { argument := 231417812772695336189152985088, coefficient := 231417812772695336189152985088 }, { argument := 6266674770097676591478865920, coefficient := 6266674770097676591478865920 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 331094558846956565222653952, coefficient := 331094558846956565222653952 }, { argument := 52858316958192786891618648064, coefficient := 52858316958192786891618648064 }, { argument := 527446514858967076791830708224, coefficient := 527446514858967076791830708224 }, { argument := 52858316958192786891618648064, coefficient := 52858316958192786891618648064 }, { argument := 331056779915093608060944384, coefficient := 331056779915093608060944384 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 6517829109122615802524073984, coefficient := 6517829109122615802524073984 }, { argument := 548079308490727747352283578368, coefficient := 548079308490727747352283578368 }, { argument := 548079176264466227002217594880, coefficient := 548079176264466227002217594880 }, { argument := 6517961335384136152590057472, coefficient := 6517961335384136152590057472 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }] }

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

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-16429476805017335975915647139840)
def positiveArguments : Array ℕ := #[
    1435659, 6952949, 1435659, 535, 489, 535,
    489
  ]
def positiveCoefficients : Array ℕ := #[
    54237663539441215822796685312, 525349973035232269102758232064, 54237663539441215822796685312, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240,
    37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    20, 22, 20, 9, 8, 9,
    8
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    20453281687963018, 22729193576691355, 20453281687963018, 9063395081288509, 8933690654464738, 9063395081288509,
    8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 93803593 / 500000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 54237663539441215822796685312, coefficient := 54237663539441215822796685312 }, { argument := 525349973035232269102758232064, coefficient := 525349973035232269102758232064 }, { argument := 54237663539441215822796685312, coefficient := 54237663539441215822796685312 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
