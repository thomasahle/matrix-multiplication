import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-146737345168091369850538872012800)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    489321, 15214141, 14710211, 15214141, 14710211, 18385047,
    2317101281, 2236650271, 2317101281, 2236650271, 79806808847, 395632465,
    451489959537, 223138315, 35308085, 891860225, 372873025, 79948366607,
    395632465, 34755125, 36767313, 94940008835, 91728888445, 94940008835,
    91728888445, 6414078885105, 21635834031, 32988601119119, 9429151221, 1809595851,
    37658577663, 18858698943, 6414188985585, 21635834031, 1809165771, 375,
    7515, 12615, 12105, 375, 12105, 8085,
    195, 7515, 45, 709222409863, 57263453428089, 375,
    3525, 41625, 2925, 28631720920203, 41625, 375,
    2925, 2925, 2925, 2925, 2925, 354616998773,
    3525, 3525, 70641, 118581
  ]
def negativeCoefficients : Array ℕ := #[
    9243012359057030662443761664, 140325682664165755666300928, 135677748793633528493375488, 140325682664165755666300928, 135677748793633528493375488, 347283718955132488508504014848,
    21371487161735780235684610048, 20629457565765056298607443968, 21371487161735780235684610048, 20629457565765056298607443968, 359417914584977603519578112, 912266353638231449985351680,
    4066660027064707033495240704, 1029043847460946286749941760, 40707450482986444610600960, 1028244832506001080555929600, 859786658020612935306444800, 360055434060165005623427072,
    912266353638231449985351680, 40069931007799042506752000, 347257453152754767541825437696, 218916755666871090205866065920, 211512416163846039689379184640, 218916755666871090205866065920,
    211512416163846039689379184640, 28886443276883844426450862080, 49888836648889086157900480512, 297134903415076511457684226048, 43484284851523233154842230784, 2086321971265227673961496576,
    43417384020579759127252697088, 43485199120582229393707892736, 28886939125364545739198300160, 49888836648889086157900480512, 2085826122784526361214058496, 14167099448608935641088000,
    283908672950123070247403520, 476581225451204594966200320, 457313970201096442494320640, 14167099448608935641088000, 457313970201096442494320640, 305442664112008652421857280,
    14733783426553293066731520, 283908672950123070247403520, 13600415470664578215444480, 399256722597726498383200256, 32236458440086171520512032768, 14167099448608935641088000,
    16646341852115499378278400, 196568504849448982020096000, 442013502796598792001945600, 32236451916800566409583132672, 196568504849448982020096000, 14167099448608935641088000,
    13812921962393712250060800, 13812921962393712250060800, 13812921962393712250060800, 442013502796598792001945600, 13812921962393712250060800, 399263245883331609312100352,
    16646341852115499378278400, 16646341852115499378278400, 333592690716394607540699136, 559982939905165399085285376
  ]
def negativeScales : Array ℕ := #[
    18, 23, 23, 23, 23, 24,
    31, 31, 31, 31, 36, 28,
    38, 27, 25, 29, 28, 36,
    28, 25, 25, 36, 36, 36,
    36, 42, 34, 44, 33, 30,
    35, 34, 42, 34, 30, 8,
    12, 13, 13, 8, 13, 12,
    7, 12, 5, 39, 45, 8,
    11, 15, 11, 44, 15, 8,
    11, 11, 11, 11, 11, 38,
    11, 11, 16, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18900421678521933, 23858909546942462, 23810314605446062, 23858909546942462, 23810314605446062, 24132029528899619,
    31109673960080655, 31058692544116635, 31109673960080655, 31058692544116635, 36215792786433435, 28559585575422063,
    38715902948543658, 27733363018755179, 25073495240168192, 29732242383633575, 28474109190143570, 36218349507756805,
    28559585575422063, 25050722397930013, 25131920410695040, 36466297132896479, 36416657106389584, 36466297132896479,
    36416657106389584, 42544379235873048, 34332703684571977, 44907032840237052, 33134480764402396, 30753020380892406,
    35132259460315751, 34134511097143887, 42544404000154260, 34332703684571977, 30752677460106706, 8550746785384604,
    12875557391602924, 13622852585874176, 13563315458888280, 8550746785384604, 13563315458888280, 12981032075801390,
    7607330313756529, 12875557391602924, 5491853096329881, 39367447166697285, 45702679912216589, 8550746785384604,
    11783407542632370, 15345162651733350, 11514220909358563, 44702679620276556, 15345162651733350, 8550746785384604,
    11514220909358563, 11514220909358563, 11514220909358563, 11514220909358563, 11514220909358563, 38367470738084763,
    11783407542632370, 11783407542632370, 16108218145594003, 16855513344577571
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
noncomputable def negativeCeiling : ℝ := 943871793 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9243012359057030662443761664, coefficient := (-9243012359057030662443761664) }, { argument := 140325682664165755666300928, coefficient := (-140325682664165755666300928) }, { argument := 135677748793633528493375488, coefficient := (-135677748793633528493375488) }, { argument := 140325682664165755666300928, coefficient := (-140325682664165755666300928) }, { argument := 135677748793633528493375488, coefficient := (-135677748793633528493375488) }, { argument := 347283718955132488508504014848, coefficient := (-347283718955132488508504014848) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 359417914584977603519578112, coefficient := (-359417914584977603519578112) }, { argument := 912266353638231449985351680, coefficient := (-912266353638231449985351680) }, { argument := 4066660027064707033495240704, coefficient := (-4066660027064707033495240704) }, { argument := 1029043847460946286749941760, coefficient := (-1029043847460946286749941760) }, { argument := 40707450482986444610600960, coefficient := (-40707450482986444610600960) }, { argument := 1028244832506001080555929600, coefficient := (-1028244832506001080555929600) }, { argument := 859786658020612935306444800, coefficient := (-859786658020612935306444800) }, { argument := 360055434060165005623427072, coefficient := (-360055434060165005623427072) }, { argument := 912266353638231449985351680, coefficient := (-912266353638231449985351680) }, { argument := 40069931007799042506752000, coefficient := (-40069931007799042506752000) }, { argument := 347257453152754767541825437696, coefficient := (-347257453152754767541825437696) }, { argument := 218916755666871090205866065920, coefficient := (-218916755666871090205866065920) }, { argument := 211512416163846039689379184640, coefficient := (-211512416163846039689379184640) }, { argument := 218916755666871090205866065920, coefficient := (-218916755666871090205866065920) }, { argument := 211512416163846039689379184640, coefficient := (-211512416163846039689379184640) }, { argument := 28886443276883844426450862080, coefficient := (-28886443276883844426450862080) }, { argument := 49888836648889086157900480512, coefficient := (-49888836648889086157900480512) }, { argument := 297134903415076511457684226048, coefficient := (-297134903415076511457684226048) }, { argument := 43484284851523233154842230784, coefficient := (-43484284851523233154842230784) }, { argument := 2086321971265227673961496576, coefficient := (-2086321971265227673961496576) }, { argument := 43417384020579759127252697088, coefficient := (-43417384020579759127252697088) }, { argument := 43485199120582229393707892736, coefficient := (-43485199120582229393707892736) }, { argument := 28886939125364545739198300160, coefficient := (-28886939125364545739198300160) }, { argument := 49888836648889086157900480512, coefficient := (-49888836648889086157900480512) }, { argument := 2085826122784526361214058496, coefficient := (-2085826122784526361214058496) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 476581225451204594966200320, coefficient := (-476581225451204594966200320) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 457313970201096442494320640, coefficient := (-457313970201096442494320640) }, { argument := 305442664112008652421857280, coefficient := (-305442664112008652421857280) }, { argument := 14733783426553293066731520, coefficient := (-14733783426553293066731520) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 13600415470664578215444480, coefficient := (-13600415470664578215444480) }, { argument := 399256722597726498383200256, coefficient := (-399256722597726498383200256) }, { argument := 32236458440086171520512032768, coefficient := (-32236458440086171520512032768) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 32236451916800566409583132672, coefficient := (-32236451916800566409583132672) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 14167099448608935641088000, coefficient := (-14167099448608935641088000) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 13812921962393712250060800, coefficient := (-13812921962393712250060800) }, { argument := 399263245883331609312100352, coefficient := (-399263245883331609312100352) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 559982939905165399085285376, coefficient := (-559982939905165399085285376) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-57681343320582469709902997618688)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    113787, 3525, 113787, 75999, 1833, 70641,
    423, 41625, 834165, 1400265, 1343655, 41625,
    1343655, 897435, 21645, 834165, 4995, 2925,
    58617, 98397, 94419, 2925, 94419, 63063,
    1521, 58617, 351, 395632465, 21635834031, 7515,
    70641, 834165, 58617, 10817920911, 834165, 7515,
    58617, 58617, 58617, 58617, 58617, 197812337,
    70641, 981423, 2317101281, 2236650271, 2317101281, 2236650271,
    3207038808051, 10817920911, 16494297829005, 4714577301, 904798251, 18829295583,
    9429352863, 3207093858291, 10817920911, 904583211, 41625, 834165,
    1400265, 1343655, 41625, 1343655
  ]
def negativeCoefficients : Array ℕ := #[
    537343914986288319930826752, 16646341852115499378278400, 537343914986288319930826752, 358895130331610166595682304, 17312195526200119353409536, 333592690716394607540699136,
    15980488178030879403147264, 196568504849448982020096000, 3939232837182957599682723840, 6612564503135463755156029440, 6345231336540213139608698880, 196568504849448982020096000,
    6345231336540213139608698880, 4238016964554120052353269760, 204431245043426941300899840, 3939232837182957599682723840, 188705764655471022739292160, 442013502796598792001945600,
    8857950596043839791718989824, 14869334234077583362945449984, 14268195870274209005822803968, 442013502796598792001945600, 14268195870274209005822803968, 9529811120294669955561947136,
    459694042908462743682023424, 8857950596043839791718989824, 424332962684734840321867776, 912266353638231449985351680, 49888836648889086157900480512, 283908672950123070247403520,
    333592690716394607540699136, 3939232837182957599682723840, 8857950596043839791718989824, 49888854613711970941790060544, 3939232837182957599682723840, 283908672950123070247403520,
    276810956126369993491218432, 276810956126369993491218432, 276810956126369993491218432, 8857950596043839791718989824, 276810956126369993491218432, 912248388815346666095771648,
    333592690716394607540699136, 9269278161434751629122338816, 21371487161735780235684610048, 20629457565765056298607443968, 21371487161735780235684610048, 20629457565765056298607443968,
    28886437561802406494409326592, 49888854613711970941790060544, 297134854225779596598360145920, 43484300443633661457840734208, 2086322721817127173018877952, 43417399588478835833507414016,
    43485214761115360890193969152, 28886933410283107807156764672, 49888854613711970941790060544, 2085826873336425860271439872, 196568504849448982020096000, 3939232837182957599682723840,
    6612564503135463755156029440, 6345231336540213139608698880, 196568504849448982020096000, 6345231336540213139608698880
  ]
def negativeScales : Array ℕ := #[
    16, 11, 16, 16, 10, 16,
    8, 15, 19, 20, 20, 15,
    20, 19, 14, 19, 12, 11,
    15, 16, 16, 11, 16, 15,
    10, 15, 8, 28, 34, 12,
    16, 19, 15, 33, 19, 12,
    15, 15, 15, 15, 15, 27,
    16, 19, 31, 31, 31, 31,
    41, 33, 43, 32, 29, 34,
    33, 41, 33, 29, 15, 19,
    20, 20, 15, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16795976216271593, 11783407542632370, 16795976216271593, 16213692815151300, 10839991071969009, 16108218145594003,
    8724513853247462, 15345162651733350, 19669973255188965, 20417268452213782, 20357731325236406, 15345162651733350,
    20357731325236406, 19775447925099447, 14401746180099724, 19669973255188965, 12286268962679781, 11514220909358563,
    15839031514181448, 16586326709842405, 16526789582861833, 11514220909358563, 16526789582861833, 15944506191833593,
    10570804437726965, 15839031514181448, 8455327220304618, 28559585575422063, 34332703684571977, 12875557391602924,
    16108218145594003, 19669973255188965, 15839031514181448, 33332704204082112, 19669973255188965, 12875557391602924,
    15839031514181448, 15839031514181448, 15839031514181448, 15839031514181448, 15839031514181448, 27559557164842213,
    16108218145594003, 19904515561049696, 31109673960080655, 31058692544116635, 31109673960080655, 31058692544116635,
    41544378950440868, 33332704204082112, 43907032601405578, 32134481281707818, 29753020899900176, 34132259977613771,
    33134511616044938, 41544403714726980, 33332704204082112, 29752677979237856, 15345162651733350, 19669973255188965,
    20417268452213782, 20357731325236406, 15345162651733350, 20357731325236406
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
noncomputable def negativeCeiling : ℝ := 387953071 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 358895130331610166595682304, coefficient := (-358895130331610166595682304) }, { argument := 17312195526200119353409536, coefficient := (-17312195526200119353409536) }, { argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 15980488178030879403147264, coefficient := (-15980488178030879403147264) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 6612564503135463755156029440, coefficient := (-6612564503135463755156029440) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }, { argument := 4238016964554120052353269760, coefficient := (-4238016964554120052353269760) }, { argument := 204431245043426941300899840, coefficient := (-204431245043426941300899840) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 188705764655471022739292160, coefficient := (-188705764655471022739292160) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 14869334234077583362945449984, coefficient := (-14869334234077583362945449984) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 442013502796598792001945600, coefficient := (-442013502796598792001945600) }, { argument := 14268195870274209005822803968, coefficient := (-14268195870274209005822803968) }, { argument := 9529811120294669955561947136, coefficient := (-9529811120294669955561947136) }, { argument := 459694042908462743682023424, coefficient := (-459694042908462743682023424) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 424332962684734840321867776, coefficient := (-424332962684734840321867776) }, { argument := 912266353638231449985351680, coefficient := (-912266353638231449985351680) }, { argument := 49888836648889086157900480512, coefficient := (-49888836648889086157900480512) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 49888854613711970941790060544, coefficient := (-49888854613711970941790060544) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 912248388815346666095771648, coefficient := (-912248388815346666095771648) }, { argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 9269278161434751629122338816, coefficient := (-9269278161434751629122338816) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 28886437561802406494409326592, coefficient := (-28886437561802406494409326592) }, { argument := 49888854613711970941790060544, coefficient := (-49888854613711970941790060544) }, { argument := 297134854225779596598360145920, coefficient := (-297134854225779596598360145920) }, { argument := 43484300443633661457840734208, coefficient := (-43484300443633661457840734208) }, { argument := 2086322721817127173018877952, coefficient := (-2086322721817127173018877952) }, { argument := 43417399588478835833507414016, coefficient := (-43417399588478835833507414016) }, { argument := 43485214761115360890193969152, coefficient := (-43485214761115360890193969152) }, { argument := 28886933410283107807156764672, coefficient := (-28886933410283107807156764672) }, { argument := 49888854613711970941790060544, coefficient := (-49888854613711970941790060544) }, { argument := 2085826873336425860271439872, coefficient := (-2085826873336425860271439872) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 6612564503135463755156029440, coefficient := (-6612564503135463755156029440) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }, { argument := 196568504849448982020096000, coefficient := (-196568504849448982020096000) }, { argument := 6345231336540213139608698880, coefficient := (-6345231336540213139608698880) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
