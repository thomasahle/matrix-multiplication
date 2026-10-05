import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-27412570062194379906679132127232)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    94419, 63063, 1521, 58617, 351, 372873025,
    18858698943, 8085, 75999, 897435, 63063, 9429352863,
    897435, 8085, 63063, 63063, 63063, 63063,
    63063, 186433121, 75999, 14710211, 2236650271, 91728888445,
    2236650271, 58838399, 60853889, 58838399, 60853889, 58838399,
    39904038925, 197812337, 225747710323, 111567467, 17653717, 445923361,
    186433121, 39974817805, 197812337, 17377237, 710354871943, 57264334231929,
    195, 1833, 21645, 1521, 28632161322123, 21645,
    195, 1521, 1521, 1521, 1521, 1521,
    355183229813, 1833, 3525, 70641, 118581, 113787,
    3525, 113787, 75999, 1833
  ]
def negativeCoefficients : Array ℕ := #[
    445881120946069031431962624, 297806597509208436111310848, 14365438840889460740063232, 276810956126369993491218432, 13260405083897963760058368, 859786658020612935306444800,
    43485199120582229393707892736, 305442664112008652421857280, 358895130331610166595682304, 4238016964554120052353269760, 9529811120294669955561947136, 43485214761115360890193969152,
    4238016964554120052353269760, 305442664112008652421857280, 297806597509208436111310848, 297806597509208436111310848, 297806597509208436111310848, 9529811120294669955561947136,
    297806597509208436111310848, 859771017487481438820368384, 358895130331610166595682304, 135677748793633528493375488, 20629457565765056298607443968, 211512416163846039689379184640,
    20629457565765056298607443968, 135672111007476001011662848, 140319514534116109034979328, 135672111007476001011662848, 140319514534116109034979328, 135672111007476001011662848,
    359423629666415535561113600, 912248388815346666095771648, 4066709216361621892819320832, 1029028255350517983751438336, 40706699931086945553219584, 1028229264606924374301212672,
    859771017487481438820368384, 360061149141602937664962560, 912248388815346666095771648, 40069180455899543449370624, 399894242072913900487049216, 32236954288566872833259470848,
    14733783426553293066731520, 17312195526200119353409536, 204431245043426941300899840, 459694042908462743682023424, 32236947765281267722330570752, 204431245043426941300899840,
    14733783426553293066731520, 14365438840889460740063232, 14365438840889460740063232, 14365438840889460740063232, 459694042908462743682023424, 14365438840889460740063232,
    399900765358519011415949312, 17312195526200119353409536, 16646341852115499378278400, 333592690716394607540699136, 559982939905165399085285376, 537343914986288319930826752,
    16646341852115499378278400, 537343914986288319930826752, 358895130331610166595682304, 17312195526200119353409536
  ]
def negativeScales : Array ℕ := #[
    16, 15, 10, 15, 8, 28,
    34, 12, 16, 19, 15, 33,
    19, 12, 15, 15, 15, 15,
    15, 27, 16, 23, 31, 36,
    31, 25, 25, 25, 25, 25,
    35, 27, 37, 26, 24, 28,
    27, 35, 27, 24, 39, 45,
    7, 10, 14, 10, 44, 14,
    7, 10, 10, 10, 10, 10,
    38, 10, 11, 16, 16, 16,
    11, 16, 16, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16526789582861833, 15944506191833593, 10570804437726965, 15839031514181448, 8455327220304618, 28474109190143570,
    34134511097143887, 12981032075801390, 16213692815151300, 19775447925099447, 15944506191833593, 33134511616044938,
    19775447925099447, 12981032075801390, 15944506191833593, 15944506191833593, 15944506191833593, 15944506191833593,
    15944506191833593, 27474082945580904, 16213692815151300, 23810314605446062, 31058692544116635, 36416657106389584,
    31058692544116635, 25810254656225758, 25858846130706811, 25810254656225758, 25858846130706811, 25810254656225758,
    35215815726453290, 27559557164842213, 37715920398914536, 26733341158820885, 24073468639939660, 28732220540683155,
    27474082945580904, 35218372407159044, 27559557164842213, 24050695374483319, 39369748975544655, 45702702103011684,
    7607330313756529, 10839991071969009, 14401746180099724, 10570804437726965, 44702701811076140, 14401746180099724,
    7607330313756529, 10570804437726965, 10570804437726965, 10570804437726965, 10570804437726965, 10570804437726965,
    38369772509354458, 10839991071969009, 11783407542632370, 16108218145594003, 16855513344577571, 16795976216271593,
    11783407542632370, 16795976216271593, 16213692815151300, 10839991071969009
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
noncomputable def negativeCeiling : ℝ := 9520319 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 445881120946069031431962624, coefficient := (-445881120946069031431962624) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 859786658020612935306444800, coefficient := (-859786658020612935306444800) }, { argument := 43485199120582229393707892736, coefficient := (-43485199120582229393707892736) }, { argument := 305442664112008652421857280, coefficient := (-305442664112008652421857280) }, { argument := 358895130331610166595682304, coefficient := (-358895130331610166595682304) }, { argument := 4238016964554120052353269760, coefficient := (-4238016964554120052353269760) }, { argument := 9529811120294669955561947136, coefficient := (-9529811120294669955561947136) }, { argument := 43485214761115360890193969152, coefficient := (-43485214761115360890193969152) }, { argument := 4238016964554120052353269760, coefficient := (-4238016964554120052353269760) }, { argument := 305442664112008652421857280, coefficient := (-305442664112008652421857280) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 9529811120294669955561947136, coefficient := (-9529811120294669955561947136) }, { argument := 297806597509208436111310848, coefficient := (-297806597509208436111310848) }, { argument := 859771017487481438820368384, coefficient := (-859771017487481438820368384) }, { argument := 358895130331610166595682304, coefficient := (-358895130331610166595682304) }, { argument := 135677748793633528493375488, coefficient := (-135677748793633528493375488) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 211512416163846039689379184640, coefficient := (-211512416163846039689379184640) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 135672111007476001011662848, coefficient := (-135672111007476001011662848) }, { argument := 140319514534116109034979328, coefficient := (-140319514534116109034979328) }, { argument := 135672111007476001011662848, coefficient := (-135672111007476001011662848) }, { argument := 140319514534116109034979328, coefficient := (-140319514534116109034979328) }, { argument := 135672111007476001011662848, coefficient := (-135672111007476001011662848) }, { argument := 359423629666415535561113600, coefficient := (-359423629666415535561113600) }, { argument := 912248388815346666095771648, coefficient := (-912248388815346666095771648) }, { argument := 4066709216361621892819320832, coefficient := (-4066709216361621892819320832) }, { argument := 1029028255350517983751438336, coefficient := (-1029028255350517983751438336) }, { argument := 40706699931086945553219584, coefficient := (-40706699931086945553219584) }, { argument := 1028229264606924374301212672, coefficient := (-1028229264606924374301212672) }, { argument := 859771017487481438820368384, coefficient := (-859771017487481438820368384) }, { argument := 360061149141602937664962560, coefficient := (-360061149141602937664962560) }, { argument := 912248388815346666095771648, coefficient := (-912248388815346666095771648) }, { argument := 40069180455899543449370624, coefficient := (-40069180455899543449370624) }, { argument := 399894242072913900487049216, coefficient := (-399894242072913900487049216) }, { argument := 32236954288566872833259470848, coefficient := (-32236954288566872833259470848) }, { argument := 14733783426553293066731520, coefficient := (-14733783426553293066731520) }, { argument := 17312195526200119353409536, coefficient := (-17312195526200119353409536) }, { argument := 204431245043426941300899840, coefficient := (-204431245043426941300899840) }, { argument := 459694042908462743682023424, coefficient := (-459694042908462743682023424) }, { argument := 32236947765281267722330570752, coefficient := (-32236947765281267722330570752) }, { argument := 204431245043426941300899840, coefficient := (-204431245043426941300899840) }, { argument := 14733783426553293066731520, coefficient := (-14733783426553293066731520) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 459694042908462743682023424, coefficient := (-459694042908462743682023424) }, { argument := 14365438840889460740063232, coefficient := (-14365438840889460740063232) }, { argument := 399900765358519011415949312, coefficient := (-399900765358519011415949312) }, { argument := 17312195526200119353409536, coefficient := (-17312195526200119353409536) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 559982939905165399085285376, coefficient := (-559982939905165399085285376) }, { argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 16646341852115499378278400, coefficient := (-16646341852115499378278400) }, { argument := 537343914986288319930826752, coefficient := (-537343914986288319930826752) }, { argument := 358895130331610166595682304, coefficient := (-358895130331610166595682304) }, { argument := 17312195526200119353409536, coefficient := (-17312195526200119353409536) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 619695738851125425574460176465920
def positiveArguments : Array ℕ := #[
    5, 17, 1, 1, 1, 1,
    217, 2597, 3885, 1127, 217, 4501,
    2261, 217
  ]
def positiveCoefficients : Array ℕ := #[
    6338253001141147007483516026880, 1346878762742493739090247155712, 316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344,
    8394780891403984989159686144, 200933142626508285869564100608, 150293657894490698999471800320, 174394803034327946226414125056, 8394780891403984989159686144, 174124003650734269291279941632,
    174936401801515300096682491904, 8394780891403984989159686144
  ]
def positiveScales : Array ℕ := #[
    2, 4, 0, 0, 0, 0,
    7, 11, 11, 10, 7, 12,
    11, 7
  ]
def negativeArguments : Array ℕ := #[
    70641, 423, 395632465, 21635834031, 7515, 70641,
    834165, 58617, 10817920911, 834165, 7515, 58617,
    58617, 58617, 58617, 58617, 197812337, 70641,
    15214141, 2317101281, 94940008835, 2317101281, 60853889, 34755125,
    1809165771, 45, 423, 4995, 351, 904583211,
    4995, 45, 351, 351, 351, 351,
    351, 17377237, 423, 14710211, 2236650271, 91728888445,
    2236650271, 58838399, 54369, 2042783, 4085257, 109047,
    17, 1
  ]
def negativeCoefficients : Array ℕ := #[
    333592690716394607540699136, 15980488178030879403147264, 912266353638231449985351680, 49888836648889086157900480512, 283908672950123070247403520, 333592690716394607540699136,
    3939232837182957599682723840, 8857950596043839791718989824, 49888854613711970941790060544, 3939232837182957599682723840, 283908672950123070247403520, 276810956126369993491218432,
    276810956126369993491218432, 276810956126369993491218432, 8857950596043839791718989824, 276810956126369993491218432, 912248388815346666095771648, 333592690716394607540699136,
    140325682664165755666300928, 21371487161735780235684610048, 218916755666871090205866065920, 21371487161735780235684610048, 140319514534116109034979328, 40069931007799042506752000,
    2085826122784526361214058496, 13600415470664578215444480, 15980488178030879403147264, 188705764655471022739292160, 424332962684734840321867776, 2085826873336425860271439872,
    188705764655471022739292160, 13600415470664578215444480, 13260405083897963760058368, 13260405083897963760058368, 13260405083897963760058368, 424332962684734840321867776,
    13260405083897963760058368, 40069180455899543449370624, 15980488178030879403147264, 135677748793633528493375488, 20629457565765056298607443968, 211512416163846039689379184640,
    20629457565765056298607443968, 135672111007476001011662848, 8216010985828471699950010368, 308696639071228878674225790976, 308673291691337571148289277952, 8239358365719779225886523392,
    1346878762742493739090247155712, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    16, 8, 28, 34, 12, 16,
    19, 15, 33, 19, 12, 15,
    15, 15, 15, 15, 27, 16,
    23, 31, 36, 31, 25, 25,
    30, 5, 8, 12, 8, 29,
    12, 5, 8, 8, 8, 8,
    8, 24, 8, 23, 31, 36,
    31, 25, 15, 20, 21, 16,
    4, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 4087462841250339, 0, 0, 0, 0,
    7761551232426566, 11342630298678407, 11923698882884927, 10138271800172220, 7761551232426566, 12136029849385551,
    11142745276751528, 7761551232426566
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    16108218145594003, 8724513853247462, 28559585575422063, 34332703684571977, 12875557391602924, 16108218145594003,
    19669973255188965, 15839031514181448, 33332704204082112, 19669973255188965, 12875557391602924, 15839031514181448,
    15839031514181448, 15839031514181448, 15839031514181448, 15839031514181448, 27559557164842213, 16108218145594003,
    23858909546942462, 31109673960080655, 36466297132896479, 31109673960080655, 25858846130706811, 25050722397930013,
    30752677460106706, 5491853096329881, 8724513853247462, 12286268962679781, 8455327220304618, 29752677979237856,
    12286268962679781, 5491853096329881, 8455327220304618, 8455327220304618, 8455327220304618, 8455327220304618,
    8455327220304618, 24050695374483319, 8724513853247462, 23810314605446062, 31058692544116635, 36416657106389584,
    31058692544116635, 25810254656225758, 15730496672824826, 20962104540226991, 21961995421999232, 16734590555032519,
    4087462841250340, 0
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 50
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
noncomputable def positiveFloor : ℝ := 182478423 / 500000000000
noncomputable def negativeCeiling : ℝ := 249031617 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 15980488178030879403147264, coefficient := (-15980488178030879403147264) }, { argument := 912266353638231449985351680, coefficient := (-912266353638231449985351680) }, { argument := 49888836648889086157900480512, coefficient := (-49888836648889086157900480512) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 49888854613711970941790060544, coefficient := (-49888854613711970941790060544) }, { argument := 3939232837182957599682723840, coefficient := (-3939232837182957599682723840) }, { argument := 283908672950123070247403520, coefficient := (-283908672950123070247403520) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 8857950596043839791718989824, coefficient := (-8857950596043839791718989824) }, { argument := 276810956126369993491218432, coefficient := (-276810956126369993491218432) }, { argument := 912248388815346666095771648, coefficient := (-912248388815346666095771648) }, { argument := 333592690716394607540699136, coefficient := (-333592690716394607540699136) }, { argument := 140325682664165755666300928, coefficient := (-140325682664165755666300928) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 218916755666871090205866065920, coefficient := (-218916755666871090205866065920) }, { argument := 21371487161735780235684610048, coefficient := (-21371487161735780235684610048) }, { argument := 140319514534116109034979328, coefficient := (-140319514534116109034979328) }, { argument := 40069931007799042506752000, coefficient := (-40069931007799042506752000) }, { argument := 2085826122784526361214058496, coefficient := (-2085826122784526361214058496) }, { argument := 13600415470664578215444480, coefficient := (-13600415470664578215444480) }, { argument := 15980488178030879403147264, coefficient := (-15980488178030879403147264) }, { argument := 188705764655471022739292160, coefficient := (-188705764655471022739292160) }, { argument := 424332962684734840321867776, coefficient := (-424332962684734840321867776) }, { argument := 2085826873336425860271439872, coefficient := (-2085826873336425860271439872) }, { argument := 188705764655471022739292160, coefficient := (-188705764655471022739292160) }, { argument := 13600415470664578215444480, coefficient := (-13600415470664578215444480) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 424332962684734840321867776, coefficient := (-424332962684734840321867776) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 40069180455899543449370624, coefficient := (-40069180455899543449370624) }, { argument := 15980488178030879403147264, coefficient := (-15980488178030879403147264) }, { argument := 135677748793633528493375488, coefficient := (-135677748793633528493375488) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 211512416163846039689379184640, coefficient := (-211512416163846039689379184640) }, { argument := 20629457565765056298607443968, coefficient := (-20629457565765056298607443968) }, { argument := 135672111007476001011662848, coefficient := (-135672111007476001011662848) }, { argument := 8216010985828471699950010368, coefficient := (-8216010985828471699950010368) }, { argument := 308696639071228878674225790976, coefficient := (-308696639071228878674225790976) }, { argument := 308673291691337571148289277952, coefficient := (-308673291691337571148289277952) }, { argument := 8239358365719779225886523392, coefficient := (-8239358365719779225886523392) }, { argument := 6338253001141147007483516026880, coefficient := 6338253001141147007483516026880 }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 150293657894490698999471800320, coefficient := 150293657894490698999471800320 }, { argument := 174394803034327946226414125056, coefficient := 174394803034327946226414125056 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 174124003650734269291279941632, coefficient := 174124003650734269291279941632 }, { argument := 174936401801515300096682491904, coefficient := 174936401801515300096682491904 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
