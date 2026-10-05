import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

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
def constantNumerator : ℤ := (-1050949107393364499222149537464320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    32683462805, 43889221481, 113489731, 11899193609, 128261413875, 5949601343,
    113489731, 60436875517, 1057569980663, 1057570499361, 60436356819, 63511791129,
    3362502105, 1097237529, 235946049003, 11078559567, 63511770969, 22192513893,
    9945927279, 3362502105, 1097237529, 1922755283, 33645820537, 33645837039,
    1922738781, 3730244805, 102031677783, 29841948801, 491241575, 50393545,
    245521195, 25444285, 2351785201, 63593047823, 29841948801, 14653661295,
    30622130469, 975227085, 29841948801, 16968951279, 30622130469, 478056317067,
    585136251, 31796524361, 29841948801, 975227085, 585136251, 975227085,
    15018497109, 16968951279, 2351785201, 91568868659, 43889243007, 34098463367,
    1086025311003, 34551106197, 17049235809, 17742459939, 17742459939, 600442196883,
    32683478835, 1086025311003, 600442196883, 91568852157
  ]
def negativeCoefficients : Array ℕ := #[
    75362934225805038576845455360, 101201654531795337517478182912, 261689502843892648128806912, 27437672398592915188920352768, 295750684535533038295056384000, 27437693328729909821620355072,
    261689502843892648128806912, 69678973454796352714379886592, 2438590346666040043651440050176, 2438591542702197236776065564672, 69678375436717756152067129344, 73224109788722476402977275904,
    31013607889122321233703075840, 1265028742845778892427362304, 272027273822579606848618364928, 25545419129724438279339638784, 73224086545824943528942239744, 25586226508525915017805037568,
    22933746886429927017554116608, 31013607889122321233703075840, 1265028742845778892427362304, 2216785913867123861076574208, 77581980074499984191834292224, 77582018125521322236211888128,
    2216766888356454838887776256, 68810871250119591994463354880, 235269030934274721501639868416, 68810849024098826183667351552, 1132725951548874528548454400, 116199603447745700786339840,
    1132266662209084298918625280, 117341053383381709634928640, 2711423732449036041428402176, 73317792378628334558010933248, 68810849024098826183667351552, 16894521228230517724198993920,
    70609825469173305299580223488, 2248720556343098894891089920, 68810849024098826183667351552, 39127737680369920771104964608, 70609825469173305299580223488, 1102322816719387078275612278784,
    43175434681787498781908926464, 73317793415104767199566364672, 68810849024098826183667351552, 2248720556343098894891089920, 43175434681787498781908926464, 2248720556343098894891089920,
    69260593135367445962645569536, 39127737680369920771104964608, 2711423732449036041428402176, 105571717829481034177455325184, 101201704167371953851454193664, 157251406759452373394042912768,
    2504203871205395368707260153856, 79669426684952389202208620544, 157251444810473711438420508672, 81822654433194345667133177856, 81822654433194345667133177856, 1384525442119578006946490351616,
    75362971188468476272359505920, 2504203871205395368707260153856, 1384525442119578006946490351616, 105571698803970365155266527232
  ]
def negativeScales : Array ℕ := #[
    34, 35, 26, 33, 36, 32,
    26, 35, 39, 39, 35, 35,
    31, 30, 37, 33, 35, 34,
    33, 31, 30, 30, 34, 34,
    30, 31, 36, 34, 28, 25,
    27, 24, 31, 35, 34, 33,
    34, 29, 34, 33, 34, 38,
    29, 34, 34, 29, 29, 29,
    33, 33, 31, 36, 35, 34,
    39, 35, 33, 34, 34, 39,
    34, 39, 39, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34927841800781805, 35353147628379406, 26757986522031346, 33470144756380386, 36900296263911338, 32470145856903524,
    26757986522031346, 35814710027309847, 39943890279397095, 39943890986984282, 35814697645361738, 35886305409115649,
    31646888024834195, 30031228726870443, 37779666057442211, 33367051263416188, 35886304951173306, 34369354049285608,
    33211458736704494, 31646888024834195, 30031228726870443, 30840528012040210, 34969708268639101, 34969708976226344,
    30840515630091970, 31796623168010801, 36570226179148915, 34796622702017929, 28871857426468264, 25586735612367274,
    27871272334499401, 24600838315487343, 31131109152424379, 35888150006910869, 34796622702017929, 33770542123918989,
    34833855608882598, 29861162955749913, 34796622702017929, 33982178372339938, 34833855608882598, 38798389628214309,
    29124197359443481, 34888150027305911, 34796622702017929, 29861162955749913, 29124197359443481, 29861162955749913,
    33806021400147278, 33982178372339938, 31131109152424379, 36414138146921636, 35353148335966481, 34988987694980951,
    39982194883535720, 35008012849917792, 33988988044078182, 34046486997732428, 34046486997732428, 39127234411616790,
    34927842508368967, 39982194883535720, 39127234411616790, 36414137886927644
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
noncomputable def negativeCeiling : ℝ := 8038954561 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 75362934225805038576845455360, coefficient := (-75362934225805038576845455360) }, { argument := 101201654531795337517478182912, coefficient := (-101201654531795337517478182912) }, { argument := 261689502843892648128806912, coefficient := (-261689502843892648128806912) }, { argument := 27437672398592915188920352768, coefficient := (-27437672398592915188920352768) }, { argument := 295750684535533038295056384000, coefficient := (-295750684535533038295056384000) }, { argument := 27437693328729909821620355072, coefficient := (-27437693328729909821620355072) }, { argument := 261689502843892648128806912, coefficient := (-261689502843892648128806912) }, { argument := 69678973454796352714379886592, coefficient := (-69678973454796352714379886592) }, { argument := 2438590346666040043651440050176, coefficient := (-2438590346666040043651440050176) }, { argument := 2438591542702197236776065564672, coefficient := (-2438591542702197236776065564672) }, { argument := 69678375436717756152067129344, coefficient := (-69678375436717756152067129344) }, { argument := 73224109788722476402977275904, coefficient := (-73224109788722476402977275904) }, { argument := 31013607889122321233703075840, coefficient := (-31013607889122321233703075840) }, { argument := 1265028742845778892427362304, coefficient := (-1265028742845778892427362304) }, { argument := 272027273822579606848618364928, coefficient := (-272027273822579606848618364928) }, { argument := 25545419129724438279339638784, coefficient := (-25545419129724438279339638784) }, { argument := 73224086545824943528942239744, coefficient := (-73224086545824943528942239744) }, { argument := 25586226508525915017805037568, coefficient := (-25586226508525915017805037568) }, { argument := 22933746886429927017554116608, coefficient := (-22933746886429927017554116608) }, { argument := 31013607889122321233703075840, coefficient := (-31013607889122321233703075840) }, { argument := 1265028742845778892427362304, coefficient := (-1265028742845778892427362304) }, { argument := 2216785913867123861076574208, coefficient := (-2216785913867123861076574208) }, { argument := 77581980074499984191834292224, coefficient := (-77581980074499984191834292224) }, { argument := 77582018125521322236211888128, coefficient := (-77582018125521322236211888128) }, { argument := 2216766888356454838887776256, coefficient := (-2216766888356454838887776256) }, { argument := 68810871250119591994463354880, coefficient := (-68810871250119591994463354880) }, { argument := 235269030934274721501639868416, coefficient := (-235269030934274721501639868416) }, { argument := 68810849024098826183667351552, coefficient := (-68810849024098826183667351552) }, { argument := 1132725951548874528548454400, coefficient := (-1132725951548874528548454400) }, { argument := 116199603447745700786339840, coefficient := (-116199603447745700786339840) }, { argument := 1132266662209084298918625280, coefficient := (-1132266662209084298918625280) }, { argument := 117341053383381709634928640, coefficient := (-117341053383381709634928640) }, { argument := 2711423732449036041428402176, coefficient := (-2711423732449036041428402176) }, { argument := 73317792378628334558010933248, coefficient := (-73317792378628334558010933248) }, { argument := 68810849024098826183667351552, coefficient := (-68810849024098826183667351552) }, { argument := 16894521228230517724198993920, coefficient := (-16894521228230517724198993920) }, { argument := 70609825469173305299580223488, coefficient := (-70609825469173305299580223488) }, { argument := 2248720556343098894891089920, coefficient := (-2248720556343098894891089920) }, { argument := 68810849024098826183667351552, coefficient := (-68810849024098826183667351552) }, { argument := 39127737680369920771104964608, coefficient := (-39127737680369920771104964608) }, { argument := 70609825469173305299580223488, coefficient := (-70609825469173305299580223488) }, { argument := 1102322816719387078275612278784, coefficient := (-1102322816719387078275612278784) }, { argument := 43175434681787498781908926464, coefficient := (-43175434681787498781908926464) }, { argument := 73317793415104767199566364672, coefficient := (-73317793415104767199566364672) }, { argument := 68810849024098826183667351552, coefficient := (-68810849024098826183667351552) }, { argument := 2248720556343098894891089920, coefficient := (-2248720556343098894891089920) }, { argument := 43175434681787498781908926464, coefficient := (-43175434681787498781908926464) }, { argument := 2248720556343098894891089920, coefficient := (-2248720556343098894891089920) }, { argument := 69260593135367445962645569536, coefficient := (-69260593135367445962645569536) }, { argument := 39127737680369920771104964608, coefficient := (-39127737680369920771104964608) }, { argument := 2711423732449036041428402176, coefficient := (-2711423732449036041428402176) }, { argument := 105571717829481034177455325184, coefficient := (-105571717829481034177455325184) }, { argument := 101201704167371953851454193664, coefficient := (-101201704167371953851454193664) }, { argument := 157251406759452373394042912768, coefficient := (-157251406759452373394042912768) }, { argument := 2504203871205395368707260153856, coefficient := (-2504203871205395368707260153856) }, { argument := 79669426684952389202208620544, coefficient := (-79669426684952389202208620544) }, { argument := 157251444810473711438420508672, coefficient := (-157251444810473711438420508672) }, { argument := 81822654433194345667133177856, coefficient := (-81822654433194345667133177856) }, { argument := 81822654433194345667133177856, coefficient := (-81822654433194345667133177856) }, { argument := 1384525442119578006946490351616, coefficient := (-1384525442119578006946490351616) }, { argument := 75362971188468476272359505920, coefficient := (-75362971188468476272359505920) }, { argument := 2504203871205395368707260153856, coefficient := (-2504203871205395368707260153856) }, { argument := 1384525442119578006946490351616, coefficient := (-1384525442119578006946490351616) }, { argument := 105571698803970365155266527232, coefficient := (-105571698803970365155266527232) }] }

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
def constantNumerator : ℤ := (-430308916778780086147031131750400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    34551106197, 32683478835, 43889243007, 13777578675, 36244411875, 11827123875,
    249697056735, 119415799125, 13777578045, 239213118375, 107207155125, 36244411875,
    11827123875, 987360821, 17277583519, 17277591993, 987352347, 3827767545,
    104699172627, 30622130469, 9403017615, 4219407927, 9402607863, 2130427971,
    121903425, 3334368555, 975227085, 881003025, 880604655, 25444285,
    2130427971, 1065214371, 12721757, 227342049, 23836403811, 256932608625,
    11918210997, 227342049, 987360821, 17277583519, 17277591993, 987352347,
    101886947, 10682662633, 115148425875, 5341335391, 101886947, 33414368837,
    584709800143, 584710086921, 33414082059, 3730244805, 102031677783, 29841948801,
    1818822565, 31827127535, 31827143145, 1818806955, 2121119595, 58018012857,
    16968951279, 780316965, 779964123, 34445765
  ]
def negativeCoefficients : Array ℕ := #[
    79669426684952389202208620544, 75362971188468476272359505920, 101201704167371953851454193664, 15884466735820209155525836800, 334295694980122173945937920000, 13635745453136562358321152000,
    287881106346817433235735183360, 275354085602048001171259392000, 15884466009479661253212241920, 275793948358600793505398784000, 247202869182669291786338304000, 334295694980122173945937920000,
    13635745453136562358321152000, 2276699046674343424889454592, 79678790346783767548370354176, 79678829426211087702055452672, 2276679506960683348046905344, 70609848276266509432227102720,
    241419855272425694612793851904, 70609825469173305299580223488, 10840941216530485764937482240, 9729292271493794298020757504, 10840468804638130100175372288, 9824864887127328623148662784,
    2248721282683646797204684800, 7688530422688716388942479360, 2248720556343098894891089920, 1015727333146183621568102400, 1015268043806393391938273280, 117341053383381709634928640,
    9824864887127328623148662784, 9824868442737248830664736768, 117337497773461502118854656, 262107537193483530953293824, 27481502546194501315420225536, 296223129718497148579872768000,
    27481523509766219581718790144, 262107537193483530953293824, 2276699046674343424889454592, 79678790346783767548370354176, 79678829426211087702055452672, 2276679506960683348046905344,
    234935304470076147361644544, 24632542952091403092928495616, 265514192825829980066807808000, 24632561742406085175320510464, 234935304470076147361644544, 38524144395042179531682086912,
    1348249005078472698252687835136, 1348249666343519194537412001792, 38523813762518931389320003584, 68810871250119591994463354880, 235269030934274721501639868416, 68810849024098826183667351552,
    2096959648252684733450813440, 73388359529932417478762168320, 73388395524141791304524759040, 2096941651147997820569518080, 39127750318695454271361515520, 133780429354783665167599140864,
    39127737680369920771104964608, 899644209358048350531747840, 899237410228519861431042048, 317706105689070946610053120
  ]
def negativeScales : Array ℕ := #[
    35, 34, 35, 33, 35, 33,
    37, 36, 33, 37, 36, 35,
    33, 29, 34, 34, 29, 31,
    36, 34, 33, 31, 33, 30,
    26, 31, 29, 29, 29, 24,
    30, 29, 23, 27, 34, 37,
    33, 27, 29, 34, 34, 29,
    26, 33, 36, 32, 26, 34,
    39, 39, 34, 31, 36, 34,
    30, 34, 34, 30, 30, 35,
    33, 29, 29, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35008012849917792, 34927842508368967, 35353148335966481, 33681603314429183, 35077039527954695, 33461380230010693,
    37861387861734502, 36797202767166521, 33681603248459834, 37799505553065338, 36641610239861858, 35077039527954695,
    33461380230010693, 29879002161393582, 34008182401968714, 34008183109555789, 29878989779445008, 31833856074875475,
    36607459085352405, 34833855608882598, 33130476674559417, 31974393441856869, 33130413805373899, 30988496149013999,
    26861163421742798, 31634766431355589, 29861162955749913, 29714571731972760, 29713919229782749, 24600838315487343,
    30988496149013999, 29988496671124131, 23600794599001323, 27760289307914390, 34472447542249815, 37902599049965493,
    33472448642772953, 27760289307914390, 29879002161393582, 34008182401968714, 34008183109555789, 29878989779445008,
    26602393995058195, 33314552229668597, 36744703733008990, 32314553330191736, 26602393995058195, 34959749584573211,
    39088929815853076, 39088930523440151, 34959737202622779, 31796623168010801, 36570226179148915, 34796622702017929,
    30760357662193732, 34889537909086357, 34889538616673479, 30760345280245763, 30982178838332939, 35755781832557601,
    33982178372339938, 29539485025314029, 29538832523125513, 25037823283162175
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
noncomputable def negativeCeiling : ℝ := 1567157053 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79669426684952389202208620544, coefficient := (-79669426684952389202208620544) }, { argument := 75362971188468476272359505920, coefficient := (-75362971188468476272359505920) }, { argument := 101201704167371953851454193664, coefficient := (-101201704167371953851454193664) }, { argument := 15884466735820209155525836800, coefficient := (-15884466735820209155525836800) }, { argument := 334295694980122173945937920000, coefficient := (-334295694980122173945937920000) }, { argument := 13635745453136562358321152000, coefficient := (-13635745453136562358321152000) }, { argument := 287881106346817433235735183360, coefficient := (-287881106346817433235735183360) }, { argument := 275354085602048001171259392000, coefficient := (-275354085602048001171259392000) }, { argument := 15884466009479661253212241920, coefficient := (-15884466009479661253212241920) }, { argument := 275793948358600793505398784000, coefficient := (-275793948358600793505398784000) }, { argument := 247202869182669291786338304000, coefficient := (-247202869182669291786338304000) }, { argument := 334295694980122173945937920000, coefficient := (-334295694980122173945937920000) }, { argument := 13635745453136562358321152000, coefficient := (-13635745453136562358321152000) }, { argument := 2276699046674343424889454592, coefficient := (-2276699046674343424889454592) }, { argument := 79678790346783767548370354176, coefficient := (-79678790346783767548370354176) }, { argument := 79678829426211087702055452672, coefficient := (-79678829426211087702055452672) }, { argument := 2276679506960683348046905344, coefficient := (-2276679506960683348046905344) }, { argument := 70609848276266509432227102720, coefficient := (-70609848276266509432227102720) }, { argument := 241419855272425694612793851904, coefficient := (-241419855272425694612793851904) }, { argument := 70609825469173305299580223488, coefficient := (-70609825469173305299580223488) }, { argument := 10840941216530485764937482240, coefficient := (-10840941216530485764937482240) }, { argument := 9729292271493794298020757504, coefficient := (-9729292271493794298020757504) }, { argument := 10840468804638130100175372288, coefficient := (-10840468804638130100175372288) }, { argument := 9824864887127328623148662784, coefficient := (-9824864887127328623148662784) }, { argument := 2248721282683646797204684800, coefficient := (-2248721282683646797204684800) }, { argument := 7688530422688716388942479360, coefficient := (-7688530422688716388942479360) }, { argument := 2248720556343098894891089920, coefficient := (-2248720556343098894891089920) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 117341053383381709634928640, coefficient := (-117341053383381709634928640) }, { argument := 9824864887127328623148662784, coefficient := (-9824864887127328623148662784) }, { argument := 9824868442737248830664736768, coefficient := (-9824868442737248830664736768) }, { argument := 117337497773461502118854656, coefficient := (-117337497773461502118854656) }, { argument := 262107537193483530953293824, coefficient := (-262107537193483530953293824) }, { argument := 27481502546194501315420225536, coefficient := (-27481502546194501315420225536) }, { argument := 296223129718497148579872768000, coefficient := (-296223129718497148579872768000) }, { argument := 27481523509766219581718790144, coefficient := (-27481523509766219581718790144) }, { argument := 262107537193483530953293824, coefficient := (-262107537193483530953293824) }, { argument := 2276699046674343424889454592, coefficient := (-2276699046674343424889454592) }, { argument := 79678790346783767548370354176, coefficient := (-79678790346783767548370354176) }, { argument := 79678829426211087702055452672, coefficient := (-79678829426211087702055452672) }, { argument := 2276679506960683348046905344, coefficient := (-2276679506960683348046905344) }, { argument := 234935304470076147361644544, coefficient := (-234935304470076147361644544) }, { argument := 24632542952091403092928495616, coefficient := (-24632542952091403092928495616) }, { argument := 265514192825829980066807808000, coefficient := (-265514192825829980066807808000) }, { argument := 24632561742406085175320510464, coefficient := (-24632561742406085175320510464) }, { argument := 234935304470076147361644544, coefficient := (-234935304470076147361644544) }, { argument := 38524144395042179531682086912, coefficient := (-38524144395042179531682086912) }, { argument := 1348249005078472698252687835136, coefficient := (-1348249005078472698252687835136) }, { argument := 1348249666343519194537412001792, coefficient := (-1348249666343519194537412001792) }, { argument := 38523813762518931389320003584, coefficient := (-38523813762518931389320003584) }, { argument := 68810871250119591994463354880, coefficient := (-68810871250119591994463354880) }, { argument := 235269030934274721501639868416, coefficient := (-235269030934274721501639868416) }, { argument := 68810849024098826183667351552, coefficient := (-68810849024098826183667351552) }, { argument := 2096959648252684733450813440, coefficient := (-2096959648252684733450813440) }, { argument := 73388359529932417478762168320, coefficient := (-73388359529932417478762168320) }, { argument := 73388395524141791304524759040, coefficient := (-73388395524141791304524759040) }, { argument := 2096941651147997820569518080, coefficient := (-2096941651147997820569518080) }, { argument := 39127750318695454271361515520, coefficient := (-39127750318695454271361515520) }, { argument := 133780429354783665167599140864, coefficient := (-133780429354783665167599140864) }, { argument := 39127737680369920771104964608, coefficient := (-39127737680369920771104964608) }, { argument := 899644209358048350531747840, coefficient := (-899644209358048350531747840) }, { argument := 899237410228519861431042048, coefficient := (-899237410228519861431042048) }, { argument := 317706105689070946610053120, coefficient := (-317706105689070946610053120) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
