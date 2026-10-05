import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1007679024748409529499025397514240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3611576335, 38929183125, 1805789545, 34445765, 60436875517, 1057569980663,
    1057570499361, 60436356819, 3827767545, 104699172627, 30622130469, 33414368837,
    584709800143, 584710086921, 33414082059, 59757058935, 1634507465661, 478056317067,
    36523868265, 36507352983, 73142055, 2000621133, 585136251, 9942748425,
    9938252535, 157995687, 2508112653, 89271735759, 62062447137, 1974471663,
    89271778575, 1013917881, 1013917881, 34313115657, 1867743465, 62062447137,
    34313115657, 78997509, 1974471663, 1867743465, 2508112653, 31755895983,
    1681252335, 548619183, 117973033101, 5539284009, 31755885903, 11096265411,
    4972967433, 1681252335, 548619183, 4701510345, 2109704727, 4701305469,
    1065214371, 3730244805, 102031677783, 29841948801, 36523868265, 36507352983,
    881003025, 880604655, 11240197, 1178514383
  ]
def negativeCoefficients : Array ℕ := #[
    33310912177205456139903303680, 359058339052723816460451840000, 33310937587595417674810654720, 317706105689070946610053120, 69678973454796352714379886592, 2438590346666040043651440050176,
    2438591542702197236776065564672, 69678375436717756152067129344, 70609848276266509432227102720, 241419855272425694612793851904, 70609825469173305299580223488, 38524144395042179531682086912,
    1348249005078472698252687835136, 1348249666343519194537412001792, 38523813762518931389320003584, 1102323172771523659989736488960, 3768917613202008773859603382272, 1102322816719387078275612278784,
    42109153154146069568437616640, 42090112330373623191498129408, 43175448627526018506329948160, 147619784115623354667695603712, 43175434681787498781908926464, 11463208474078358014840012800,
    11458025065815011137589084160, 5829012005677838492063760384, 2891657013620230690940387328, 102923303910131144423620214784, 71553129932772942416248307712, 2276410840509543309889241088,
    102923353273618285670380339200, 2337935457820612047994355712, 2337935457820612047994355712, 39560328931017198601588703232, 2153361605887405833679011840, 71553129932772942416248307712,
    39560328931017198601588703232, 5828987323934267868683698176, 2276410840509543309889241088, 2153361605887405833679011840, 2891657013620230690940387328, 73224110753717775758908194816,
    31013631547071595766203023360, 1265029707841078248358281216, 272027293651676564581779505152, 25545438616403709144267227136, 73224087510820242884873158656, 25586246026334066507117494272,
    22933764380860837921850130432, 31013631547071595766203023360, 1265029707841078248358281216, 10840944761764112430991933440, 9729295792516069367331422208, 10840472349871756766229823488,
    9824868442737248830664736768, 68810871250119591994463354880, 235269030934274721501639868416, 68810849024098826183667351552, 42109153154146069568437616640, 42090112330373623191498129408,
    1015727333146183621568102400, 1015268043806393391938273280, 12959064837317367559094272, 1358734575649169921496055808
  ]
def negativeScales : Array ℕ := #[
    31, 35, 30, 25, 35, 39,
    39, 35, 31, 36, 34, 34,
    39, 39, 34, 35, 40, 38,
    35, 35, 26, 30, 29, 33,
    33, 27, 31, 36, 35, 30,
    36, 29, 29, 34, 30, 35,
    34, 26, 30, 30, 31, 34,
    30, 29, 36, 32, 34, 33,
    32, 30, 29, 32, 30, 32,
    29, 31, 36, 34, 35, 35,
    29, 29, 23, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31749981518003409, 35180133020918799, 30749982618526552, 25037823283162175, 35814710027309847, 39943890279397095,
    39943890986984282, 35814697645361738, 31833856074875475, 36607459085352405, 34833855608882598, 34959749584573211,
    39088929815853076, 39088930523440151, 34959737202622779, 35798390094207182, 40571993105323231, 38798389628214309,
    35088120518992934, 35087468016804438, 26124197825436347, 30897800841373533, 29124197359443481, 33210997557990655,
    33210345055802159, 27235309935041531, 31223955002873610, 36377484426182304, 35853001534503249, 30878819519797683,
    36377485118119293, 29917293670575440, 29917293670575440, 34998041101471466, 30798649168769407, 35853001534503249,
    34998041101471466, 26235303826235372, 30878819519797683, 30798649168769407, 31223955002873610, 34886305428128431,
    30646889125357334, 29031229827393581, 36779666162605707, 32367052363939326, 34886304970186094, 33369355149808746,
    32211459837227632, 30646889125357334, 29031229827393581, 32130477146353336, 30974393963966969, 32130414277188377,
    29988496671124131, 31796623168010801, 36570226179148915, 34796622702017929, 35088120518992934, 35087468016804438,
    29714571731972760, 29713919229782749, 23422163985218119, 30134322219834546
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
noncomputable def negativeCeiling : ℝ := 764724963 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33310912177205456139903303680, coefficient := (-33310912177205456139903303680) }, { argument := 359058339052723816460451840000, coefficient := (-359058339052723816460451840000) }, { argument := 33310937587595417674810654720, coefficient := (-33310937587595417674810654720) }, { argument := 317706105689070946610053120, coefficient := (-317706105689070946610053120) }, { argument := 69678973454796352714379886592, coefficient := (-69678973454796352714379886592) }, { argument := 2438590346666040043651440050176, coefficient := (-2438590346666040043651440050176) }, { argument := 2438591542702197236776065564672, coefficient := (-2438591542702197236776065564672) }, { argument := 69678375436717756152067129344, coefficient := (-69678375436717756152067129344) }, { argument := 70609848276266509432227102720, coefficient := (-70609848276266509432227102720) }, { argument := 241419855272425694612793851904, coefficient := (-241419855272425694612793851904) }, { argument := 70609825469173305299580223488, coefficient := (-70609825469173305299580223488) }, { argument := 38524144395042179531682086912, coefficient := (-38524144395042179531682086912) }, { argument := 1348249005078472698252687835136, coefficient := (-1348249005078472698252687835136) }, { argument := 1348249666343519194537412001792, coefficient := (-1348249666343519194537412001792) }, { argument := 38523813762518931389320003584, coefficient := (-38523813762518931389320003584) }, { argument := 1102323172771523659989736488960, coefficient := (-1102323172771523659989736488960) }, { argument := 3768917613202008773859603382272, coefficient := (-3768917613202008773859603382272) }, { argument := 1102322816719387078275612278784, coefficient := (-1102322816719387078275612278784) }, { argument := 42109153154146069568437616640, coefficient := (-42109153154146069568437616640) }, { argument := 42090112330373623191498129408, coefficient := (-42090112330373623191498129408) }, { argument := 43175448627526018506329948160, coefficient := (-43175448627526018506329948160) }, { argument := 147619784115623354667695603712, coefficient := (-147619784115623354667695603712) }, { argument := 43175434681787498781908926464, coefficient := (-43175434681787498781908926464) }, { argument := 11463208474078358014840012800, coefficient := (-11463208474078358014840012800) }, { argument := 11458025065815011137589084160, coefficient := (-11458025065815011137589084160) }, { argument := 5829012005677838492063760384, coefficient := (-5829012005677838492063760384) }, { argument := 2891657013620230690940387328, coefficient := (-2891657013620230690940387328) }, { argument := 102923303910131144423620214784, coefficient := (-102923303910131144423620214784) }, { argument := 71553129932772942416248307712, coefficient := (-71553129932772942416248307712) }, { argument := 2276410840509543309889241088, coefficient := (-2276410840509543309889241088) }, { argument := 102923353273618285670380339200, coefficient := (-102923353273618285670380339200) }, { argument := 2337935457820612047994355712, coefficient := (-2337935457820612047994355712) }, { argument := 2337935457820612047994355712, coefficient := (-2337935457820612047994355712) }, { argument := 39560328931017198601588703232, coefficient := (-39560328931017198601588703232) }, { argument := 2153361605887405833679011840, coefficient := (-2153361605887405833679011840) }, { argument := 71553129932772942416248307712, coefficient := (-71553129932772942416248307712) }, { argument := 39560328931017198601588703232, coefficient := (-39560328931017198601588703232) }, { argument := 5828987323934267868683698176, coefficient := (-5828987323934267868683698176) }, { argument := 2276410840509543309889241088, coefficient := (-2276410840509543309889241088) }, { argument := 2153361605887405833679011840, coefficient := (-2153361605887405833679011840) }, { argument := 2891657013620230690940387328, coefficient := (-2891657013620230690940387328) }, { argument := 73224110753717775758908194816, coefficient := (-73224110753717775758908194816) }, { argument := 31013631547071595766203023360, coefficient := (-31013631547071595766203023360) }, { argument := 1265029707841078248358281216, coefficient := (-1265029707841078248358281216) }, { argument := 272027293651676564581779505152, coefficient := (-272027293651676564581779505152) }, { argument := 25545438616403709144267227136, coefficient := (-25545438616403709144267227136) }, { argument := 73224087510820242884873158656, coefficient := (-73224087510820242884873158656) }, { argument := 25586246026334066507117494272, coefficient := (-25586246026334066507117494272) }, { argument := 22933764380860837921850130432, coefficient := (-22933764380860837921850130432) }, { argument := 31013631547071595766203023360, coefficient := (-31013631547071595766203023360) }, { argument := 1265029707841078248358281216, coefficient := (-1265029707841078248358281216) }, { argument := 10840944761764112430991933440, coefficient := (-10840944761764112430991933440) }, { argument := 9729295792516069367331422208, coefficient := (-9729295792516069367331422208) }, { argument := 10840472349871756766229823488, coefficient := (-10840472349871756766229823488) }, { argument := 9824868442737248830664736768, coefficient := (-9824868442737248830664736768) }, { argument := 68810871250119591994463354880, coefficient := (-68810871250119591994463354880) }, { argument := 235269030934274721501639868416, coefficient := (-235269030934274721501639868416) }, { argument := 68810849024098826183667351552, coefficient := (-68810849024098826183667351552) }, { argument := 42109153154146069568437616640, coefficient := (-42109153154146069568437616640) }, { argument := 42090112330373623191498129408, coefficient := (-42090112330373623191498129408) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 12959064837317367559094272, coefficient := (-12959064837317367559094272) }, { argument := 1358734575649169921496055808, coefficient := (-1358734575649169921496055808) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 6584142845265801546913897101918208
def positiveArguments : Array ℕ := #[
    3, 29369915, 509, 29358533, 257, 24602893,
    665
  ]
def positiveCoefficients : Array ℕ := #[
    60847228810955011271841753858048, 277391004401460872012816711680, 39381967499766159995228389376, 277283504450844827409172135936, 39768823762042841331134365696, 3717884073114502852496794320896,
    823230126124777882807917608960
  ]
def positiveScales : Array ℕ := #[
    1, 24, 8, 24, 8, 24,
    9
  ]
def negativeArguments : Array ℕ := #[
    12703207125, 589257641, 11240197, 1922755283, 33645820537, 33645837039,
    1922738781, 121903425, 3334368555, 975227085, 1818822565, 31827127535,
    31827143145, 1818806955, 73142055, 2000621133, 585136251, 881003025,
    880604655, 121903425, 3334368555, 975227085, 377572725, 377401995,
    2442418873, 42739285547, 42739306509, 2442397911, 1877312745, 51349275747,
    15018497109, 881003025, 880604655, 2121119595, 58018012857, 16968951279,
    9942748425, 9938252535, 377572725, 377401995, 2351010771, 32070195,
    10465011, 8217523629, 105662853, 2351010015, 211663287, 94860261,
    32070195, 10465011, 982480075, 25196009, 982081705, 12721757,
    780316965, 779964123, 1
  ]
def negativeCoefficients : Array ℕ := #[
    14645800671887418829307904000, 1358735612125602563051487232, 12959064837317367559094272, 2216785913867123861076574208, 77581980074499984191834292224, 77582018125521322236211888128,
    2216766888356454838887776256, 2248721282683646797204684800, 7688530422688716388942479360, 2248720556343098894891089920, 2096959648252684733450813440, 73388359529932417478762168320,
    73388395524141791304524759040, 2096941651147997820569518080, 43175448627526018506329948160, 147619784115623354667695603712, 43175434681787498781908926464, 1015727333146183621568102400,
    1015268043806393391938273280, 2248721282683646797204684800, 7688530422688716388942479360, 2248720556343098894891089920, 870623428411014532772659200, 870229751834051478804234240,
    2815917241939319499205378048, 98550082797337817757194911744, 98550131132418976894647533568, 2815893074398739930479067136, 69260615506656321353904291840, 236806737018812464779428364288,
    69260593135367445962645569536, 1015727333146183621568102400, 1015268043806393391938273280, 39127750318695454271361515520, 133780429354783665167599140864, 39127737680369920771104964608,
    11463208474078358014840012800, 11458025065815011137589084160, 870623428411014532772659200, 870229751834051478804234240, 2710530875448223360924778496, 295795339779479846843842560,
    12065336227847204279156736, 9474159706488997380467195904, 243641950923624189637165056, 2710530003839565878148464640, 244031155318070873646170112, 218732869679036413060841472,
    295795339779479846843842560, 12065336227847204279156736, 1132722406315247862494003200, 116196082425470631475675136, 1132263116975457632864174080, 117337497773461502118854656,
    899644209358048350531747840, 899237410228519861431042048, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    33, 29, 23, 30, 34, 34,
    30, 26, 31, 29, 30, 34,
    34, 30, 26, 30, 29, 29,
    29, 26, 31, 29, 28, 28,
    31, 35, 35, 31, 30, 35,
    33, 29, 29, 30, 35, 33,
    33, 33, 28, 28, 31, 24,
    23, 32, 26, 31, 27, 26,
    24, 23, 29, 24, 29, 23,
    29, 29, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 24807835754503726, 8991521844801183, 24807276544931372, 8005624549193878, 24552324633083059,
    9377210530388551
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33564473722976775, 29134323320357684, 23422163985218119, 30840528012040210, 34969708268639101, 34969708976226344,
    30840515630091970, 26861163421742798, 31634766431355589, 29861162955749913, 30760357662193732, 34889537909086357,
    34889538616673479, 30760345280245763, 26124197825436347, 30897800841373533, 29124197359443481, 29714571731972760,
    29713919229782749, 26861163421742798, 31634766431355589, 29861162955749913, 28492179310534916, 28491526808346416,
    31185663496644865, 35314843740202766, 35314844447789841, 31185651114696970, 30806021866140151, 35579624877151922,
    33806021400147278, 29714571731972760, 29713919229782749, 30982178838332939, 35755781832557601, 33982178372339938,
    33210997557990655, 33210345055802159, 28492179310534916, 28491526808346416, 31130634002604031, 24934729798234083,
    23319070492253999, 32936056561902796, 26654893028823861, 31130633538685431, 27657195814694722, 26499300502088315,
    24934729798234083, 23319070492253999, 29871852911078449, 24586691895881256, 29871267817277976, 23600794599001323,
    29539485025314029, 29538832523125513, 0
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 57
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
noncomputable def positiveFloor : ℝ := 25262841 / 10000000000
noncomputable def negativeCeiling : ℝ := 577984509 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14645800671887418829307904000, coefficient := (-14645800671887418829307904000) }, { argument := 1358735612125602563051487232, coefficient := (-1358735612125602563051487232) }, { argument := 12959064837317367559094272, coefficient := (-12959064837317367559094272) }, { argument := 2216785913867123861076574208, coefficient := (-2216785913867123861076574208) }, { argument := 77581980074499984191834292224, coefficient := (-77581980074499984191834292224) }, { argument := 77582018125521322236211888128, coefficient := (-77582018125521322236211888128) }, { argument := 2216766888356454838887776256, coefficient := (-2216766888356454838887776256) }, { argument := 2248721282683646797204684800, coefficient := (-2248721282683646797204684800) }, { argument := 7688530422688716388942479360, coefficient := (-7688530422688716388942479360) }, { argument := 2248720556343098894891089920, coefficient := (-2248720556343098894891089920) }, { argument := 2096959648252684733450813440, coefficient := (-2096959648252684733450813440) }, { argument := 73388359529932417478762168320, coefficient := (-73388359529932417478762168320) }, { argument := 73388395524141791304524759040, coefficient := (-73388395524141791304524759040) }, { argument := 2096941651147997820569518080, coefficient := (-2096941651147997820569518080) }, { argument := 43175448627526018506329948160, coefficient := (-43175448627526018506329948160) }, { argument := 147619784115623354667695603712, coefficient := (-147619784115623354667695603712) }, { argument := 43175434681787498781908926464, coefficient := (-43175434681787498781908926464) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 2248721282683646797204684800, coefficient := (-2248721282683646797204684800) }, { argument := 7688530422688716388942479360, coefficient := (-7688530422688716388942479360) }, { argument := 2248720556343098894891089920, coefficient := (-2248720556343098894891089920) }, { argument := 870623428411014532772659200, coefficient := (-870623428411014532772659200) }, { argument := 870229751834051478804234240, coefficient := (-870229751834051478804234240) }, { argument := 2815917241939319499205378048, coefficient := (-2815917241939319499205378048) }, { argument := 98550082797337817757194911744, coefficient := (-98550082797337817757194911744) }, { argument := 98550131132418976894647533568, coefficient := (-98550131132418976894647533568) }, { argument := 2815893074398739930479067136, coefficient := (-2815893074398739930479067136) }, { argument := 69260615506656321353904291840, coefficient := (-69260615506656321353904291840) }, { argument := 236806737018812464779428364288, coefficient := (-236806737018812464779428364288) }, { argument := 69260593135367445962645569536, coefficient := (-69260593135367445962645569536) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 39127750318695454271361515520, coefficient := (-39127750318695454271361515520) }, { argument := 133780429354783665167599140864, coefficient := (-133780429354783665167599140864) }, { argument := 39127737680369920771104964608, coefficient := (-39127737680369920771104964608) }, { argument := 11463208474078358014840012800, coefficient := (-11463208474078358014840012800) }, { argument := 11458025065815011137589084160, coefficient := (-11458025065815011137589084160) }, { argument := 870623428411014532772659200, coefficient := (-870623428411014532772659200) }, { argument := 870229751834051478804234240, coefficient := (-870229751834051478804234240) }, { argument := 2710530875448223360924778496, coefficient := (-2710530875448223360924778496) }, { argument := 295795339779479846843842560, coefficient := (-295795339779479846843842560) }, { argument := 12065336227847204279156736, coefficient := (-12065336227847204279156736) }, { argument := 9474159706488997380467195904, coefficient := (-9474159706488997380467195904) }, { argument := 243641950923624189637165056, coefficient := (-243641950923624189637165056) }, { argument := 2710530003839565878148464640, coefficient := (-2710530003839565878148464640) }, { argument := 244031155318070873646170112, coefficient := (-244031155318070873646170112) }, { argument := 218732869679036413060841472, coefficient := (-218732869679036413060841472) }, { argument := 295795339779479846843842560, coefficient := (-295795339779479846843842560) }, { argument := 12065336227847204279156736, coefficient := (-12065336227847204279156736) }, { argument := 1132722406315247862494003200, coefficient := (-1132722406315247862494003200) }, { argument := 116196082425470631475675136, coefficient := (-116196082425470631475675136) }, { argument := 1132263116975457632864174080, coefficient := (-1132263116975457632864174080) }, { argument := 117337497773461502118854656, coefficient := (-117337497773461502118854656) }, { argument := 899644209358048350531747840, coefficient := (-899644209358048350531747840) }, { argument := 899237410228519861431042048, coefficient := (-899237410228519861431042048) }, { argument := 60847228810955011271841753858048, coefficient := 60847228810955011271841753858048 }, { argument := 277391004401460872012816711680, coefficient := 277391004401460872012816711680 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 277283504450844827409172135936, coefficient := 277283504450844827409172135936 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 3717884073114502852496794320896, coefficient := 3717884073114502852496794320896 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
