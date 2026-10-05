import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 18, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-116604327582792447988286021959680)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    882443385, 901945135, 195523445, 1837920383, 21703102395, 1525082871,
    1803890165, 21703102395, 195523445, 1525082871, 1525082871, 1525082871,
    1525082871, 1525082871, 1764886875, 1837920383, 92128617, 7747025559,
    3873511845, 46065243, 42121781, 340912057, 683035899, 3680402633,
    22517667, 52541223, 683035899, 683035899, 22517667, 8429113347,
    337765005, 340912057, 683035899, 52541223, 337765005, 52541223,
    683035899, 683035899, 24813573, 5175765, 435226155, 217613025,
    2587935, 5453399, 870619843, 34749907177, 870619843, 21811107,
    41652513, 10448879, 5518760989, 164432359, 4949469, 11037519283,
    4949469, 4949469, 424004511, 4949469, 164432359, 424004511,
    333222799, 4949469, 4949469, 10448879
  ]
def negativeCoefficients : Array ℕ := #[
    8139103641316473117427630080, 8318975536936205741541294080, 7213541900650050922731274240, 8475911733263809834209247232, 100087893871519456552896430080, 225062507300281588789215756288,
    8318975052709173806665564160, 100087893871519456552896430080, 7213541900650050922731274240, 7033203353133799649662992384, 7033203353133799649662992384, 7033203353133799649662992384,
    225062507300281588789215756288, 7033203353133799649662992384, 8139104125543505052303360000, 8475911733263809834209247232, 424868254915951762518048768, 35726849454839919077895438336,
    35726840835598750637107445760, 424876874157120203306041344, 777009714035841590777348096, 25154869868483531447832936448, 25199576844018251705842925568, 135782890918315559689551609856,
    13292084489152484416268795904, 969214494000701988686266368, 25199576844018251705842925568, 25199576844018251705842925568, 13292084489152484416268795904, 310979393360796666655622037504,
    24922658417160908280503992320, 25154869868483531447832936448, 25199576844018251705842925568, 969214494000701988686266368, 24922658417160908280503992320, 969214494000701988686266368,
    25199576844018251705842925568, 25199576844018251705842925568, 915459261370618679641767936, 23869003085165829354946560, 2007126373867411184151429120, 2007125889640379249275699200,
    23869487312197764230676480, 100597455684823595073142784, 16060101429314190255522316288, 160255661069820441178572587008, 16060101429314190255522316288, 100585977198323729304649728,
    768353247337860056909611008, 96373898385079092989919232, 25450792892013803493765677056, 758310410977332863262785536, 91301587943759140727291904, 25450786677766893662860476416,
    91301587943759140727291904, 91301587943759140727291904, 3910751350257683194485669888, 91301587943759140727291904, 758310410977332863262785536, 3910751350257683194485669888,
    768359461584769887814811648, 91301587943759140727291904, 91301587943759140727291904, 96373898385079092989919232
  ]
def negativeScales : Array ℕ := #[
    29, 29, 27, 30, 34, 30,
    30, 34, 27, 30, 30, 30,
    30, 30, 30, 30, 26, 32,
    31, 25, 25, 28, 29, 31,
    24, 25, 29, 29, 24, 32,
    28, 28, 29, 25, 28, 25,
    29, 29, 24, 22, 28, 27,
    21, 22, 29, 35, 29, 24,
    25, 23, 32, 27, 22, 33,
    22, 22, 28, 22, 27, 28,
    28, 22, 22, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29716928481442891, 29748464436842674, 27542766368971490, 30775427126148845, 34337182235320530, 30506240492945643,
    30748464352866954, 34337182235320530, 27542766368971490, 30506240492945643, 30506240492945643, 30506240492945643,
    30506240492945643, 30506240492945643, 30716928567274445, 30775427126148845, 26457146020216069, 32850995355174355,
    31850995007118521, 25457175287665954, 25328063102131348, 28344824383119172, 29347386164771257, 31777216458948104,
    24424554025293734, 25646946446649874, 29347386164771257, 29347386164771257, 24424554025293734, 32972733752198476,
    28331444620902235, 28344824383119172, 29347386164771257, 25646946446649874, 28331444620902235, 25646946446649874,
    29347386164771257, 29347386164771257, 24564626153504293, 22303340684136973, 28697190017397742, 27697189669341918,
    21303369951586859, 22378724283971261, 29697467661295501, 35016290073027449, 29697467661295501, 24378559658531374,
    25311900203818400, 23316844836384581, 32361697259455864, 27292918997139100, 22238842324383307, 33361696907197122,
    22238842324383307, 22238842324383307, 28659504372883114, 22238842324383307, 27292918997139100, 28659504372883114,
    28311911871924152, 22238842324383307, 22238842324383307, 23316844836384581
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
noncomputable def negativeCeiling : ℝ := 68613499 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8139103641316473117427630080, coefficient := (-8139103641316473117427630080) }, { argument := 8318975536936205741541294080, coefficient := (-8318975536936205741541294080) }, { argument := 7213541900650050922731274240, coefficient := (-7213541900650050922731274240) }, { argument := 8475911733263809834209247232, coefficient := (-8475911733263809834209247232) }, { argument := 100087893871519456552896430080, coefficient := (-100087893871519456552896430080) }, { argument := 225062507300281588789215756288, coefficient := (-225062507300281588789215756288) }, { argument := 8318975052709173806665564160, coefficient := (-8318975052709173806665564160) }, { argument := 100087893871519456552896430080, coefficient := (-100087893871519456552896430080) }, { argument := 7213541900650050922731274240, coefficient := (-7213541900650050922731274240) }, { argument := 7033203353133799649662992384, coefficient := (-7033203353133799649662992384) }, { argument := 7033203353133799649662992384, coefficient := (-7033203353133799649662992384) }, { argument := 7033203353133799649662992384, coefficient := (-7033203353133799649662992384) }, { argument := 225062507300281588789215756288, coefficient := (-225062507300281588789215756288) }, { argument := 7033203353133799649662992384, coefficient := (-7033203353133799649662992384) }, { argument := 8139104125543505052303360000, coefficient := (-8139104125543505052303360000) }, { argument := 8475911733263809834209247232, coefficient := (-8475911733263809834209247232) }, { argument := 424868254915951762518048768, coefficient := (-424868254915951762518048768) }, { argument := 35726849454839919077895438336, coefficient := (-35726849454839919077895438336) }, { argument := 35726840835598750637107445760, coefficient := (-35726840835598750637107445760) }, { argument := 424876874157120203306041344, coefficient := (-424876874157120203306041344) }, { argument := 777009714035841590777348096, coefficient := (-777009714035841590777348096) }, { argument := 25154869868483531447832936448, coefficient := (-25154869868483531447832936448) }, { argument := 25199576844018251705842925568, coefficient := (-25199576844018251705842925568) }, { argument := 135782890918315559689551609856, coefficient := (-135782890918315559689551609856) }, { argument := 13292084489152484416268795904, coefficient := (-13292084489152484416268795904) }, { argument := 969214494000701988686266368, coefficient := (-969214494000701988686266368) }, { argument := 25199576844018251705842925568, coefficient := (-25199576844018251705842925568) }, { argument := 25199576844018251705842925568, coefficient := (-25199576844018251705842925568) }, { argument := 13292084489152484416268795904, coefficient := (-13292084489152484416268795904) }, { argument := 310979393360796666655622037504, coefficient := (-310979393360796666655622037504) }, { argument := 24922658417160908280503992320, coefficient := (-24922658417160908280503992320) }, { argument := 25154869868483531447832936448, coefficient := (-25154869868483531447832936448) }, { argument := 25199576844018251705842925568, coefficient := (-25199576844018251705842925568) }, { argument := 969214494000701988686266368, coefficient := (-969214494000701988686266368) }, { argument := 24922658417160908280503992320, coefficient := (-24922658417160908280503992320) }, { argument := 969214494000701988686266368, coefficient := (-969214494000701988686266368) }, { argument := 25199576844018251705842925568, coefficient := (-25199576844018251705842925568) }, { argument := 25199576844018251705842925568, coefficient := (-25199576844018251705842925568) }, { argument := 915459261370618679641767936, coefficient := (-915459261370618679641767936) }, { argument := 23869003085165829354946560, coefficient := (-23869003085165829354946560) }, { argument := 2007126373867411184151429120, coefficient := (-2007126373867411184151429120) }, { argument := 2007125889640379249275699200, coefficient := (-2007125889640379249275699200) }, { argument := 23869487312197764230676480, coefficient := (-23869487312197764230676480) }, { argument := 100597455684823595073142784, coefficient := (-100597455684823595073142784) }, { argument := 16060101429314190255522316288, coefficient := (-16060101429314190255522316288) }, { argument := 160255661069820441178572587008, coefficient := (-160255661069820441178572587008) }, { argument := 16060101429314190255522316288, coefficient := (-16060101429314190255522316288) }, { argument := 100585977198323729304649728, coefficient := (-100585977198323729304649728) }, { argument := 768353247337860056909611008, coefficient := (-768353247337860056909611008) }, { argument := 96373898385079092989919232, coefficient := (-96373898385079092989919232) }, { argument := 25450792892013803493765677056, coefficient := (-25450792892013803493765677056) }, { argument := 758310410977332863262785536, coefficient := (-758310410977332863262785536) }, { argument := 91301587943759140727291904, coefficient := (-91301587943759140727291904) }, { argument := 25450786677766893662860476416, coefficient := (-25450786677766893662860476416) }, { argument := 91301587943759140727291904, coefficient := (-91301587943759140727291904) }, { argument := 91301587943759140727291904, coefficient := (-91301587943759140727291904) }, { argument := 3910751350257683194485669888, coefficient := (-3910751350257683194485669888) }, { argument := 91301587943759140727291904, coefficient := (-91301587943759140727291904) }, { argument := 758310410977332863262785536, coefficient := (-758310410977332863262785536) }, { argument := 3910751350257683194485669888, coefficient := (-3910751350257683194485669888) }, { argument := 768359461584769887814811648, coefficient := (-768359461584769887814811648) }, { argument := 91301587943759140727291904, coefficient := (-91301587943759140727291904) }, { argument := 91301587943759140727291904, coefficient := (-91301587943759140727291904) }, { argument := 96373898385079092989919232, coefficient := (-96373898385079092989919232) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1819944218833338596291046834962432)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12754399095, 23574772585, 699472215, 6575038821, 77641415865, 5455883277,
    5893692315, 77641415865, 699472215, 5455883277, 5455883277, 5455883277,
    5455883277, 5455883277, 3188600605, 6575038821, 2780148559, 47895499973,
    25223607045, 66344091767, 831547485, 1940277465, 25223607045, 25223607045,
    831547485, 311275941885, 12473212275, 47895499973, 25223607045, 1940277465,
    12473212275, 1940277465, 25223607045, 25223607045, 13338050397, 279836361,
    23531227447, 11765610885, 139921019, 85819279, 13700807003, 546853802417,
    13700807003, 343237947, 332055611, 1668134203, 94993352933, 26251164563,
    790168833, 94993330295, 790168833, 790168833, 67691130027, 790168833,
    26251164563, 67691130027, 2656456207, 790168833, 790168833, 1668134203,
    2583189, 412398873, 16460482347, 412398873
  ]
def negativeCoefficients : Array ℕ := #[
    29409641989927214802995773440, 54359724558924894586189905920, 25805969873551486671000698880, 30322014601422996838425821184, 358057831995526877560134696960, 805146260054806384135221805056,
    54359716891996888950657515520, 358057831995526877560134696960, 25805969873551486671000698880, 25160820626712699504225681408, 25160820626712699504225681408, 25160820626712699504225681408,
    805146260054806384135221805056, 25160820626712699504225681408, 29409649656855220438528163840, 30322014601422996838425821184, 25642344477382699854879260672, 441758015142146869716985053184,
    930586847549864490850257469440, 152979060203568738064540893184, 490858996509818632536399544320, 35791801828840941955779133440, 930586847549864490850257469440, 930586847549864490850257469440,
    490858996509818632536399544320, 11484055272510965090382847672320, 920360618455909936005749145600, 441758015142146869716985053184, 930586847549864490850257469440, 35791801828840941955779133440,
    920360618455909936005749145600, 35791801828840941955779133440, 930586847549864490850257469440, 930586847549864490850257469440, 30755450264462385274310098944, 645258716735649586895388672,
    54259316306882349011560300544, 54259303216611585705419735040, 645271807006412893035954176, 791543138151638287549202432, 126367640193814286484241383424, 1260959017365166102957715881984,
    126367640193814286484241383424, 791452820586810396370796544, 24501379497425016793547669504, 15385822361671228069221761024, 438079517564654400797967122432, 121062128582623610334139645952,
    14576042237372742381367984128, 438079413165306315638759751680, 14576042237372742381367984128, 14576042237372742381367984128, 624340475834132465335261986816, 14576042237372742381367984128,
    121062128582623610334139645952, 624340475834132465335261986816, 24501483896773101952755040256, 14576042237372742381367984128, 14576042237372742381367984128, 15385822361671228069221761024,
    95302852754043405858766848, 15214832933034496031547457536, 151821152592461470590226661376, 15214832933034496031547457536
  ]
def negativeScales : Array ℕ := #[
    33, 34, 29, 32, 36, 32,
    32, 36, 29, 32, 32, 32,
    32, 32, 31, 32, 31, 35,
    34, 35, 29, 30, 34, 34,
    29, 38, 33, 35, 34, 30,
    33, 30, 34, 34, 33, 28,
    34, 33, 27, 26, 33, 38,
    33, 28, 28, 30, 36, 34,
    29, 36, 29, 29, 35, 29,
    34, 35, 31, 29, 29, 30,
    21, 28, 33, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33570275878934814, 34456524802824948, 29381691509730031, 32614352266528674, 36176107376080134, 32345165633704915,
    32456524599346364, 36176107376080134, 29381691509730031, 32345165633704915, 32345165633704915, 32345165633704915,
    32345165633704915, 32345165633704915, 31570276255037236, 32614352266528674, 31372514830318562, 35479171062630341,
    34554055548642468, 35949248952147128, 29631223409176541, 30853615832355471, 34554055548642468, 34554055548642468,
    29631223409176541, 38179403120842870, 33538114004772867, 35479171062630341, 34554055548642468, 30853615832355471,
    33538114004772867, 30853615832355471, 34554055548642468, 34554055548642468, 33634828754231180, 28060008192745727,
    34453857525938802, 33453857177882979, 27060037460195613, 26354798444725779, 33673541822020179, 38992364254733428,
    33673541822020179, 28354633819285892, 28306849636199141, 30635588213655331, 36467107514674095, 34611662374402932,
    29557585701641027, 36467107170863363, 29557585701641027, 29557585701641027, 35978247766777855, 29557585701641027,
    34611662374402932, 35978247766777855, 31306855783448968, 29557585701641027, 29557585701641027, 30635588213655331,
    21300721771969986, 28619465149235639, 33938287569567980, 28619465149235639
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
noncomputable def negativeCeiling : ℝ := 6092051429 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29409641989927214802995773440, coefficient := (-29409641989927214802995773440) }, { argument := 54359724558924894586189905920, coefficient := (-54359724558924894586189905920) }, { argument := 25805969873551486671000698880, coefficient := (-25805969873551486671000698880) }, { argument := 30322014601422996838425821184, coefficient := (-30322014601422996838425821184) }, { argument := 358057831995526877560134696960, coefficient := (-358057831995526877560134696960) }, { argument := 805146260054806384135221805056, coefficient := (-805146260054806384135221805056) }, { argument := 54359716891996888950657515520, coefficient := (-54359716891996888950657515520) }, { argument := 358057831995526877560134696960, coefficient := (-358057831995526877560134696960) }, { argument := 25805969873551486671000698880, coefficient := (-25805969873551486671000698880) }, { argument := 25160820626712699504225681408, coefficient := (-25160820626712699504225681408) }, { argument := 25160820626712699504225681408, coefficient := (-25160820626712699504225681408) }, { argument := 25160820626712699504225681408, coefficient := (-25160820626712699504225681408) }, { argument := 805146260054806384135221805056, coefficient := (-805146260054806384135221805056) }, { argument := 25160820626712699504225681408, coefficient := (-25160820626712699504225681408) }, { argument := 29409649656855220438528163840, coefficient := (-29409649656855220438528163840) }, { argument := 30322014601422996838425821184, coefficient := (-30322014601422996838425821184) }, { argument := 25642344477382699854879260672, coefficient := (-25642344477382699854879260672) }, { argument := 441758015142146869716985053184, coefficient := (-441758015142146869716985053184) }, { argument := 930586847549864490850257469440, coefficient := (-930586847549864490850257469440) }, { argument := 152979060203568738064540893184, coefficient := (-152979060203568738064540893184) }, { argument := 490858996509818632536399544320, coefficient := (-490858996509818632536399544320) }, { argument := 35791801828840941955779133440, coefficient := (-35791801828840941955779133440) }, { argument := 930586847549864490850257469440, coefficient := (-930586847549864490850257469440) }, { argument := 930586847549864490850257469440, coefficient := (-930586847549864490850257469440) }, { argument := 490858996509818632536399544320, coefficient := (-490858996509818632536399544320) }, { argument := 11484055272510965090382847672320, coefficient := (-11484055272510965090382847672320) }, { argument := 920360618455909936005749145600, coefficient := (-920360618455909936005749145600) }, { argument := 441758015142146869716985053184, coefficient := (-441758015142146869716985053184) }, { argument := 930586847549864490850257469440, coefficient := (-930586847549864490850257469440) }, { argument := 35791801828840941955779133440, coefficient := (-35791801828840941955779133440) }, { argument := 920360618455909936005749145600, coefficient := (-920360618455909936005749145600) }, { argument := 35791801828840941955779133440, coefficient := (-35791801828840941955779133440) }, { argument := 930586847549864490850257469440, coefficient := (-930586847549864490850257469440) }, { argument := 930586847549864490850257469440, coefficient := (-930586847549864490850257469440) }, { argument := 30755450264462385274310098944, coefficient := (-30755450264462385274310098944) }, { argument := 645258716735649586895388672, coefficient := (-645258716735649586895388672) }, { argument := 54259316306882349011560300544, coefficient := (-54259316306882349011560300544) }, { argument := 54259303216611585705419735040, coefficient := (-54259303216611585705419735040) }, { argument := 645271807006412893035954176, coefficient := (-645271807006412893035954176) }, { argument := 791543138151638287549202432, coefficient := (-791543138151638287549202432) }, { argument := 126367640193814286484241383424, coefficient := (-126367640193814286484241383424) }, { argument := 1260959017365166102957715881984, coefficient := (-1260959017365166102957715881984) }, { argument := 126367640193814286484241383424, coefficient := (-126367640193814286484241383424) }, { argument := 791452820586810396370796544, coefficient := (-791452820586810396370796544) }, { argument := 24501379497425016793547669504, coefficient := (-24501379497425016793547669504) }, { argument := 15385822361671228069221761024, coefficient := (-15385822361671228069221761024) }, { argument := 438079517564654400797967122432, coefficient := (-438079517564654400797967122432) }, { argument := 121062128582623610334139645952, coefficient := (-121062128582623610334139645952) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 438079413165306315638759751680, coefficient := (-438079413165306315638759751680) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 624340475834132465335261986816, coefficient := (-624340475834132465335261986816) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 121062128582623610334139645952, coefficient := (-121062128582623610334139645952) }, { argument := 624340475834132465335261986816, coefficient := (-624340475834132465335261986816) }, { argument := 24501483896773101952755040256, coefficient := (-24501483896773101952755040256) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 14576042237372742381367984128, coefficient := (-14576042237372742381367984128) }, { argument := 15385822361671228069221761024, coefficient := (-15385822361671228069221761024) }, { argument := 95302852754043405858766848, coefficient := (-95302852754043405858766848) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 151821152592461470590226661376, coefficient := (-151821152592461470590226661376) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18
