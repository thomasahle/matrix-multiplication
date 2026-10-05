import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 19, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19

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
def constantNumerator : ℤ := (-6816058763898909251463859606126592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2350179, 34988957, 209, 539, 451, 12617,
    69887809, 451, 407, 209, 209, 407,
    12617, 407, 4700351, 539, 4652413455655, 1013229705481529,
    309480951837, 32063579276018251, 97937010075, 11752441209, 309480951837, 615044423271,
    97937010075, 9492055016469, 607209462465, 4052921900545009, 309480951837, 11752441209,
    607209462465, 11752441209, 309480951837, 309480951837, 4652413455655, 3479842737264799,
    6199114843, 61131676128881581, 64863908967, 2872760537, 122263321704695663, 2872760537,
    5594323151, 105687348177, 5594323151, 64863908967, 105687348177, 434981620363539,
    5594323151, 5594323151, 6199114843, 1393265, 57082325, 1175369275,
    57082325, 1393265, 82295325, 12882871575, 3220719075, 329186025,
    3507258032250355, 42062055, 34851417, 12746877946526797
  ]
def negativeCoefficients : Array ℕ := #[
    22196813076688199837357703168, 330461355614734505974530310144, 16170591763165279840869810176, 20851552536713124005332123648, 279155478858853251989752512512, 488096546114488841512570322944,
    330035846782795536592550232064, 279155478858853251989752512512, 15745049874660930371373236224, 16170591763165279840869810176, 16170591763165279840869810176, 15745049874660930371373236224,
    488096546114488841512570322944, 15745049874660930371373236224, 22196780020122819749841207296, 20851552536713124005332123648, 41905215010522679232702709760, 2281590462023665706375883784192,
    713614489278146365199770189824, 18050190459955019139530004365312, 451654740049459724809981132800, 27099284402967583488598867968, 713614489278146365199770189824, 709097941877651767951670378496,
    451654740049459724809981132800, 10943594351398409132145842847744, 700064847076662573455470755840, 2281592195132028122696995831808, 713614489278146365199770189824, 27099284402967583488598867968,
    700064847076662573455470755840, 27099284402967583488598867968, 713614489278146365199770189824, 713614489278146365199770189824, 41905215010522679232702709760, 979488653428354724463476998144,
    114353484992355167493620236288, 34414074229320616699727049654272, 1196527928334643094018611740672, 105986156822182838164818755584, 34414065629396653979601289084928, 105986156822182838164818755584,
    103197047432125395055218262016, 3899174927300305467221490008064, 103197047432125395055218262016, 1196527928334643094018611740672, 3899174927300305467221490008064, 979491531691124397609081372672,
    103197047432125395055218262016, 103197047432125395055218262016, 114353484992355167493620236288, 51402405763713876864532480, 8423864323258500647590297600, 86726944832106168973891993600,
    8423864323258500647590297600, 51402405763713876864532480, 12144646389902012046743961600, 475294069756984974639523430400, 475294244078716471194786201600, 12144820711633508602006732800,
    987205372945929863783388282880, 12414527420788723425560494080, 642895170005130320252239872, 3587927173132204762898819448832
  ]
def negativeScales : Array ℕ := #[
    21, 25, 7, 9, 8, 13,
    26, 8, 8, 7, 7, 8,
    13, 8, 22, 9, 42, 49,
    38, 54, 36, 33, 38, 39,
    36, 43, 39, 51, 38, 33,
    39, 33, 38, 38, 42, 51,
    32, 55, 35, 31, 56, 31,
    32, 36, 32, 35, 36, 48,
    32, 32, 32, 20, 25, 30,
    25, 20, 26, 33, 31, 28,
    51, 25, 25, 53
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21164339212317696, 25060396323549088, 7707359132166870, 9074141462752506, 8816983624165144, 13623081294663700,
    26058537482771596, 8816983624165144, 8668884984300449, 7707359132166870, 7707359132166870, 8668884984300449,
    13623081294663700, 8668884984300449, 22164337063785008, 9074141462752506, 42081116452122751, 49847882704139148,
    38171059659869406, 54831785002785500, 36511135101467419, 33452241412413510, 38171059659869406, 39161899660583930,
    36511135101467419, 43109857601143650, 39143403316966541, 51847883800017664, 38171059659869406, 33452241412413510,
    39143403316966541, 33452241412413510, 38171059659869406, 38171059659869406, 42081116452122751, 51627943531897965,
    32529415085167009, 55762769642437817, 35916696923921768, 31419790593991822, 56762769281914701, 31419790593991822,
    32381316446177174, 36621011725933668, 32381316446177174, 35916696923921768, 36621011725933668, 48627947771303200,
    32381316446177174, 32381316446177174, 32529415085167009, 20410038254991501, 25766540762445095, 30130466944830274,
    25766540762445095, 20410038254991501, 26294307141141734, 33584735152987031, 31584735682118505, 28294327849138043,
    51639264998244058, 25326016000869072, 25054713979051677, 53500993453704603
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
noncomputable def negativeCeiling : ℝ := 39941207271 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22196813076688199837357703168, coefficient := (-22196813076688199837357703168) }, { argument := 330461355614734505974530310144, coefficient := (-330461355614734505974530310144) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 20851552536713124005332123648, coefficient := (-20851552536713124005332123648) }, { argument := 279155478858853251989752512512, coefficient := (-279155478858853251989752512512) }, { argument := 488096546114488841512570322944, coefficient := (-488096546114488841512570322944) }, { argument := 330035846782795536592550232064, coefficient := (-330035846782795536592550232064) }, { argument := 279155478858853251989752512512, coefficient := (-279155478858853251989752512512) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 488096546114488841512570322944, coefficient := (-488096546114488841512570322944) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 22196780020122819749841207296, coefficient := (-22196780020122819749841207296) }, { argument := 20851552536713124005332123648, coefficient := (-20851552536713124005332123648) }, { argument := 41905215010522679232702709760, coefficient := (-41905215010522679232702709760) }, { argument := 2281590462023665706375883784192, coefficient := (-2281590462023665706375883784192) }, { argument := 713614489278146365199770189824, coefficient := (-713614489278146365199770189824) }, { argument := 18050190459955019139530004365312, coefficient := (-18050190459955019139530004365312) }, { argument := 451654740049459724809981132800, coefficient := (-451654740049459724809981132800) }, { argument := 27099284402967583488598867968, coefficient := (-27099284402967583488598867968) }, { argument := 713614489278146365199770189824, coefficient := (-713614489278146365199770189824) }, { argument := 709097941877651767951670378496, coefficient := (-709097941877651767951670378496) }, { argument := 451654740049459724809981132800, coefficient := (-451654740049459724809981132800) }, { argument := 10943594351398409132145842847744, coefficient := (-10943594351398409132145842847744) }, { argument := 700064847076662573455470755840, coefficient := (-700064847076662573455470755840) }, { argument := 2281592195132028122696995831808, coefficient := (-2281592195132028122696995831808) }, { argument := 713614489278146365199770189824, coefficient := (-713614489278146365199770189824) }, { argument := 27099284402967583488598867968, coefficient := (-27099284402967583488598867968) }, { argument := 700064847076662573455470755840, coefficient := (-700064847076662573455470755840) }, { argument := 27099284402967583488598867968, coefficient := (-27099284402967583488598867968) }, { argument := 713614489278146365199770189824, coefficient := (-713614489278146365199770189824) }, { argument := 713614489278146365199770189824, coefficient := (-713614489278146365199770189824) }, { argument := 41905215010522679232702709760, coefficient := (-41905215010522679232702709760) }, { argument := 979488653428354724463476998144, coefficient := (-979488653428354724463476998144) }, { argument := 114353484992355167493620236288, coefficient := (-114353484992355167493620236288) }, { argument := 34414074229320616699727049654272, coefficient := (-34414074229320616699727049654272) }, { argument := 1196527928334643094018611740672, coefficient := (-1196527928334643094018611740672) }, { argument := 105986156822182838164818755584, coefficient := (-105986156822182838164818755584) }, { argument := 34414065629396653979601289084928, coefficient := (-34414065629396653979601289084928) }, { argument := 105986156822182838164818755584, coefficient := (-105986156822182838164818755584) }, { argument := 103197047432125395055218262016, coefficient := (-103197047432125395055218262016) }, { argument := 3899174927300305467221490008064, coefficient := (-3899174927300305467221490008064) }, { argument := 103197047432125395055218262016, coefficient := (-103197047432125395055218262016) }, { argument := 1196527928334643094018611740672, coefficient := (-1196527928334643094018611740672) }, { argument := 3899174927300305467221490008064, coefficient := (-3899174927300305467221490008064) }, { argument := 979491531691124397609081372672, coefficient := (-979491531691124397609081372672) }, { argument := 103197047432125395055218262016, coefficient := (-103197047432125395055218262016) }, { argument := 103197047432125395055218262016, coefficient := (-103197047432125395055218262016) }, { argument := 114353484992355167493620236288, coefficient := (-114353484992355167493620236288) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 86726944832106168973891993600, coefficient := (-86726944832106168973891993600) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 12144646389902012046743961600, coefficient := (-12144646389902012046743961600) }, { argument := 475294069756984974639523430400, coefficient := (-475294069756984974639523430400) }, { argument := 475294244078716471194786201600, coefficient := (-475294244078716471194786201600) }, { argument := 12144820711633508602006732800, coefficient := (-12144820711633508602006732800) }, { argument := 987205372945929863783388282880, coefficient := (-987205372945929863783388282880) }, { argument := 12414527420788723425560494080, coefficient := (-12414527420788723425560494080) }, { argument := 642895170005130320252239872, coefficient := (-642895170005130320252239872) }, { argument := 3587927173132204762898819448832, coefficient := (-3587927173132204762898819448832) }] }

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
def constantNumerator : ℤ := (-27916774742327224810531303427407872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    234345735, 54799710953111, 938584713, 938584713, 671791107, 34851417,
    68187555, 10674379305, 2668595805, 272754135, 12699157591, 47174205785,
    793530277, 9210476023615, 1393265, 9210475376833, 1393265, 4652413113049,
    1013229839594183, 309480878051, 32063585989066165, 97936986725, 11752438407, 309480878051,
    615044276633, 97936986725, 9492052753387, 607209317695, 4052922436996111, 309480878051,
    11752438407, 607209317695, 11752438407, 309480878051, 309480878051, 4652413113049,
    12645906297095173, 23028166805, 6925309290770107, 240953257545, 10671589495, 443219685175613041,
    10671589495, 20781516385, 392602160895, 20781516385, 240953257545, 392602160895,
    6322971771616101, 20781516385, 20781516385, 23028166805, 61502063352231977, 6584578805,
    5455793867, 111484420358415989, 36685510485, 61502036570561261, 146930172763, 146930172763,
    105165130057, 5455793867, 458502525, 71775998775
  ]
def negativeCoefficients : Array ℕ := #[
    17291663193241436199887831040, 987183831313766351195523252224, 17313831992207130348862046208, 17313831992207130348862046208, 12392358621823029276586278912, 642895170005130320252239872,
    628919188048497052420669440, 24613442898129579043832463360, 24613451925504960115444285440, 628928215423878124032491520, 117129055016441457966766358528, 435105250498201798126631649280,
    117104399476470791291122221056, 41480296387857401716450263040, 51402405763713876864532480, 41480293475010227526506119168, 51402405763713876864532480, 41905211924602171362910404608,
    2281590764018514996410013712384, 713614319139214087358148247552, 18050194239065029640865689108480, 451654632366591194530473574400, 27099277941995471671828414464, 713614319139214087358148247552,
    709097772815548175412843511808, 451654632366591194530473574400, 10943591742242504643473374707712, 700064680168216351522234040320, 2281592497127151006408488517632, 713614319139214087358148247552,
    27099277941995471671828414464, 700064680168216351522234040320, 27099277941995471671828414464, 713614319139214087358148247552, 713614319139214087358148247552, 41905211924602171362910404608,
    3559506180460001875359315263488, 424794699538528769735005306880, 124755281365350751275773002252288, 4444803075659240054056518942720, 393712160547904713412931747840, 124755250562509965088922477264896,
    393712160547904713412931747840, 383351314217696694638907228160, 14484463169630810246086278512640, 383351314217696694638907228160, 4444803075659240054056518942720, 14484463169630810246086278512640,
    3559516664315554675036375744512, 383351314217696694638907228160, 383351314217696694638907228160, 424794699538528769735005306880, 34622583699453571212302639693824, 485856160196029085187068395520,
    25160408295865791911473184768, 125520298495944496544086948315136, 676728223130183368653416693760, 34622568622713289095187038994432, 677595823416247706305536458752, 677595823416247706305536458752,
    484988559909964747534948630528, 25160408295865791911473184768, 16915757471649231065107660800, 662016740018657643247907635200
  ]
def negativeScales : Array ℕ := #[
    27, 45, 29, 29, 29, 25,
    26, 33, 31, 28, 33, 35,
    29, 43, 20, 43, 20, 42,
    49, 38, 54, 36, 33, 38,
    39, 36, 43, 39, 51, 38,
    33, 39, 33, 38, 38, 42,
    53, 34, 52, 37, 33, 58,
    33, 34, 38, 34, 37, 38,
    52, 34, 34, 34, 55, 32,
    32, 56, 35, 55, 37, 37,
    36, 32, 28, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27804063298375387, 45639233517109698, 29805911722794518, 29805911722794518, 29323437456767296, 25054713979051677,
    26023005119324339, 33313433131165952, 31313433660297425, 28023025827320649, 33564013746692294, 35457279177993795,
    29563710028972239, 43066412859477622, 20410038254991501, 43066412758168069, 20410038254991501, 42081116345881979,
    49847882895096492, 38171059315904104, 54831785304837871, 36511134757502117, 33452241068448208, 38171059315904104,
    39161899316618628, 36511134757502117, 43109857257178348, 39143402973001239, 51847883990975036, 38171059315904104,
    33452241068448208, 39143402973001239, 33452241068448208, 38171059315904104, 38171059315904104, 42081116345881979,
    53489519952863895, 34422680516469784, 52620799928026756, 37809962350141679, 33313056025295270, 58620799571816497,
    33313056025295270, 34274581877480634, 38514277157227554, 34274581877480634, 37809962350141679, 38514277157227554,
    52489524202044364, 34274581877480634, 34274581877480634, 34422680516469784, 55771484331252265, 32616444012719541,
    32345141990893291, 56629619724659409, 35094491309515329, 55771483703016558, 37096339733907697, 37096339733907697,
    36613865468617170, 32345141990893291, 28772354438310123, 36062782449787990
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
noncomputable def negativeCeiling : ℝ := 87103967671 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17291663193241436199887831040, coefficient := (-17291663193241436199887831040) }, { argument := 987183831313766351195523252224, coefficient := (-987183831313766351195523252224) }, { argument := 17313831992207130348862046208, coefficient := (-17313831992207130348862046208) }, { argument := 17313831992207130348862046208, coefficient := (-17313831992207130348862046208) }, { argument := 12392358621823029276586278912, coefficient := (-12392358621823029276586278912) }, { argument := 642895170005130320252239872, coefficient := (-642895170005130320252239872) }, { argument := 628919188048497052420669440, coefficient := (-628919188048497052420669440) }, { argument := 24613442898129579043832463360, coefficient := (-24613442898129579043832463360) }, { argument := 24613451925504960115444285440, coefficient := (-24613451925504960115444285440) }, { argument := 628928215423878124032491520, coefficient := (-628928215423878124032491520) }, { argument := 117129055016441457966766358528, coefficient := (-117129055016441457966766358528) }, { argument := 435105250498201798126631649280, coefficient := (-435105250498201798126631649280) }, { argument := 117104399476470791291122221056, coefficient := (-117104399476470791291122221056) }, { argument := 41480296387857401716450263040, coefficient := (-41480296387857401716450263040) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 41480293475010227526506119168, coefficient := (-41480293475010227526506119168) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 41905211924602171362910404608, coefficient := (-41905211924602171362910404608) }, { argument := 2281590764018514996410013712384, coefficient := (-2281590764018514996410013712384) }, { argument := 713614319139214087358148247552, coefficient := (-713614319139214087358148247552) }, { argument := 18050194239065029640865689108480, coefficient := (-18050194239065029640865689108480) }, { argument := 451654632366591194530473574400, coefficient := (-451654632366591194530473574400) }, { argument := 27099277941995471671828414464, coefficient := (-27099277941995471671828414464) }, { argument := 713614319139214087358148247552, coefficient := (-713614319139214087358148247552) }, { argument := 709097772815548175412843511808, coefficient := (-709097772815548175412843511808) }, { argument := 451654632366591194530473574400, coefficient := (-451654632366591194530473574400) }, { argument := 10943591742242504643473374707712, coefficient := (-10943591742242504643473374707712) }, { argument := 700064680168216351522234040320, coefficient := (-700064680168216351522234040320) }, { argument := 2281592497127151006408488517632, coefficient := (-2281592497127151006408488517632) }, { argument := 713614319139214087358148247552, coefficient := (-713614319139214087358148247552) }, { argument := 27099277941995471671828414464, coefficient := (-27099277941995471671828414464) }, { argument := 700064680168216351522234040320, coefficient := (-700064680168216351522234040320) }, { argument := 27099277941995471671828414464, coefficient := (-27099277941995471671828414464) }, { argument := 713614319139214087358148247552, coefficient := (-713614319139214087358148247552) }, { argument := 713614319139214087358148247552, coefficient := (-713614319139214087358148247552) }, { argument := 41905211924602171362910404608, coefficient := (-41905211924602171362910404608) }, { argument := 3559506180460001875359315263488, coefficient := (-3559506180460001875359315263488) }, { argument := 424794699538528769735005306880, coefficient := (-424794699538528769735005306880) }, { argument := 124755281365350751275773002252288, coefficient := (-124755281365350751275773002252288) }, { argument := 4444803075659240054056518942720, coefficient := (-4444803075659240054056518942720) }, { argument := 393712160547904713412931747840, coefficient := (-393712160547904713412931747840) }, { argument := 124755250562509965088922477264896, coefficient := (-124755250562509965088922477264896) }, { argument := 393712160547904713412931747840, coefficient := (-393712160547904713412931747840) }, { argument := 383351314217696694638907228160, coefficient := (-383351314217696694638907228160) }, { argument := 14484463169630810246086278512640, coefficient := (-14484463169630810246086278512640) }, { argument := 383351314217696694638907228160, coefficient := (-383351314217696694638907228160) }, { argument := 4444803075659240054056518942720, coefficient := (-4444803075659240054056518942720) }, { argument := 14484463169630810246086278512640, coefficient := (-14484463169630810246086278512640) }, { argument := 3559516664315554675036375744512, coefficient := (-3559516664315554675036375744512) }, { argument := 383351314217696694638907228160, coefficient := (-383351314217696694638907228160) }, { argument := 383351314217696694638907228160, coefficient := (-383351314217696694638907228160) }, { argument := 424794699538528769735005306880, coefficient := (-424794699538528769735005306880) }, { argument := 34622583699453571212302639693824, coefficient := (-34622583699453571212302639693824) }, { argument := 485856160196029085187068395520, coefficient := (-485856160196029085187068395520) }, { argument := 25160408295865791911473184768, coefficient := (-25160408295865791911473184768) }, { argument := 125520298495944496544086948315136, coefficient := (-125520298495944496544086948315136) }, { argument := 676728223130183368653416693760, coefficient := (-676728223130183368653416693760) }, { argument := 34622568622713289095187038994432, coefficient := (-34622568622713289095187038994432) }, { argument := 677595823416247706305536458752, coefficient := (-677595823416247706305536458752) }, { argument := 677595823416247706305536458752, coefficient := (-677595823416247706305536458752) }, { argument := 484988559909964747534948630528, coefficient := (-484988559909964747534948630528) }, { argument := 25160408295865791911473184768, coefficient := (-25160408295865791911473184768) }, { argument := 16915757471649231065107660800, coefficient := (-16915757471649231065107660800) }, { argument := 662016740018657643247907635200, coefficient := (-662016740018657643247907635200) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19
