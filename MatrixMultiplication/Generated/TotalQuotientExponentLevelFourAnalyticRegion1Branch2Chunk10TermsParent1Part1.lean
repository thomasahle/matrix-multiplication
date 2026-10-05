import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6243331067985116417761344403537920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    408602551211583, 331455, 1392111, 6032481, 198873, 198873,
    464037, 6032481, 6032481, 198873, 74444793, 2983095,
    1392111, 6032481, 464037, 2983095, 464037, 6032481,
    6032481, 198873, 1335393877254915, 28623, 3053409566339731, 708267,
    22533, 12213290372495229, 11571, 11571, 391587, 21315,
    708267, 391587, 1336786696050137, 22533, 21315, 28623,
    10545, 44289, 191919, 6327, 6327, 14763,
    191919, 191919, 6327, 2368407, 94905, 44289,
    191919, 14763, 94905, 14763, 191919, 191919,
    6327, 794503119, 124033, 26994888241, 3069157, 97643,
    215959053143, 50141, 50141, 1696877
  ]
def negativeCoefficients : Array ℕ := #[
    460045574344779801923306913792, 1565251982579558254305607680, 26296233307336578672334209024, 56975172165895920456724119552, 1878302379095469905166729216, 30052838065527518482667667456,
    2191352775611381556027850752, 56975172165895920456724119552, 56975172165895920456724119552, 30052838065527518482667667456, 703111190574737567834078969856, 56349071372864097155001876480,
    26296233307336578672334209024, 56975172165895920456724119552, 2191352775611381556027850752, 56349071372864097155001876480, 2191352775611381556027850752, 56975172165895920456724119552,
    56975172165895920456724119552, 1878302379095469905166729216, 1503519841999519266966035496960, 1081346366713422839612964864, 55005336740708481270283767906304, 26757570733781080052550598656,
    851272671668013724801695744, 55003769970537179613527575363584, 874280041172554636282822656, 874280041172554636282822656, 14793738591419806082364604416, 805257932658931901839441920,
    26757570733781080052550598656, 14793738591419806082364604416, 1505088016551308372559672639488, 851272671668013724801695744, 805257932658931901839441920, 1081346366713422839612964864,
    49797354561860408778424320, 836595556639254867477528576, 1812623706051718879534645248, 59756825474232490534109184, 956109207587719848545746944, 69716296386604572289794048,
    1812623706051718879534645248, 1812623706051718879534645248, 956109207587719848545746944, 22368971669187695623268204544, 1792704764226974716023275520, 836595556639254867477528576,
    1812623706051718879534645248, 69716296386604572289794048, 1792704764226974716023275520, 69716296386604572289794048, 1812623706051718879534645248, 1812623706051718879534645248,
    59756825474232490534109184, 29311991403914009318006980608, 2342917127879082819161423872, 995935589360236824336281894912, 57974736589859006780526297088, 1844424121947363070403674112,
    995935345932390341646611382272, 1894273422540535045279449088, 1894273422540535045279449088, 32053100281409579845123309568
  ]
def negativeScales : Array ℕ := #[
    48, 18, 20, 22, 17, 17,
    18, 22, 22, 17, 26, 21,
    20, 22, 18, 21, 18, 22,
    22, 17, 50, 14, 51, 19,
    14, 53, 13, 13, 18, 14,
    19, 18, 50, 14, 14, 14,
    13, 15, 17, 12, 12, 13,
    17, 17, 12, 21, 16, 15,
    17, 13, 16, 13, 17, 17,
    12, 29, 16, 34, 21, 16,
    37, 15, 15, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48537691540348304, 18338453490525323, 20408842818416730, 22524320035837256, 17601487896365009, 17601487896365009,
    18823880318738715, 22524320035837256, 22524320035837256, 17601487896365009, 26149667608038562, 21508378491967993,
    20408842818416730, 22524320035837256, 18823880318738715, 21508378491967993, 18823880318738715, 22524320035837256,
    22524320035837256, 17601487896365009, 50246186753951090, 14804887270297456, 51439342540433588, 19433933799379577,
    14459751783535349, 53439301446171047, 13498225931350174, 13498225931350174, 18578973345237406, 14379581434851302,
    19433933799379577, 18578973345237406, 50247690703924209, 14459751783535349, 14379581434851302, 14804887270297456,
    13364271474681056, 15434660802572478, 17550138019993724, 12627305880526679, 12627305880526679, 13849698303573471,
    17550138019993724, 17550138019993724, 12627305880526679, 21175485592194293, 16534196476124184, 15434660802572478,
    17550138019993724, 13849698303573471, 16534196476124184, 13849698303573471, 17550138019993724, 17550138019993724,
    12627305880526679, 29565477642308537, 16920364493267946, 34651967192929391, 21549411016800793, 16575229000958025,
    37651966840303987, 15613703148778080, 15613703148778080, 20694450562717709
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
noncomputable def negativeCeiling : ℝ := 72830905053 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 460045574344779801923306913792, coefficient := (-460045574344779801923306913792) }, { argument := 1565251982579558254305607680, coefficient := (-1565251982579558254305607680) }, { argument := 26296233307336578672334209024, coefficient := (-26296233307336578672334209024) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 1878302379095469905166729216, coefficient := (-1878302379095469905166729216) }, { argument := 30052838065527518482667667456, coefficient := (-30052838065527518482667667456) }, { argument := 2191352775611381556027850752, coefficient := (-2191352775611381556027850752) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 30052838065527518482667667456, coefficient := (-30052838065527518482667667456) }, { argument := 703111190574737567834078969856, coefficient := (-703111190574737567834078969856) }, { argument := 56349071372864097155001876480, coefficient := (-56349071372864097155001876480) }, { argument := 26296233307336578672334209024, coefficient := (-26296233307336578672334209024) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 2191352775611381556027850752, coefficient := (-2191352775611381556027850752) }, { argument := 56349071372864097155001876480, coefficient := (-56349071372864097155001876480) }, { argument := 2191352775611381556027850752, coefficient := (-2191352775611381556027850752) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 1878302379095469905166729216, coefficient := (-1878302379095469905166729216) }, { argument := 1503519841999519266966035496960, coefficient := (-1503519841999519266966035496960) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 55005336740708481270283767906304, coefficient := (-55005336740708481270283767906304) }, { argument := 26757570733781080052550598656, coefficient := (-26757570733781080052550598656) }, { argument := 851272671668013724801695744, coefficient := (-851272671668013724801695744) }, { argument := 55003769970537179613527575363584, coefficient := (-55003769970537179613527575363584) }, { argument := 874280041172554636282822656, coefficient := (-874280041172554636282822656) }, { argument := 874280041172554636282822656, coefficient := (-874280041172554636282822656) }, { argument := 14793738591419806082364604416, coefficient := (-14793738591419806082364604416) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 26757570733781080052550598656, coefficient := (-26757570733781080052550598656) }, { argument := 14793738591419806082364604416, coefficient := (-14793738591419806082364604416) }, { argument := 1505088016551308372559672639488, coefficient := (-1505088016551308372559672639488) }, { argument := 851272671668013724801695744, coefficient := (-851272671668013724801695744) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 836595556639254867477528576, coefficient := (-836595556639254867477528576) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 59756825474232490534109184, coefficient := (-59756825474232490534109184) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 69716296386604572289794048, coefficient := (-69716296386604572289794048) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 956109207587719848545746944, coefficient := (-956109207587719848545746944) }, { argument := 22368971669187695623268204544, coefficient := (-22368971669187695623268204544) }, { argument := 1792704764226974716023275520, coefficient := (-1792704764226974716023275520) }, { argument := 836595556639254867477528576, coefficient := (-836595556639254867477528576) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 69716296386604572289794048, coefficient := (-69716296386604572289794048) }, { argument := 1792704764226974716023275520, coefficient := (-1792704764226974716023275520) }, { argument := 69716296386604572289794048, coefficient := (-69716296386604572289794048) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 1812623706051718879534645248, coefficient := (-1812623706051718879534645248) }, { argument := 59756825474232490534109184, coefficient := (-59756825474232490534109184) }, { argument := 29311991403914009318006980608, coefficient := (-29311991403914009318006980608) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 995935589360236824336281894912, coefficient := (-995935589360236824336281894912) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 995935345932390341646611382272, coefficient := (-995935345932390341646611382272) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-95312181757594281511400165034950656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    92365, 3069157, 1696877, 6356077737, 97643, 92365,
    124033, 112536634880359, 196233258019737, 112536633751399, 111940416226589, 6219232617178339,
    73879725745, 33595868635, 1447735852479, 954626947953, 3109616876407343, 1447735852479,
    73879725745, 36864011877, 64040645739, 36864011877, 954626947953, 64040645739,
    55969640295121, 33595868635, 408584019212247, 48919911537791939, 435028360089, 252281864901970497,
    446009644957, 14221158149, 435028360089, 247708169559, 446009644957, 6966091707027,
    8538849795, 24459962842518465, 435028360089, 14221158149, 8538849795, 14221158149,
    218933272397, 247708169559, 204294619922481, 55039414413620391, 4089, 1007892125175365961,
    101181, 3219, 1007862120182226199, 1653, 1653, 55941,
    3045, 101181, 55941, 55099474186227353, 3219, 3045,
    4089, 5415, 22743, 98553
  ]
def negativeCoefficients : Array ℕ := #[
    1744725520761019120652124160, 57974736589859006780526297088, 32053100281409579845123309568, 29312234831760492007677493248, 1844424121947363070403674112, 1744725520761019120652124160,
    2342917127879082819161423872, 253409973456357177551363244032, 883756027695385949001379479552, 253409970914165259893265661952, 252067408402882222166294659072, 14004466848627401060306829443072,
    85177524565866608636062597120, 77466798830476356654485995520, 3338251594626729865079326507008, 1100609937172214957885387440128, 14004469405853115649102475952128, 3338251594626729865079326507008,
    85177524565866608636062597120, 85002624078151034277571067904, 73833837641401943663799435264, 85002624078151034277571067904, 1100609937172214957885387440128, 73833837641401943663799435264,
    252064851177167633370648150016, 77466798830476356654485995520, 460024709168453791953482416128, 55078923843149351107278128807936, 1003107102920918197300497481728, 568088256382424071836462540128256,
    1028428221865980119273978200064, 32791758100794005827876814848, 1003107102920918197300497481728, 571176151102740500726748807168, 1028428221865980119273978200064, 16062713864189695791112025800704,
    630055907408849078823294074880, 55078939771531168553957138104320, 1003107102920918197300497481728, 32791758100794005827876814848, 630055907408849078823294074880, 32791758100794005827876814848,
    1009651511281799677551614885888, 571176151102740500726748807168, 460030587078341270008693260288, 15492217890241943719361428586496, 77239026193815917115211776, 567392824921179431544633616760832,
    1911255052412934289467899904, 60805190833429551771549696, 567375933611688995740632731353088, 62448574369468188305915904, 62448574369468188305915904, 1056695613672843291597471744,
    57518423761352278702817280, 1911255052412934289467899904, 1056695613672843291597471744, 15509123213337735643506113773568, 60805190833429551771549696, 57518423761352278702817280,
    77239026193815917115211776, 51143229009478257664327680, 859206247359234728760705024, 1861613535945008578981527552
  ]
def negativeScales : Array ℕ := #[
    16, 21, 20, 32, 16, 16,
    16, 46, 47, 46, 46, 52,
    36, 34, 40, 39, 51, 40,
    36, 35, 35, 35, 39, 35,
    45, 34, 48, 55, 38, 57,
    38, 33, 38, 37, 38, 42,
    32, 54, 38, 33, 32, 33,
    37, 37, 47, 55, 11, 59,
    16, 11, 59, 10, 10, 15,
    11, 16, 15, 55, 11, 11,
    11, 12, 14, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16495058652271465, 21549411016800793, 20694450562717709, 32565489623435436, 16575229000958025, 16495058652271465,
    16920364493267946, 46677388057520645, 47479562901651816, 46677388043047624, 46669724345668312, 52465658002430026,
    36104459459657120, 34967564795077109, 40396935537283575, 39796146106842284, 51465658265867153, 40396935537283575,
    36104459459657120, 35101494035580024, 35898268808116011, 35101494035580024, 39796146106842284, 35898268808116011,
    45669709709442243, 34967564795077109, 48537626106028865, 55441271313230256, 38662318499064238, 57807814116801848,
    38698283952588596, 33727319909591375, 38662318499064238, 37849850495775703, 38698283952588596, 42663486604482916,
    32991394622818987, 54441271730445999, 38662318499064238, 33727319909591375, 32991394622818987, 33727319909591375,
    37671700268642762, 37849850495775703, 47537644539771881, 55611314638916666, 11997532370288072, 59806046943966561,
    16626578877333553, 11652396861500322, 59806003994231446, 10690871009350625, 10690871009350625, 15771618423534793,
    11572226512796267, 16626578877333553, 15771618423534793, 55612888069442534, 11652396861500322, 11572226512796267,
    11997532370288072, 12402745622495697, 14473134950387196, 16588612167811137
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
noncomputable def negativeCeiling : ℝ := 1341668928163 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 29312234831760492007677493248, coefficient := (-29312234831760492007677493248) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 253409973456357177551363244032, coefficient := (-253409973456357177551363244032) }, { argument := 883756027695385949001379479552, coefficient := (-883756027695385949001379479552) }, { argument := 253409970914165259893265661952, coefficient := (-253409970914165259893265661952) }, { argument := 252067408402882222166294659072, coefficient := (-252067408402882222166294659072) }, { argument := 14004466848627401060306829443072, coefficient := (-14004466848627401060306829443072) }, { argument := 85177524565866608636062597120, coefficient := (-85177524565866608636062597120) }, { argument := 77466798830476356654485995520, coefficient := (-77466798830476356654485995520) }, { argument := 3338251594626729865079326507008, coefficient := (-3338251594626729865079326507008) }, { argument := 1100609937172214957885387440128, coefficient := (-1100609937172214957885387440128) }, { argument := 14004469405853115649102475952128, coefficient := (-14004469405853115649102475952128) }, { argument := 3338251594626729865079326507008, coefficient := (-3338251594626729865079326507008) }, { argument := 85177524565866608636062597120, coefficient := (-85177524565866608636062597120) }, { argument := 85002624078151034277571067904, coefficient := (-85002624078151034277571067904) }, { argument := 73833837641401943663799435264, coefficient := (-73833837641401943663799435264) }, { argument := 85002624078151034277571067904, coefficient := (-85002624078151034277571067904) }, { argument := 1100609937172214957885387440128, coefficient := (-1100609937172214957885387440128) }, { argument := 73833837641401943663799435264, coefficient := (-73833837641401943663799435264) }, { argument := 252064851177167633370648150016, coefficient := (-252064851177167633370648150016) }, { argument := 77466798830476356654485995520, coefficient := (-77466798830476356654485995520) }, { argument := 460024709168453791953482416128, coefficient := (-460024709168453791953482416128) }, { argument := 55078923843149351107278128807936, coefficient := (-55078923843149351107278128807936) }, { argument := 1003107102920918197300497481728, coefficient := (-1003107102920918197300497481728) }, { argument := 568088256382424071836462540128256, coefficient := (-568088256382424071836462540128256) }, { argument := 1028428221865980119273978200064, coefficient := (-1028428221865980119273978200064) }, { argument := 32791758100794005827876814848, coefficient := (-32791758100794005827876814848) }, { argument := 1003107102920918197300497481728, coefficient := (-1003107102920918197300497481728) }, { argument := 571176151102740500726748807168, coefficient := (-571176151102740500726748807168) }, { argument := 1028428221865980119273978200064, coefficient := (-1028428221865980119273978200064) }, { argument := 16062713864189695791112025800704, coefficient := (-16062713864189695791112025800704) }, { argument := 630055907408849078823294074880, coefficient := (-630055907408849078823294074880) }, { argument := 55078939771531168553957138104320, coefficient := (-55078939771531168553957138104320) }, { argument := 1003107102920918197300497481728, coefficient := (-1003107102920918197300497481728) }, { argument := 32791758100794005827876814848, coefficient := (-32791758100794005827876814848) }, { argument := 630055907408849078823294074880, coefficient := (-630055907408849078823294074880) }, { argument := 32791758100794005827876814848, coefficient := (-32791758100794005827876814848) }, { argument := 1009651511281799677551614885888, coefficient := (-1009651511281799677551614885888) }, { argument := 571176151102740500726748807168, coefficient := (-571176151102740500726748807168) }, { argument := 460030587078341270008693260288, coefficient := (-460030587078341270008693260288) }, { argument := 15492217890241943719361428586496, coefficient := (-15492217890241943719361428586496) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 567392824921179431544633616760832, coefficient := (-567392824921179431544633616760832) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 567375933611688995740632731353088, coefficient := (-567375933611688995740632731353088) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 62448574369468188305915904, coefficient := (-62448574369468188305915904) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 15509123213337735643506113773568, coefficient := (-15509123213337735643506113773568) }, { argument := 60805190833429551771549696, coefficient := (-60805190833429551771549696) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 77239026193815917115211776, coefficient := (-77239026193815917115211776) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 859206247359234728760705024, coefficient := (-859206247359234728760705024) }, { argument := 1861613535945008578981527552, coefficient := (-1861613535945008578981527552) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
