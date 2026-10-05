import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2482007298197426920010164964687872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10331577, 678004327, 25037797785, 200302333231, 5424083665, 3663657135,
    39483693, 2218185, 13215234915, 119929869, 228978495, 119929869,
    119929869, 39483693, 2218185, 1764886185, 1803889815, 48880845,
    459479943, 5425773795, 381270591, 901944855, 5425773795, 48880845,
    381270591, 381270591, 381270591, 381270591, 381270591, 882443145,
    459479943, 11120591521, 23947744285, 201788806947, 66344088509, 6652378251,
    15522215919, 201788806947, 201788806947, 6652378251, 2490206925291, 99785673765,
    23947744285, 201788806947, 15522215919, 99785673765, 15522215919, 201788806947,
    201788806947, 13338047139, 1763330717, 66581883217, 128038480607, 1047788583257,
    31538786787, 128038474139, 31538786787, 31538786787, 2701822734753, 31538786787,
    1047788583257, 2701822734753, 28213293089, 31538786787
  ]
def negativeCoefficients : Array ℕ := #[
    95291978398411954078089216, 25013944602073365873755684864, 923731695818373776368855941120, 923731469619786258523906637824, 25014170800660883718704988160, 8447818192895620586951147520,
    364172789927958653586898944, 20459145501570710875668480, 30472257043869475010594734080, 553078900059128217338904576, 8447815391296364392312995840, 553078900059128217338904576,
    553078900059128217338904576, 364172789927958653586898944, 20459145501570710875668480, 8139100943480152337405706240, 8318973438619067357079797760, 7213539502573321340489564160,
    8475908915523652575075237888, 100087860598204833599292702720, 225062432480287625823274401792, 8318972954392035422204067840, 100087860598204833599292702720, 7213539502573321340489564160,
    7033201015008988306977325056, 7033201015008988306977325056, 7033201015008988306977325056, 225062432480287625823274401792, 7033201015008988306977325056, 8139101427707184272281436160,
    8475908915523652575075237888, 25642338217018929839700180992, 441757909968035533461976514560, 930586619672623262297738969088, 152979052691132214046325997568, 490858876310834248244961214464,
    35791793064331663934528421888, 930586619672623262297738969088, 930586619672623262297738969088, 490858876310834248244961214464, 11484052460355559599564405080064, 920360393082814215459302277120,
    441757909968035533461976514560, 930586619672623262297738969088, 35791793064331663934528421888, 920360393082814215459302277120, 35791793064331663934528421888, 930586619672623262297738969088,
    930586619672623262297738969088, 30755442752025861256095203328, 130110841815239058003159154688, 153527369956202025709243203584, 147618317708997037695992594432, 1208017989918536991764834680832,
    145446982063770340145598824448, 147618310251900745898906353664, 145446982063770340145598824448, 145446982063770340145598824448, 6229979065064829569569816313856, 145446982063770340145598824448,
    1208017989918536991764834680832, 6229979065064829569569816313856, 130110849272335349800245395456, 145446982063770340145598824448
  ]
def negativeScales : Array ℕ := #[
    23, 29, 34, 37, 32, 31,
    25, 21, 33, 26, 27, 26,
    26, 25, 21, 30, 30, 25,
    28, 32, 28, 29, 32, 25,
    28, 28, 28, 28, 28, 29,
    28, 33, 34, 37, 35, 32,
    33, 37, 37, 32, 41, 36,
    34, 37, 33, 36, 33, 37,
    37, 33, 30, 35, 36, 39,
    34, 36, 34, 34, 41, 34,
    39, 41, 34, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23300557146530098, 29336719239719401, 34543388623590196, 37543388270310535, 32336732285806700, 31770637348825224,
    25234753598879560, 21080948262800525, 33621483019545669, 26837615772774151, 27770636870375763, 26837615772774151,
    26837615772774151, 25234753598879560, 21080948262800525, 30716928003238422, 30748464072947851, 25542765889360499,
    28775426646537850, 32337181755709539, 28506240013334652, 29748463988972110, 32337181755709539, 25542765889360499,
    28506240013334652, 28506240013334652, 28506240013334652, 28506240013334652, 28506240013334652, 29716928089070005,
    28775426646537850, 33372514478096600, 34479170719152279, 37554055195362807, 35949248881299803, 32631223055896880,
    33853615479075798, 37554055195362807, 37554055195362807, 32631223055896880, 41179402767563209, 36538113651493206,
    34479170719152279, 37554055195362807, 33853615479075798, 36538113651493206, 33853615479075798, 37554055195362807,
    37554055195362807, 33634828401833274, 30715655935118448, 35954410636668666, 36897786510040860, 39930484793664317,
    34876408116283023, 36897786437161579, 34876408116283023, 34876408116283023, 41297070161912219, 34876408116283023,
    39930484793664317, 41297070161912219, 34715656017804221, 34876408116283023
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
noncomputable def negativeCeiling : ℝ := 9487464301 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 95291978398411954078089216, coefficient := (-95291978398411954078089216) }, { argument := 25013944602073365873755684864, coefficient := (-25013944602073365873755684864) }, { argument := 923731695818373776368855941120, coefficient := (-923731695818373776368855941120) }, { argument := 923731469619786258523906637824, coefficient := (-923731469619786258523906637824) }, { argument := 25014170800660883718704988160, coefficient := (-25014170800660883718704988160) }, { argument := 8447818192895620586951147520, coefficient := (-8447818192895620586951147520) }, { argument := 364172789927958653586898944, coefficient := (-364172789927958653586898944) }, { argument := 20459145501570710875668480, coefficient := (-20459145501570710875668480) }, { argument := 30472257043869475010594734080, coefficient := (-30472257043869475010594734080) }, { argument := 553078900059128217338904576, coefficient := (-553078900059128217338904576) }, { argument := 8447815391296364392312995840, coefficient := (-8447815391296364392312995840) }, { argument := 553078900059128217338904576, coefficient := (-553078900059128217338904576) }, { argument := 553078900059128217338904576, coefficient := (-553078900059128217338904576) }, { argument := 364172789927958653586898944, coefficient := (-364172789927958653586898944) }, { argument := 20459145501570710875668480, coefficient := (-20459145501570710875668480) }, { argument := 8139100943480152337405706240, coefficient := (-8139100943480152337405706240) }, { argument := 8318973438619067357079797760, coefficient := (-8318973438619067357079797760) }, { argument := 7213539502573321340489564160, coefficient := (-7213539502573321340489564160) }, { argument := 8475908915523652575075237888, coefficient := (-8475908915523652575075237888) }, { argument := 100087860598204833599292702720, coefficient := (-100087860598204833599292702720) }, { argument := 225062432480287625823274401792, coefficient := (-225062432480287625823274401792) }, { argument := 8318972954392035422204067840, coefficient := (-8318972954392035422204067840) }, { argument := 100087860598204833599292702720, coefficient := (-100087860598204833599292702720) }, { argument := 7213539502573321340489564160, coefficient := (-7213539502573321340489564160) }, { argument := 7033201015008988306977325056, coefficient := (-7033201015008988306977325056) }, { argument := 7033201015008988306977325056, coefficient := (-7033201015008988306977325056) }, { argument := 7033201015008988306977325056, coefficient := (-7033201015008988306977325056) }, { argument := 225062432480287625823274401792, coefficient := (-225062432480287625823274401792) }, { argument := 7033201015008988306977325056, coefficient := (-7033201015008988306977325056) }, { argument := 8139101427707184272281436160, coefficient := (-8139101427707184272281436160) }, { argument := 8475908915523652575075237888, coefficient := (-8475908915523652575075237888) }, { argument := 25642338217018929839700180992, coefficient := (-25642338217018929839700180992) }, { argument := 441757909968035533461976514560, coefficient := (-441757909968035533461976514560) }, { argument := 930586619672623262297738969088, coefficient := (-930586619672623262297738969088) }, { argument := 152979052691132214046325997568, coefficient := (-152979052691132214046325997568) }, { argument := 490858876310834248244961214464, coefficient := (-490858876310834248244961214464) }, { argument := 35791793064331663934528421888, coefficient := (-35791793064331663934528421888) }, { argument := 930586619672623262297738969088, coefficient := (-930586619672623262297738969088) }, { argument := 930586619672623262297738969088, coefficient := (-930586619672623262297738969088) }, { argument := 490858876310834248244961214464, coefficient := (-490858876310834248244961214464) }, { argument := 11484052460355559599564405080064, coefficient := (-11484052460355559599564405080064) }, { argument := 920360393082814215459302277120, coefficient := (-920360393082814215459302277120) }, { argument := 441757909968035533461976514560, coefficient := (-441757909968035533461976514560) }, { argument := 930586619672623262297738969088, coefficient := (-930586619672623262297738969088) }, { argument := 35791793064331663934528421888, coefficient := (-35791793064331663934528421888) }, { argument := 920360393082814215459302277120, coefficient := (-920360393082814215459302277120) }, { argument := 35791793064331663934528421888, coefficient := (-35791793064331663934528421888) }, { argument := 930586619672623262297738969088, coefficient := (-930586619672623262297738969088) }, { argument := 930586619672623262297738969088, coefficient := (-930586619672623262297738969088) }, { argument := 30755442752025861256095203328, coefficient := (-30755442752025861256095203328) }, { argument := 130110841815239058003159154688, coefficient := (-130110841815239058003159154688) }, { argument := 153527369956202025709243203584, coefficient := (-153527369956202025709243203584) }, { argument := 147618317708997037695992594432, coefficient := (-147618317708997037695992594432) }, { argument := 1208017989918536991764834680832, coefficient := (-1208017989918536991764834680832) }, { argument := 145446982063770340145598824448, coefficient := (-145446982063770340145598824448) }, { argument := 147618310251900745898906353664, coefficient := (-147618310251900745898906353664) }, { argument := 145446982063770340145598824448, coefficient := (-145446982063770340145598824448) }, { argument := 145446982063770340145598824448, coefficient := (-145446982063770340145598824448) }, { argument := 6229979065064829569569816313856, coefficient := (-6229979065064829569569816313856) }, { argument := 145446982063770340145598824448, coefficient := (-145446982063770340145598824448) }, { argument := 1208017989918536991764834680832, coefficient := (-1208017989918536991764834680832) }, { argument := 6229979065064829569569816313856, coefficient := (-6229979065064829569569816313856) }, { argument := 130110849272335349800245395456, coefficient := (-130110849272335349800245395456) }, { argument := 145446982063770340145598824448, coefficient := (-145446982063770340145598824448) }] }

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
def constantNumerator : ℤ := (-889385547606804529713439735545856)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31538786787, 66581883217, 2583189, 412398873, 16460482347, 412398873,
    10331577, 22351791, 825421905, 6603373623, 178815945, 3588712065,
    3320153811, 186525495, 21982531245, 10084811763, 224294445, 10084811763,
    10084811763, 3320153811, 186525495, 52154179, 1925984445, 15407871787,
    417237205, 406087155, 1452749985, 101521755, 31, 31,
    279836361, 23531227447, 11765610885, 139921019, 2583189, 412398873,
    16460482347, 412398873, 10331577, 279836361, 23531227447, 11765610885,
    139921019, 221293191, 35328836787, 1410114654393, 35328836787, 885071763,
    678004327, 25037797785, 200302333231, 5424083665, 2583189, 412398873,
    16460482347, 412398873, 10331577, 678004327, 25037797785, 200302333231,
    5424083665, 3817219257, 13655849859, 954304497
  ]
def negativeCoefficients : Array ℕ := #[
    145446982063770340145598824448, 153527369956202025709243203584, 95302852754043405858766848, 15214832933034496031547457536, 151821152592461470590226661376, 15214832933034496031547457536,
    95291978398411954078089216, 13194168581313423757585416192, 487243092299801552370385551360, 487242972986260883617005699072, 13194287894854092510965268480, 8275006627161089648759930880,
    30623013818434216352481804288, 1720394034743495300701224960, 50688265996104850181707530240, 46507985405899156295623114752, 8275004448139445941819146240, 46507985405899156295623114752,
    46507985405899156295623114752, 30623013818434216352481804288, 1720394034743495300701224960, 962074792387437148990603264, 35528142146860529860340613120, 35528133446914856097073332224,
    962083492333110912257884160, 7490985819905822112067092480, 26798507176380390004500725760, 7490983329595372161277624320, 299813603264428035327131648, 299813603264428035327131648,
    645258716735649586895388672, 54259316306882349011560300544, 54259303216611585705419735040, 645271807006412893035954176, 95302852754043405858766848, 15214832933034496031547457536,
    151821152592461470590226661376, 15214832933034496031547457536, 95291978398411954078089216, 645258716735649586895388672, 54259316306882349011560300544, 54259303216611585705419735040,
    645271807006412893035954176, 4082138859631525884283846656, 651702010631644246684616097792, 6503006036043766323614708662272, 651702010631644246684616097792, 4081673074731978699678154752,
    25013944602073365873755684864, 923731695818373776368855941120, 923731469619786258523906637824, 25014170800660883718704988160, 95302852754043405858766848, 15214832933034496031547457536,
    151821152592461470590226661376, 15214832933034496031547457536, 95291978398411954078089216, 25013944602073365873755684864, 923731695818373776368855941120, 923731469619786258523906637824,
    25014170800660883718704988160, 8801908338389340981678833664, 31488245932246958255288352768, 8801905412274562289501208576
  ]
def negativeScales : Array ℕ := #[
    34, 35, 21, 28, 33, 28,
    23, 24, 29, 32, 27, 31,
    31, 27, 34, 33, 27, 33,
    33, 31, 27, 25, 30, 33,
    28, 28, 30, 26, 4, 4,
    28, 34, 33, 27, 21, 28,
    33, 28, 23, 28, 34, 33,
    27, 27, 35, 40, 35, 29,
    29, 34, 37, 32, 21, 28,
    33, 28, 23, 29, 34, 37,
    32, 31, 33, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34876408116283023, 35954410636668666, 21300721771969986, 28619465149235639, 33938287569567980, 28619465149235639,
    23300557146530098, 24413887100241872, 29620556484121458, 32620556130841797, 27413900146329171, 31740819029466455,
    31628602932084824, 27474797595993660, 34355638468206770, 33231465104602301, 27740818649567769, 33231465104602301,
    33231465104602301, 31628602932084824, 27474797595993660, 25636279521593277, 30842948906961092, 33842948553681421,
    28636292567680581, 28597214152998034, 30436139293752432, 26597213673387043, 4954196321574415, 4954196321574415,
    28060008192745727, 34453857525938802, 33453857177882979, 27060037460195613, 21300721771969986, 28619465149235639,
    33938287569567980, 28619465149235639, 23300557146530098, 28060008192745727, 34453857525938802, 33453857177882979,
    27060037460195613, 27721383820561463, 35040127197698756, 40358949609498899, 35040127197698756, 29721219195121131,
    29336719239719401, 34543388623590196, 37543388270310535, 32336732285806700, 21300721771969986, 28619465149235639,
    33938287569567980, 28619465149235639, 23300557146530098, 29336719239719401, 34543388623590196, 37543388270310535,
    32336732285806700, 31829874910956773, 33668800050576809, 29829874431345771
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
noncomputable def negativeCeiling : ℝ := 6329534817 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 145446982063770340145598824448, coefficient := (-145446982063770340145598824448) }, { argument := 153527369956202025709243203584, coefficient := (-153527369956202025709243203584) }, { argument := 95302852754043405858766848, coefficient := (-95302852754043405858766848) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 151821152592461470590226661376, coefficient := (-151821152592461470590226661376) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 95291978398411954078089216, coefficient := (-95291978398411954078089216) }, { argument := 13194168581313423757585416192, coefficient := (-13194168581313423757585416192) }, { argument := 487243092299801552370385551360, coefficient := (-487243092299801552370385551360) }, { argument := 487242972986260883617005699072, coefficient := (-487242972986260883617005699072) }, { argument := 13194287894854092510965268480, coefficient := (-13194287894854092510965268480) }, { argument := 8275006627161089648759930880, coefficient := (-8275006627161089648759930880) }, { argument := 30623013818434216352481804288, coefficient := (-30623013818434216352481804288) }, { argument := 1720394034743495300701224960, coefficient := (-1720394034743495300701224960) }, { argument := 50688265996104850181707530240, coefficient := (-50688265996104850181707530240) }, { argument := 46507985405899156295623114752, coefficient := (-46507985405899156295623114752) }, { argument := 8275004448139445941819146240, coefficient := (-8275004448139445941819146240) }, { argument := 46507985405899156295623114752, coefficient := (-46507985405899156295623114752) }, { argument := 46507985405899156295623114752, coefficient := (-46507985405899156295623114752) }, { argument := 30623013818434216352481804288, coefficient := (-30623013818434216352481804288) }, { argument := 1720394034743495300701224960, coefficient := (-1720394034743495300701224960) }, { argument := 962074792387437148990603264, coefficient := (-962074792387437148990603264) }, { argument := 35528142146860529860340613120, coefficient := (-35528142146860529860340613120) }, { argument := 35528133446914856097073332224, coefficient := (-35528133446914856097073332224) }, { argument := 962083492333110912257884160, coefficient := (-962083492333110912257884160) }, { argument := 7490985819905822112067092480, coefficient := (-7490985819905822112067092480) }, { argument := 26798507176380390004500725760, coefficient := (-26798507176380390004500725760) }, { argument := 7490983329595372161277624320, coefficient := (-7490983329595372161277624320) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 645258716735649586895388672, coefficient := (-645258716735649586895388672) }, { argument := 54259316306882349011560300544, coefficient := (-54259316306882349011560300544) }, { argument := 54259303216611585705419735040, coefficient := (-54259303216611585705419735040) }, { argument := 645271807006412893035954176, coefficient := (-645271807006412893035954176) }, { argument := 95302852754043405858766848, coefficient := (-95302852754043405858766848) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 151821152592461470590226661376, coefficient := (-151821152592461470590226661376) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 95291978398411954078089216, coefficient := (-95291978398411954078089216) }, { argument := 645258716735649586895388672, coefficient := (-645258716735649586895388672) }, { argument := 54259316306882349011560300544, coefficient := (-54259316306882349011560300544) }, { argument := 54259303216611585705419735040, coefficient := (-54259303216611585705419735040) }, { argument := 645271807006412893035954176, coefficient := (-645271807006412893035954176) }, { argument := 4082138859631525884283846656, coefficient := (-4082138859631525884283846656) }, { argument := 651702010631644246684616097792, coefficient := (-651702010631644246684616097792) }, { argument := 6503006036043766323614708662272, coefficient := (-6503006036043766323614708662272) }, { argument := 651702010631644246684616097792, coefficient := (-651702010631644246684616097792) }, { argument := 4081673074731978699678154752, coefficient := (-4081673074731978699678154752) }, { argument := 25013944602073365873755684864, coefficient := (-25013944602073365873755684864) }, { argument := 923731695818373776368855941120, coefficient := (-923731695818373776368855941120) }, { argument := 923731469619786258523906637824, coefficient := (-923731469619786258523906637824) }, { argument := 25014170800660883718704988160, coefficient := (-25014170800660883718704988160) }, { argument := 95302852754043405858766848, coefficient := (-95302852754043405858766848) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 151821152592461470590226661376, coefficient := (-151821152592461470590226661376) }, { argument := 15214832933034496031547457536, coefficient := (-15214832933034496031547457536) }, { argument := 95291978398411954078089216, coefficient := (-95291978398411954078089216) }, { argument := 25013944602073365873755684864, coefficient := (-25013944602073365873755684864) }, { argument := 923731695818373776368855941120, coefficient := (-923731695818373776368855941120) }, { argument := 923731469619786258523906637824, coefficient := (-923731469619786258523906637824) }, { argument := 25014170800660883718704988160, coefficient := (-25014170800660883718704988160) }, { argument := 8801908338389340981678833664, coefficient := (-8801908338389340981678833664) }, { argument := 31488245932246958255288352768, coefficient := (-31488245932246958255288352768) }, { argument := 8801905412274562289501208576, coefficient := (-8801905412274562289501208576) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk18
