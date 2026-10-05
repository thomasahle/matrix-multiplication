import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1116333247146060901952876070305792)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    39985570625, 3836343875, 51949625, 74925777, 2715334959, 21722687655,
    599398233, 12556305405, 21281242115, 12556305405, 124876295, 4525558265,
    36204479425, 998997055, 5381273745, 9120532335, 5381273745, 175,
    175, 69760925, 5151661775, 53694909125, 5151661775, 69760925,
    1923094943, 69693597281, 557548983145, 15384554647, 12556305405, 21281242115,
    12556305405, 2172847533, 78744713811, 629957941995, 17382548757, 141706875285,
    240174018155, 141706875285, 5649, 5649, 5381273745, 9120532335,
    5381273745, 3773, 3773, 17100029828409, 35417085, 295190187533739,
    876384465, 27881535, 295190310319245, 14317545, 14317545, 484535865,
    26374425, 876384465, 484535865, 17099841646167, 27881535, 26374425,
    35417085, 14912111526893, 7024395, 2292171
  ]
def negativeCoefficients : Array ℕ := #[
    184400896990153370469662720000, 17692013410217046717759488000, 119787679637522945671168000, 44228372250970669668812980224, 1602850850018227786084471799808, 1602851439059659547777874001920,
    44227783209538907975410778112, 57905738079342740339026821120, 196284813433027187064092753920, 57905738079342740339026821120, 2303561054738055711917342720, 83481815105116030525232906240,
    83481845784357268113430937600, 2303530375496818123719311360, 49633489782293777433451560960, 168244125799737588912079503360, 49633489782293777433451560960, 1692496147460480844588646400,
    1692496147460480844588646400, 160857741227530812758425600, 23757846579434319878134169600, 247624061672491668916404224000, 23757846579434319878134169600, 160857741227530812758425600,
    70949680485932115927054155776, 2571239905237573740177173512192, 2571240850158203857893672878080, 70948735565301998210554789888, 57905738079342740339026821120, 196284813433027187064092753920,
    57905738079342740339026821120, 40081962352442169387361763328, 1452583582829018931139052568576, 1452584116647816465173698314240, 40081428533644635352716017664, 653507615466868069540445552640,
    2215214323029878254009046794240, 653507615466868069540445552640, 54633775640024321663321505792, 54633775640024321663321505792, 49633489782293777433451560960, 168244125799737588912079503360,
    49633489782293777433451560960, 36490216939247967009331216384, 36490216939247967009331216384, 4813230497702946190921826304, 163332475707954363723939840, 166177302322546724254481645568,
    4041609984007466489594511360, 128580885131793860803952640, 166177371444641607766706749440, 132056044189409911095951360, 132056044189409911095951360, 2234527274047120337755176960,
    121630567016561760219955200, 4041609984007466489594511360, 2234527274047120337755176960, 4813177529110761881890455552, 128580885131793860803952640, 121630567016561760219955200,
    163332475707954363723939840, 67158179915822592941178748928, 518308867350580023294689280, 21141545905089448318599168
  ]
def negativeScales : Array ℕ := #[
    35, 31, 25, 26, 31, 34,
    29, 33, 34, 33, 26, 32,
    35, 29, 32, 33, 32, 7,
    7, 26, 32, 35, 32, 26,
    30, 36, 39, 33, 33, 34,
    33, 31, 36, 39, 34, 37,
    37, 37, 12, 12, 32, 33,
    32, 11, 11, 43, 25, 48,
    29, 24, 48, 23, 23, 28,
    24, 29, 28, 43, 24, 24,
    25, 43, 22, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35218760425288713, 31837084899082653, 25630609999252044, 26158958804154716, 31338483031345890, 34338483561530589,
    29158939589954233, 33547692973774089, 34308863307459596, 33547692973774089, 26895924402380042, 32075448625512095,
    35075449155696795, 29895905188178154, 32325300552436402, 33086470886123148, 32325300552436402, 7451211111832378,
    7451211111832378, 26055915833971809, 32262390732464439, 35644066260039690, 32262390732464439, 26055915833971809,
    30840782845579620, 36020307071319634, 39020307601504334, 33840763631378599, 33547692973774089, 34308863307459596,
    33547692973774089, 31016939799282288, 36196464026473461, 39196464556658161, 34016920585081805, 37044118799892348,
    37805289134298409, 37044118799892348, 12463779785335462, 12463779785335462, 32325300552436402, 33086470886123148,
    32325300552436402, 11881496387932734, 11881496387932734, 43959064087350077, 25077942140301808, 48068638093751943,
    29706988670182637, 24732806654406840, 48068638693846428, 23771280802423319, 23771280802423319, 28852028217752524,
    24652636305591918, 29706988670182637, 28852028217752524, 43959048210703139, 24732806654406840, 24652636305591918,
    25077942140301808, 43761549788809611, 22743942543169723, 21128283245028767
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
noncomputable def negativeCeiling : ℝ := 3812704161 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 184400896990153370469662720000, coefficient := (-184400896990153370469662720000) }, { argument := 17692013410217046717759488000, coefficient := (-17692013410217046717759488000) }, { argument := 119787679637522945671168000, coefficient := (-119787679637522945671168000) }, { argument := 44228372250970669668812980224, coefficient := (-44228372250970669668812980224) }, { argument := 1602850850018227786084471799808, coefficient := (-1602850850018227786084471799808) }, { argument := 1602851439059659547777874001920, coefficient := (-1602851439059659547777874001920) }, { argument := 44227783209538907975410778112, coefficient := (-44227783209538907975410778112) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 196284813433027187064092753920, coefficient := (-196284813433027187064092753920) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 2303561054738055711917342720, coefficient := (-2303561054738055711917342720) }, { argument := 83481815105116030525232906240, coefficient := (-83481815105116030525232906240) }, { argument := 83481845784357268113430937600, coefficient := (-83481845784357268113430937600) }, { argument := 2303530375496818123719311360, coefficient := (-2303530375496818123719311360) }, { argument := 49633489782293777433451560960, coefficient := (-49633489782293777433451560960) }, { argument := 168244125799737588912079503360, coefficient := (-168244125799737588912079503360) }, { argument := 49633489782293777433451560960, coefficient := (-49633489782293777433451560960) }, { argument := 1692496147460480844588646400, coefficient := (-1692496147460480844588646400) }, { argument := 1692496147460480844588646400, coefficient := (-1692496147460480844588646400) }, { argument := 160857741227530812758425600, coefficient := (-160857741227530812758425600) }, { argument := 23757846579434319878134169600, coefficient := (-23757846579434319878134169600) }, { argument := 247624061672491668916404224000, coefficient := (-247624061672491668916404224000) }, { argument := 23757846579434319878134169600, coefficient := (-23757846579434319878134169600) }, { argument := 160857741227530812758425600, coefficient := (-160857741227530812758425600) }, { argument := 70949680485932115927054155776, coefficient := (-70949680485932115927054155776) }, { argument := 2571239905237573740177173512192, coefficient := (-2571239905237573740177173512192) }, { argument := 2571240850158203857893672878080, coefficient := (-2571240850158203857893672878080) }, { argument := 70948735565301998210554789888, coefficient := (-70948735565301998210554789888) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 196284813433027187064092753920, coefficient := (-196284813433027187064092753920) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 40081962352442169387361763328, coefficient := (-40081962352442169387361763328) }, { argument := 1452583582829018931139052568576, coefficient := (-1452583582829018931139052568576) }, { argument := 1452584116647816465173698314240, coefficient := (-1452584116647816465173698314240) }, { argument := 40081428533644635352716017664, coefficient := (-40081428533644635352716017664) }, { argument := 653507615466868069540445552640, coefficient := (-653507615466868069540445552640) }, { argument := 2215214323029878254009046794240, coefficient := (-2215214323029878254009046794240) }, { argument := 653507615466868069540445552640, coefficient := (-653507615466868069540445552640) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 54633775640024321663321505792, coefficient := (-54633775640024321663321505792) }, { argument := 49633489782293777433451560960, coefficient := (-49633489782293777433451560960) }, { argument := 168244125799737588912079503360, coefficient := (-168244125799737588912079503360) }, { argument := 49633489782293777433451560960, coefficient := (-49633489782293777433451560960) }, { argument := 36490216939247967009331216384, coefficient := (-36490216939247967009331216384) }, { argument := 36490216939247967009331216384, coefficient := (-36490216939247967009331216384) }, { argument := 4813230497702946190921826304, coefficient := (-4813230497702946190921826304) }, { argument := 163332475707954363723939840, coefficient := (-163332475707954363723939840) }, { argument := 166177302322546724254481645568, coefficient := (-166177302322546724254481645568) }, { argument := 4041609984007466489594511360, coefficient := (-4041609984007466489594511360) }, { argument := 128580885131793860803952640, coefficient := (-128580885131793860803952640) }, { argument := 166177371444641607766706749440, coefficient := (-166177371444641607766706749440) }, { argument := 132056044189409911095951360, coefficient := (-132056044189409911095951360) }, { argument := 132056044189409911095951360, coefficient := (-132056044189409911095951360) }, { argument := 2234527274047120337755176960, coefficient := (-2234527274047120337755176960) }, { argument := 121630567016561760219955200, coefficient := (-121630567016561760219955200) }, { argument := 4041609984007466489594511360, coefficient := (-4041609984007466489594511360) }, { argument := 2234527274047120337755176960, coefficient := (-2234527274047120337755176960) }, { argument := 4813177529110761881890455552, coefficient := (-4813177529110761881890455552) }, { argument := 128580885131793860803952640, coefficient := (-128580885131793860803952640) }, { argument := 121630567016561760219955200, coefficient := (-121630567016561760219955200) }, { argument := 163332475707954363723939840, coefficient := (-163332475707954363723939840) }, { argument := 67158179915822592941178748928, coefficient := (-67158179915822592941178748928) }, { argument := 518308867350580023294689280, coefficient := (-518308867350580023294689280) }, { argument := 21141545905089448318599168, coefficient := (-21141545905089448318599168) }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 113161079575183432267907136030244864
def positiveArguments : Array ℕ := #[
    9939, 67110761, 67106967, 878836097, 285, 93,
    11961922769, 939, 3515344171, 1881, 843, 285,
    93, 498706789, 30785, 8299880209, 761765, 24235,
    33199535315, 12445, 12445, 421165, 22925, 761765,
    421165, 997403679, 24235, 22925, 30785, 75196503,
    8995635, 271269, 1156243795, 278361, 8865, 271269,
    154251, 278361, 4345623, 5319, 2302883705, 271269,
    8865, 5319, 8865
  ]
def positiveCoefficients : Array ℕ := #[
    787448707229273251342233322389504, 633843216772550708182292365312, 633807383455678693314410840064, 16600744513635105437517294338048, 176406455598166689173125201920, 7195526478346272847851159552,
    56488583155000857540662053044224, 145303212111121509766284705792, 16600743488881578654804282966016, 145535325868487518567828291584, 130447931639696946467495215104, 176406455598166689173125201920,
    7195526478346272847851159552, 9420304900612577080366203928576, 595468501709381746293274050560, 313560608886517646688056049139712, 14734678031659807892320802570240, 468773075813768608784066805760,
    313560745636806257627242147348480, 481442618403329922534987530240, 481442618403329922534987530240, 8146515885087924741842025840640, 443433990634645981282225356800, 14734678031659807892320802570240,
    8146515885087924741842025840640, 9420211407200949227130263175168, 468773075813768608784066805760, 443433990634645981282225356800, 595468501709381746293274050560, 710210890792413449841253810176,
    43500221661316178864031966167040, 10494211141153306930987829035008, 349453244386176068619996737044480, 10768569602359929334412347441152, 342948076508278004280648007680, 10494211141153306930987829035008,
    5967296531244037274483275333632, 10768569602359929334412347441152, 168113147104357877698373653364736, 6584603068958937682188441747456, 43500243289754670407007044894720, 10494211141153306930987829035008,
    342948076508278004280648007680, 6584603068958937682188441747456, 342948076508278004280648007680
  ]
def positiveScales : Array ℕ := #[
    13, 26, 25, 29, 8, 6,
    33, 9, 31, 10, 9, 8,
    6, 28, 14, 32, 19, 14,
    34, 13, 13, 18, 14, 19,
    18, 29, 14, 14, 14, 26,
    23, 18, 30, 18, 13, 18,
    17, 18, 22, 12, 31, 18,
    13, 12, 13
  ]
def negativeArguments : Array ℕ := #[
    405509722231567, 23143533, 119296886918537, 46361007, 20777421, 7024395,
    2292171, 18299376400771, 18293929510525, 11121299073, 18849100159, 11121299073,
    3507, 3507, 21, 21, 1, 571,
    8781
  ]
def negativeCoefficients : Array ℕ := #[
    228281679242149809859176955904, 426922830212451440240099328, 67158176934097929000183660544, 427604815564228519218118656, 383275767698718385646862336, 518308867350580023294689280,
    21141545905089448318599168, 5150816546226545241962315776, 5149283382921406892631654400, 51287939441703570014566612992, 173852263326395508542482153472, 51287939441703570014566612992,
    33917622795108036125556473856, 33917622795108036125556473856, 1624796301562061610805100544, 1624796301562061610805100544, 1267650600228229401496703205376, 90478561591289873531827191283712,
    695702495037755148408909427900416
  ]
def negativeScales : Array ℕ := #[
    48, 24, 46, 25, 24, 22,
    21, 44, 44, 33, 34, 33,
    11, 11, 4, 4, 0, 9,
    13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13278884988802170, 26000040780809702, 25999959216578875, 29711018886812152, 8154818109052103, 6539158811107971,
    33477730257000277, 9874981347482478, 31711018797755491, 10877284133344468, 9719388820935039, 8154818109052103,
    6539158811107971, 28893616601704744, 14909939947780247, 32950443367733794, 19538986477897971, 14564804462053633,
    34950443996922897, 13603278609868012, 13603278609868012, 18684026023749686, 14484634113369768, 19538986477897971,
    18684026023749686, 29893602283362452, 14564804462053633, 14484634113369768, 14909939947780247, 26164162235398132,
    23100793693937801, 18049364663591340, 30106798477390995, 18086597569790315, 13113904915786050, 18049364663591340,
    17234920316747416, 18086597569790315, 22051131589765528, 12376939321619844, 31100794411249852, 18049364663591340,
    13113904915786050, 12376939321619844, 13113904915786050
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    48526729832378291, 24464105781574588, 46761549724756066, 25466408567444016, 24308513254862818, 22743942543169723,
    21128283245028767, 44056859719266657, 44056430230790090, 33372606267214760, 34133776600901504, 33372606267214760,
    11776021715645854, 11776021715645854, 4392317422778766, 4392317422778766, 0, 9157346935362843,
    13100169531129907
  ]

abbrev PositiveTerm := Fin 45
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 32518911231 / 50000000000
noncomputable def negativeCeiling : ℝ := 119976403233 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 228281679242149809859176955904, coefficient := (-228281679242149809859176955904) }, { argument := 426922830212451440240099328, coefficient := (-426922830212451440240099328) }, { argument := 67158176934097929000183660544, coefficient := (-67158176934097929000183660544) }, { argument := 427604815564228519218118656, coefficient := (-427604815564228519218118656) }, { argument := 383275767698718385646862336, coefficient := (-383275767698718385646862336) }, { argument := 518308867350580023294689280, coefficient := (-518308867350580023294689280) }, { argument := 21141545905089448318599168, coefficient := (-21141545905089448318599168) }, { argument := 5150816546226545241962315776, coefficient := (-5150816546226545241962315776) }, { argument := 5149283382921406892631654400, coefficient := (-5149283382921406892631654400) }, { argument := 51287939441703570014566612992, coefficient := (-51287939441703570014566612992) }, { argument := 173852263326395508542482153472, coefficient := (-173852263326395508542482153472) }, { argument := 51287939441703570014566612992, coefficient := (-51287939441703570014566612992) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 33917622795108036125556473856, coefficient := (-33917622795108036125556473856) }, { argument := 1624796301562061610805100544, coefficient := (-1624796301562061610805100544) }, { argument := 1624796301562061610805100544, coefficient := (-1624796301562061610805100544) }, { argument := 787448707229273251342233322389504, coefficient := 787448707229273251342233322389504 }, { argument := 633843216772550708182292365312, coefficient := 633843216772550708182292365312 }, { argument := 633807383455678693314410840064, coefficient := 633807383455678693314410840064 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 16600744513635105437517294338048, coefficient := 16600744513635105437517294338048 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 56488583155000857540662053044224, coefficient := 56488583155000857540662053044224 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 16600743488881578654804282966016, coefficient := 16600743488881578654804282966016 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 90478561591289873531827191283712, coefficient := (-90478561591289873531827191283712) }, { argument := 9420304900612577080366203928576, coefficient := 9420304900612577080366203928576 }, { argument := 595468501709381746293274050560, coefficient := 595468501709381746293274050560 }, { argument := 313560608886517646688056049139712, coefficient := 313560608886517646688056049139712 }, { argument := 14734678031659807892320802570240, coefficient := 14734678031659807892320802570240 }, { argument := 468773075813768608784066805760, coefficient := 468773075813768608784066805760 }, { argument := 313560745636806257627242147348480, coefficient := 313560745636806257627242147348480 }, { argument := 481442618403329922534987530240, coefficient := 481442618403329922534987530240 }, { argument := 481442618403329922534987530240, coefficient := 481442618403329922534987530240 }, { argument := 8146515885087924741842025840640, coefficient := 8146515885087924741842025840640 }, { argument := 443433990634645981282225356800, coefficient := 443433990634645981282225356800 }, { argument := 14734678031659807892320802570240, coefficient := 14734678031659807892320802570240 }, { argument := 8146515885087924741842025840640, coefficient := 8146515885087924741842025840640 }, { argument := 9420211407200949227130263175168, coefficient := 9420211407200949227130263175168 }, { argument := 468773075813768608784066805760, coefficient := 468773075813768608784066805760 }, { argument := 443433990634645981282225356800, coefficient := 443433990634645981282225356800 }, { argument := 595468501709381746293274050560, coefficient := 595468501709381746293274050560 }, { argument := 695702495037755148408909427900416, coefficient := (-695702495037755148408909427900416) }, { argument := 710210890792413449841253810176, coefficient := 710210890792413449841253810176 }, { argument := 43500221661316178864031966167040, coefficient := 43500221661316178864031966167040 }, { argument := 10494211141153306930987829035008, coefficient := 10494211141153306930987829035008 }, { argument := 349453244386176068619996737044480, coefficient := 349453244386176068619996737044480 }, { argument := 10768569602359929334412347441152, coefficient := 10768569602359929334412347441152 }, { argument := 342948076508278004280648007680, coefficient := 342948076508278004280648007680 }, { argument := 10494211141153306930987829035008, coefficient := 10494211141153306930987829035008 }, { argument := 5967296531244037274483275333632, coefficient := 5967296531244037274483275333632 }, { argument := 10768569602359929334412347441152, coefficient := 10768569602359929334412347441152 }, { argument := 168113147104357877698373653364736, coefficient := 168113147104357877698373653364736 }, { argument := 6584603068958937682188441747456, coefficient := 6584603068958937682188441747456 }, { argument := 43500243289754670407007044894720, coefficient := 43500243289754670407007044894720 }, { argument := 10494211141153306930987829035008, coefficient := 10494211141153306930987829035008 }, { argument := 342948076508278004280648007680, coefficient := 342948076508278004280648007680 }, { argument := 6584603068958937682188441747456, coefficient := 6584603068958937682188441747456 }, { argument := 342948076508278004280648007680, coefficient := 342948076508278004280648007680 }] }

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

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
