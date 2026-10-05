import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-205971620152416290116556849938432)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6717465279, 3827014977, 1001192971947, 50023895933269, 22965145, 200195947,
    4043809623, 145404483, 25011947867173, 4043809623, 22965145, 180482883,
    172741443, 180482883, 145404483, 172741443, 500596585435, 200195947,
    15208985237, 15271045963507, 98735, 625859635785883, 3255, 7595,
    98735, 98735, 3255, 1218455, 48825, 15271048878067,
    98735, 7595, 48825, 7595, 98735, 98735,
    495775752493, 2117420917811, 79365127855053, 158719167757739, 4245929787989, 188035733,
    16249405055, 87451, 168071524197, 2883, 6727, 87451,
    87451, 2883, 1079203, 43245, 8124708473, 87451,
    6727, 43245, 6727, 87451, 87451, 195908245,
    460812705, 16769125983, 67076519499, 1843235253
  ]
def negativeCoefficients : Array ℕ := #[
    247830725651485859422276681728, 70595965846972445982386552832, 563621536923308581887934464, 28160949885586342329794428928, 211816076215315270373212160, 230810212431432593044406272,
    4662195074892806633237250048, 5364478570142102489772589056, 28160949773602648745366781952, 4662195074892806633237250048, 211816076215315270373212160, 208082597024141523768311808,
    199157324371517894314426368, 208082597024141523768311808, 5364478570142102489772589056, 199157324371517894314426368, 563621648907002166315581440, 230810212431432593044406272,
    547961441968292598346940416, 68774676910807842257184489472, 1865051418744537680697098240, 704655305627884255571441876992, 983763385711404490917150720, 71732746874789910796042240,
    1865051418744537680697098240, 1865051418744537680697098240, 983763385711404490917150720, 23015964211539734235415838720, 1844556348208883420469657600, 68774690036819172206137311232,
    1865051418744537680697098240, 71732746874789910796042240, 1844556348208883420469657600, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240,
    558193873546700513326661632, 9536016056440113236862304256, 357428760234228463275016716288, 357403792385154301770462134272, 9560983905514274741416886272, 216790440210211347950993408,
    18734288524976705039425863680, 1651902685173733374331715584, 193773274558771328498660278272, 871333284487243977669476352, 63534718660528206705065984, 1651902685173733374331715584,
    1651902685173733374331715584, 871333284487243977669476352, 20385568301649478894225457152, 1633749908413582458130268160, 18734302234366316319443255296, 1651902685173733374331715584,
    63534718660528206705065984, 1633749908413582458130268160, 63534718660528206705065984, 1651902685173733374331715584, 1651902685173733374331715584, 225866828590286806051717120,
    17000988070097635729012162560, 618671550696388218398290477056, 618671694276620716116585480192, 17000844489865138010717159424
  ]
def negativeScales : Array ℕ := #[
    32, 31, 39, 45, 24, 27,
    31, 27, 44, 31, 24, 27,
    27, 27, 27, 27, 38, 27,
    33, 43, 16, 49, 11, 12,
    16, 16, 11, 20, 15, 43,
    16, 12, 15, 12, 16, 16,
    38, 40, 46, 47, 41, 27,
    33, 16, 37, 11, 12, 16,
    16, 11, 20, 15, 32, 16,
    12, 15, 12, 16, 16, 27,
    28, 33, 35, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32645269813311099, 31833572402243709, 39864857209861028, 45507682654604108, 24452942556854727, 27576837525972101,
    31913067938236403, 27115496509114077, 44507682648867146, 31913067938236403, 24452942556854727, 27427286777474542,
    27364039005473782, 27427286777474542, 27115496509114077, 27364039005473782, 38864857496504280, 27576837525972101,
    33824204847733657, 43795864114514616, 16591273967534972, 49152832462478720, 11668441828086828, 12890834253091783,
    16591273967534972, 16591273967534972, 11668441828086828, 20216621539732443, 15575332423664331, 43795864389860582,
    16591273967534972, 12890834253091783, 15575332423664331, 12890834253091783, 16591273967534972, 16591273967534972,
    38850896759034085, 40945445236575253, 46173570476146293, 47173469694524293, 41949217663523716, 27486431606764277,
    33919667852285080, 16416187260972460, 37290284357985500, 11493355121495124, 12715747542935743, 16416187260972460,
    16416187260972460, 11493355121495124, 20041534833174352, 15400245717103432, 32919668908021106, 16416187260972460,
    12715747542935743, 15400245717103432, 12715747542935743, 16416187260972460, 16416187260972460, 27545602875288010,
    28779605253186184, 33965088459015265, 35965088793833491, 30779593068990472
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
noncomputable def negativeCeiling : ℝ := 85794883 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 247830725651485859422276681728, coefficient := (-247830725651485859422276681728) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }, { argument := 563621536923308581887934464, coefficient := (-563621536923308581887934464) }, { argument := 28160949885586342329794428928, coefficient := (-28160949885586342329794428928) }, { argument := 211816076215315270373212160, coefficient := (-211816076215315270373212160) }, { argument := 230810212431432593044406272, coefficient := (-230810212431432593044406272) }, { argument := 4662195074892806633237250048, coefficient := (-4662195074892806633237250048) }, { argument := 5364478570142102489772589056, coefficient := (-5364478570142102489772589056) }, { argument := 28160949773602648745366781952, coefficient := (-28160949773602648745366781952) }, { argument := 4662195074892806633237250048, coefficient := (-4662195074892806633237250048) }, { argument := 211816076215315270373212160, coefficient := (-211816076215315270373212160) }, { argument := 208082597024141523768311808, coefficient := (-208082597024141523768311808) }, { argument := 199157324371517894314426368, coefficient := (-199157324371517894314426368) }, { argument := 208082597024141523768311808, coefficient := (-208082597024141523768311808) }, { argument := 5364478570142102489772589056, coefficient := (-5364478570142102489772589056) }, { argument := 199157324371517894314426368, coefficient := (-199157324371517894314426368) }, { argument := 563621648907002166315581440, coefficient := (-563621648907002166315581440) }, { argument := 230810212431432593044406272, coefficient := (-230810212431432593044406272) }, { argument := 547961441968292598346940416, coefficient := (-547961441968292598346940416) }, { argument := 68774676910807842257184489472, coefficient := (-68774676910807842257184489472) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 704655305627884255571441876992, coefficient := (-704655305627884255571441876992) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 23015964211539734235415838720, coefficient := (-23015964211539734235415838720) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 68774690036819172206137311232, coefficient := (-68774690036819172206137311232) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 558193873546700513326661632, coefficient := (-558193873546700513326661632) }, { argument := 9536016056440113236862304256, coefficient := (-9536016056440113236862304256) }, { argument := 357428760234228463275016716288, coefficient := (-357428760234228463275016716288) }, { argument := 357403792385154301770462134272, coefficient := (-357403792385154301770462134272) }, { argument := 9560983905514274741416886272, coefficient := (-9560983905514274741416886272) }, { argument := 216790440210211347950993408, coefficient := (-216790440210211347950993408) }, { argument := 18734288524976705039425863680, coefficient := (-18734288524976705039425863680) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 193773274558771328498660278272, coefficient := (-193773274558771328498660278272) }, { argument := 871333284487243977669476352, coefficient := (-871333284487243977669476352) }, { argument := 63534718660528206705065984, coefficient := (-63534718660528206705065984) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 871333284487243977669476352, coefficient := (-871333284487243977669476352) }, { argument := 20385568301649478894225457152, coefficient := (-20385568301649478894225457152) }, { argument := 1633749908413582458130268160, coefficient := (-1633749908413582458130268160) }, { argument := 18734302234366316319443255296, coefficient := (-18734302234366316319443255296) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 63534718660528206705065984, coefficient := (-63534718660528206705065984) }, { argument := 1633749908413582458130268160, coefficient := (-1633749908413582458130268160) }, { argument := 63534718660528206705065984, coefficient := (-63534718660528206705065984) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 225866828590286806051717120, coefficient := (-225866828590286806051717120) }, { argument := 17000988070097635729012162560, coefficient := (-17000988070097635729012162560) }, { argument := 618671550696388218398290477056, coefficient := (-618671550696388218398290477056) }, { argument := 618671694276620716116585480192, coefficient := (-618671694276620716116585480192) }, { argument := 17000844489865138010717159424, coefficient := (-17000844489865138010717159424) }] }

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

end TermShard10


end Parent3

namespace Parent3

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 28996942351412533340443004077342720
def positiveArguments : Array ℕ := #[
    1873, 3, 3, 3, 3, 3,
    1085, 12985, 19425, 5635, 1085, 22505,
    11305, 1085, 12985, 1085, 45, 35,
    5, 47, 555, 39, 35, 555,
    5, 39, 39, 39, 39, 39,
    45, 47, 625, 2625, 11375, 375,
    375, 875, 11375, 11375, 375, 140375,
    5625, 2625, 11375, 875, 5625, 875
  ]
def positiveCoefficients : Array ℕ := #[
    296788696778434208625415637958656, 475368975085586025561263702016, 475368975085586025561263702016, 475368975085586025561263702016, 475368975085586025561263702016, 475368975085586025561263702016,
    83947808914039849891596861440, 2009331426265082858695641006080, 1502936578944906989994718003200, 1743948030343279462264141250560, 83947808914039849891596861440, 1741240036507342692912799416320,
    1749364018015153000966824919040, 83947808914039849891596861440, 2009331426265082858695641006080, 83947808914039849891596861440, 445658414142736898963684720640, 346623210999906476971754782720,
    396140812571321687967719751680, 465465454771302983362070708224, 5496453774427088420552111554560, 12359593352225236664592856252416, 346623210999906476971754782720, 5496453774427088420552111554560,
    396140812571321687967719751680, 386237292257038645768526757888, 386237292257038645768526757888, 386237292257038645768526757888, 12359593352225236664592856252416, 386237292257038645768526757888,
    445658414142736898963684720640, 465465454771302983362070708224, 12089258196146291747061760000, 203099537695257701350637568000, 440048998339725019593048064000, 14507109835375550096474112000,
    232113757366008801543585792000, 16924961474604808445886464000, 440048998339725019593048064000, 440048998339725019593048064000, 232113757366008801543585792000, 5430494781708914252780142592000,
    435213295061266502894223360000, 203099537695257701350637568000, 440048998339725019593048064000, 16924961474604808445886464000, 435213295061266502894223360000, 16924961474604808445886464000
  ]
def positiveScales : Array ℕ := #[
    10, 1, 1, 1, 1, 1,
    10, 13, 14, 12, 10, 14,
    13, 10, 13, 10, 5, 5,
    2, 5, 9, 5, 5, 9,
    2, 5, 5, 5, 5, 5,
    5, 5, 9, 11, 13, 8,
    8, 9, 13, 13, 8, 17,
    12, 11, 13, 9, 12, 9
  ]
def negativeArguments : Array ℕ := #[
    3963918015, 6966438209, 3963918015, 79469439, 2893243521, 23145953193,
    635750487, 3827014977, 6717465279, 3827014977, 12582915, 12582909,
    3, 3, 35, 1
  ]
def negativeCoefficients : Array ℕ := #[
    73121381151871779528234762240, 257016205493469065491920191488, 73121381151871779528234762240, 732976201457136357932531712, 26685461387402653324403539968, 26685467180833213973809594368,
    732970408026575708526477312, 70595965846972445982386552832, 247830725651485859422276681728, 70595965846972445982386552832, 118842272105595403608187207680, 118842215437197609172444643328,
    475368975085586025561263702016, 1901475900342344102245054808064, 11091942751997007263096153047040, 40564819207303340847894502572032
  ]
def negativeScales : Array ℕ := #[
    31, 32, 31, 26, 31, 34,
    29, 31, 32, 31, 23, 23,
    1, 1, 5, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10871135184083522, 1584962500720924, 1584962500720924, 1584962500720924, 1584962500720924, 1584962500720924,
    10083479327331841, 13664558393563860, 14245626978182434, 12460199895059578, 10083479327331841, 14457957944272909,
    13464673371638885, 10083479327331841, 13664558393563860, 10083479327331841, 5491853096329661, 5129283016944966,
    2321928094887362, 5554588851677541, 9116343961237468, 5285402218862248, 5129283016944966, 9116343961237468,
    2321928094887362, 5285402218862248, 5285402218862248, 5285402218862248, 5285402218862248, 5285402218862248,
    5491853096329661, 5554588851677541, 9287712379549449, 11358101707440846, 13473578924860776, 8550746785383158,
    8550746785383158, 9773139206696762, 13473578924860776, 13473578924860776, 8550746785383158, 17098926497062688,
    12457637380991757, 11358101707440846, 13473578924860776, 9773139206696762, 12457637380991757, 9773139206696762
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31884279981104318, 32697774079501420, 31884279981104318, 26243896824233853, 31430040612356893, 34430040925566866,
    29243885421153433, 31833572402243709, 32645269813311099, 31833572402243709, 23584962844690126, 23584962156759523,
    1584962500724866, 1584962500724866, 5129283016944967, 0
  ]

abbrev PositiveTerm := Fin 48
abbrev NegativeTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 2837428977 / 62500000000
noncomputable def negativeCeiling : ℝ := 1128074089 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 257016205493469065491920191488, coefficient := (-257016205493469065491920191488) }, { argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 732976201457136357932531712, coefficient := (-732976201457136357932531712) }, { argument := 26685461387402653324403539968, coefficient := (-26685461387402653324403539968) }, { argument := 26685467180833213973809594368, coefficient := (-26685467180833213973809594368) }, { argument := 732970408026575708526477312, coefficient := (-732970408026575708526477312) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }, { argument := 247830725651485859422276681728, coefficient := (-247830725651485859422276681728) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }, { argument := 118842272105595403608187207680, coefficient := (-118842272105595403608187207680) }, { argument := 118842215437197609172444643328, coefficient := (-118842215437197609172444643328) }, { argument := 296788696778434208625415637958656, coefficient := 296788696778434208625415637958656 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 83947808914039849891596861440, coefficient := 83947808914039849891596861440 }, { argument := 2009331426265082858695641006080, coefficient := 2009331426265082858695641006080 }, { argument := 1502936578944906989994718003200, coefficient := 1502936578944906989994718003200 }, { argument := 1743948030343279462264141250560, coefficient := 1743948030343279462264141250560 }, { argument := 83947808914039849891596861440, coefficient := 83947808914039849891596861440 }, { argument := 1741240036507342692912799416320, coefficient := 1741240036507342692912799416320 }, { argument := 1749364018015153000966824919040, coefficient := 1749364018015153000966824919040 }, { argument := 83947808914039849891596861440, coefficient := 83947808914039849891596861440 }, { argument := 2009331426265082858695641006080, coefficient := 2009331426265082858695641006080 }, { argument := 83947808914039849891596861440, coefficient := 83947808914039849891596861440 }, { argument := 11091942751997007263096153047040, coefficient := (-11091942751997007263096153047040) }, { argument := 445658414142736898963684720640, coefficient := 445658414142736898963684720640 }, { argument := 346623210999906476971754782720, coefficient := 346623210999906476971754782720 }, { argument := 396140812571321687967719751680, coefficient := 396140812571321687967719751680 }, { argument := 465465454771302983362070708224, coefficient := 465465454771302983362070708224 }, { argument := 5496453774427088420552111554560, coefficient := 5496453774427088420552111554560 }, { argument := 12359593352225236664592856252416, coefficient := 12359593352225236664592856252416 }, { argument := 346623210999906476971754782720, coefficient := 346623210999906476971754782720 }, { argument := 5496453774427088420552111554560, coefficient := 5496453774427088420552111554560 }, { argument := 396140812571321687967719751680, coefficient := 396140812571321687967719751680 }, { argument := 386237292257038645768526757888, coefficient := 386237292257038645768526757888 }, { argument := 386237292257038645768526757888, coefficient := 386237292257038645768526757888 }, { argument := 386237292257038645768526757888, coefficient := 386237292257038645768526757888 }, { argument := 12359593352225236664592856252416, coefficient := 12359593352225236664592856252416 }, { argument := 386237292257038645768526757888, coefficient := 386237292257038645768526757888 }, { argument := 445658414142736898963684720640, coefficient := 445658414142736898963684720640 }, { argument := 465465454771302983362070708224, coefficient := 465465454771302983362070708224 }, { argument := 40564819207303340847894502572032, coefficient := (-40564819207303340847894502572032) }, { argument := 12089258196146291747061760000, coefficient := 12089258196146291747061760000 }, { argument := 203099537695257701350637568000, coefficient := 203099537695257701350637568000 }, { argument := 440048998339725019593048064000, coefficient := 440048998339725019593048064000 }, { argument := 14507109835375550096474112000, coefficient := 14507109835375550096474112000 }, { argument := 232113757366008801543585792000, coefficient := 232113757366008801543585792000 }, { argument := 16924961474604808445886464000, coefficient := 16924961474604808445886464000 }, { argument := 440048998339725019593048064000, coefficient := 440048998339725019593048064000 }, { argument := 440048998339725019593048064000, coefficient := 440048998339725019593048064000 }, { argument := 232113757366008801543585792000, coefficient := 232113757366008801543585792000 }, { argument := 5430494781708914252780142592000, coefficient := 5430494781708914252780142592000 }, { argument := 435213295061266502894223360000, coefficient := 435213295061266502894223360000 }, { argument := 203099537695257701350637568000, coefficient := 203099537695257701350637568000 }, { argument := 440048998339725019593048064000, coefficient := 440048998339725019593048064000 }, { argument := 16924961474604808445886464000, coefficient := 16924961474604808445886464000 }, { argument := 435213295061266502894223360000, coefficient := 435213295061266502894223360000 }, { argument := 16924961474604808445886464000, coefficient := 16924961474604808445886464000 }] }

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

end TermShard11


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
