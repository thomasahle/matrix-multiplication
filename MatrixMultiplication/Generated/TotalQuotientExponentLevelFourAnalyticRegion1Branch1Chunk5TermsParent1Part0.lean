import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-324933446027183855280699796881408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15020735, 126751709, 505909565, 251674633, 505909565, 72346369603,
    3834079, 2714164166677, 25570803, 1257887, 12774329, 25773821,
    9077813301, 3834079, 1257887, 53840245, 19952803319, 79639441655,
    39619320603, 79639441655, 3059384428079, 1405520541, 112849290184841, 9284146137,
    458839773, 4634939691, 9426279159, 383837225513, 1405520541, 458839773,
    7161, 173481, 131439, 73227, 7161, 73227,
    146223, 7161, 173481, 7161, 1108566017301, 118914411543275,
    43990225, 3566775, 764478775, 1382719775, 118914421168875, 764478775,
    22589575, 22589575, 43990225, 43990225, 1382719775, 43990225,
    1108556391701, 3566775, 3756275, 4988201859, 19909864515, 9904832183,
    19909864515, 62916206795009, 14417513045, 2322067209059783
  ]
def negativeCoefficients : Array ℕ := #[
    70933415512066980298945986560, 4676312673656615273903423488, 4666192134998363597197803520, 4642577544795776351551356928, 4666192134998363597197803520, 40727385398209872329179136,
    282905096285536975801286656, 1527938591208611249572020224, 235849029350122211795533824, 11601959781323143376797696, 235644777776366062785265664, 237721539894300394670522368,
    40882836599722532243767296, 282905096285536975801286656, 11601959781323143376797696, 254253368417490001368469995520, 184032128189327761062863306752, 183636049797863606917330370560,
    182711866884447247244420186112, 183636049797863606917330370560, 6889121285139841209799278592, 51854555420337585728375488512, 254114010612737449635314925568, 42815566933039544223922126848,
    2116024965842496482854305792, 42749773138477715195405795328, 43471039803353776554283892736, 6914596743165087361418657792, 51854555420337585728375488512, 2116024965842496482854305792,
    135267465535318117501108224, 3276963439258835685268783104, 2482812512567613188971954176, 2766437843528764080506535936, 135267465535318117501108224, 2766437843528764080506535936,
    2762074376898592528329080832, 135267465535318117501108224, 3276963439258835685268783104, 135267465535318117501108224, 312033593902023651367059456, 33471431219704693636097638400,
    101434552789987470029619200, 131590771187010771930316800, 1762768039025998465649868800, 3188334726885281828228300800, 33471433929070229462188032000, 1762768039025998465649868800,
    104176027189716861111500800, 104176027189716861111500800, 101434552789987470029619200, 101434552789987470029619200, 3188334726885281828228300800, 101434552789987470029619200,
    312030884536487825276665856, 131590771187010771930316800, 70954028641764706300303769600, 184032166161950436793975308288, 183636087625218173067979653120, 182711904372842891040656457728,
    183636087625218173067979653120, 70837351369391900203591663616, 531912346640967803929561661440, 2614415254362721588047188590592
  ]
def negativeScales : Array ℕ := #[
    23, 26, 28, 27, 28, 36,
    21, 41, 24, 20, 23, 24,
    33, 21, 20, 25, 34, 36,
    35, 36, 41, 30, 46, 33,
    28, 32, 33, 38, 30, 28,
    12, 17, 17, 16, 12, 16,
    17, 12, 17, 12, 40, 46,
    25, 21, 29, 30, 46, 29,
    24, 24, 25, 25, 30, 25,
    40, 21, 21, 32, 34, 33,
    34, 45, 33, 51
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23840452074704782, 26917429964342335, 28914304280506939, 27906984574548615, 28914304280506939, 36074201571889664,
    21870448635463357, 41303645123696905, 24607994130466023, 20262570895466728, 23606744176610483, 24619403098551404,
    33079697671355347, 21870448635463357, 20262570895466728, 25682181639204881, 34215872404609294, 36212764055361644,
    35205485089800503, 36212764055361644, 41476378539312703, 30388457392145851, 46681390672563893, 33112122085572781,
    28773415211467357, 32109903420871311, 33134041261346452, 38481703678323837, 30388457392145851, 28773415211467357,
    12805945352531863, 17404418138930338, 17004033883722640, 16160088071555465, 12805945352531863, 16160088071555465,
    17157810730844399, 12805945352531863, 17404418138930338, 12805945352531863, 40011831826757727, 46756916898285084,
    25390679644535597, 21766188779946842, 29509901206234966, 30364861660379862, 46756917015064915, 29509901206234966,
    24429153792350249, 24429153792350249, 25390679644535597, 25390679644535597, 30364861660379862, 25390679644535597,
    40011819299884760, 21766188779946842, 21840871258533351, 32215872702290516, 34212764352543658, 33205485385809284,
    34212764352543658, 45838496928516343, 33747103276834200, 51044331152953200
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
noncomputable def negativeCeiling : ℝ := 2880746251 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70933415512066980298945986560, coefficient := (-70933415512066980298945986560) }, { argument := 4676312673656615273903423488, coefficient := (-4676312673656615273903423488) }, { argument := 4666192134998363597197803520, coefficient := (-4666192134998363597197803520) }, { argument := 4642577544795776351551356928, coefficient := (-4642577544795776351551356928) }, { argument := 4666192134998363597197803520, coefficient := (-4666192134998363597197803520) }, { argument := 40727385398209872329179136, coefficient := (-40727385398209872329179136) }, { argument := 282905096285536975801286656, coefficient := (-282905096285536975801286656) }, { argument := 1527938591208611249572020224, coefficient := (-1527938591208611249572020224) }, { argument := 235849029350122211795533824, coefficient := (-235849029350122211795533824) }, { argument := 11601959781323143376797696, coefficient := (-11601959781323143376797696) }, { argument := 235644777776366062785265664, coefficient := (-235644777776366062785265664) }, { argument := 237721539894300394670522368, coefficient := (-237721539894300394670522368) }, { argument := 40882836599722532243767296, coefficient := (-40882836599722532243767296) }, { argument := 282905096285536975801286656, coefficient := (-282905096285536975801286656) }, { argument := 11601959781323143376797696, coefficient := (-11601959781323143376797696) }, { argument := 254253368417490001368469995520, coefficient := (-254253368417490001368469995520) }, { argument := 184032128189327761062863306752, coefficient := (-184032128189327761062863306752) }, { argument := 183636049797863606917330370560, coefficient := (-183636049797863606917330370560) }, { argument := 182711866884447247244420186112, coefficient := (-182711866884447247244420186112) }, { argument := 183636049797863606917330370560, coefficient := (-183636049797863606917330370560) }, { argument := 6889121285139841209799278592, coefficient := (-6889121285139841209799278592) }, { argument := 51854555420337585728375488512, coefficient := (-51854555420337585728375488512) }, { argument := 254114010612737449635314925568, coefficient := (-254114010612737449635314925568) }, { argument := 42815566933039544223922126848, coefficient := (-42815566933039544223922126848) }, { argument := 2116024965842496482854305792, coefficient := (-2116024965842496482854305792) }, { argument := 42749773138477715195405795328, coefficient := (-42749773138477715195405795328) }, { argument := 43471039803353776554283892736, coefficient := (-43471039803353776554283892736) }, { argument := 6914596743165087361418657792, coefficient := (-6914596743165087361418657792) }, { argument := 51854555420337585728375488512, coefficient := (-51854555420337585728375488512) }, { argument := 2116024965842496482854305792, coefficient := (-2116024965842496482854305792) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 3276963439258835685268783104, coefficient := (-3276963439258835685268783104) }, { argument := 2482812512567613188971954176, coefficient := (-2482812512567613188971954176) }, { argument := 2766437843528764080506535936, coefficient := (-2766437843528764080506535936) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 2766437843528764080506535936, coefficient := (-2766437843528764080506535936) }, { argument := 2762074376898592528329080832, coefficient := (-2762074376898592528329080832) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 3276963439258835685268783104, coefficient := (-3276963439258835685268783104) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 312033593902023651367059456, coefficient := (-312033593902023651367059456) }, { argument := 33471431219704693636097638400, coefficient := (-33471431219704693636097638400) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 131590771187010771930316800, coefficient := (-131590771187010771930316800) }, { argument := 1762768039025998465649868800, coefficient := (-1762768039025998465649868800) }, { argument := 3188334726885281828228300800, coefficient := (-3188334726885281828228300800) }, { argument := 33471433929070229462188032000, coefficient := (-33471433929070229462188032000) }, { argument := 1762768039025998465649868800, coefficient := (-1762768039025998465649868800) }, { argument := 104176027189716861111500800, coefficient := (-104176027189716861111500800) }, { argument := 104176027189716861111500800, coefficient := (-104176027189716861111500800) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 3188334726885281828228300800, coefficient := (-3188334726885281828228300800) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 312030884536487825276665856, coefficient := (-312030884536487825276665856) }, { argument := 131590771187010771930316800, coefficient := (-131590771187010771930316800) }, { argument := 70954028641764706300303769600, coefficient := (-70954028641764706300303769600) }, { argument := 184032166161950436793975308288, coefficient := (-184032166161950436793975308288) }, { argument := 183636087625218173067979653120, coefficient := (-183636087625218173067979653120) }, { argument := 182711904372842891040656457728, coefficient := (-182711904372842891040656457728) }, { argument := 183636087625218173067979653120, coefficient := (-183636087625218173067979653120) }, { argument := 70837351369391900203591663616, coefficient := (-70837351369391900203591663616) }, { argument := 531912346640967803929561661440, coefficient := (-531912346640967803929561661440) }, { argument := 2614415254362721588047188590592, coefficient := (-2614415254362721588047188590592) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-458573887044172120093636348084224)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    95156029233, 4704673429, 47502148147, 96673327903, 7893644746023, 14417513045,
    4704673429, 279, 6759, 5121, 2853, 279,
    2853, 5697, 279, 6759, 279, 118914411543275,
    7713005580879125, 7715472175, 625578825, 134082394825, 242516057825, 7713005588047125,
    134082394825, 3961999225, 3961999225, 7715472175, 7715472175, 242516057825,
    7715472175, 118914404375275, 625578825, 465, 11265, 8535,
    4755, 465, 4755, 9495, 465, 11265,
    465, 43990225, 7715472175, 1928868275, 10997325, 18521536105,
    785252774061, 7161, 16152822068963, 279, 465, 14229,
    465, 279, 227943, 14601, 785253472429, 14229,
    465, 14601, 465, 14229
  ]
def negativeCoefficients : Array ℕ := #[
    438829729582893900080854597632, 21696476673786136237824802816, 438129984909572704356087627776, 445827034645111371239167885312, 71099631073568512674487074816, 531912346640967803929561661440,
    21696476673786136237824802816, 84322575918120384935755776, 2042782403693819647959760896, 1547727280561629000917581824, 1724532681680268517718360064, 84322575918120384935755776,
    1724532681680268517718360064, 1721812598586135602075271168, 84322575918120384935755776, 2042782403693819647959760896, 84322575918120384935755776, 33471431219704693636097638400,
    2171018066247111462361235456000, 17790667577506524315621785600, 23079784965413869382428262400, 309172952765856625268778598400, 559203956557840210245084774400, 2171018068264724095423217664000,
    309172952765856625268778598400, 18271496430952646594422374400, 18271496430952646594422374400, 17790667577506524315621785600, 17790667577506524315621785600, 559203956557840210245084774400,
    17790667577506524315621785600, 33471429202092060574115430400, 23079784965413869382428262400, 4391800829068770048737280, 106394916859053106664570880, 80610795862584843797790720,
    89819410504180651964497920, 4391800829068770048737280, 89819410504180651964497920, 89677739509694562608087040, 4391800829068770048737280, 106394916859053106664570880,
    4391800829068770048737280, 101434552789987470029619200, 17790667577506524315621785600, 17790669710411307838288691200, 101432419885203947362713600, 41706791550403593937879040,
    7072928201305535774051008512, 135267465535318117501108224, 72745843450763691042063515648, 84322575918120384935755776, 4391800829068770048737280, 134389105369504363491360768,
    140537626530200641559592960, 84322575918120384935755776, 2152860766409511077891014656, 137902546032759379530350592, 7072934491645264909008109568, 134389105369504363491360768,
    4391800829068770048737280, 137902546032759379530350592, 4391800829068770048737280, 134389105369504363491360768
  ]
def negativeScales : Array ℕ := #[
    36, 32, 35, 36, 42, 33,
    32, 8, 12, 12, 11, 8,
    11, 12, 8, 12, 8, 46,
    52, 32, 29, 36, 37, 52,
    36, 31, 31, 32, 32, 37,
    32, 46, 29, 8, 13, 13,
    12, 8, 12, 13, 8, 13,
    8, 25, 32, 30, 23, 34,
    39, 12, 43, 8, 8, 13,
    8, 8, 17, 13, 39, 13,
    8, 13, 8, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36469576019655448, 32131447436937141, 35467273705495161, 36492398855020169, 42843828732298478, 33747103276834200,
    32131447436937141, 8124121311829188, 12722594099078657, 12322209843748895, 11478264031581849, 8124121311829188,
    11478264031581849, 12475986690870773, 8124121311829188, 12722594099078657, 8124121311829188, 46756916898285084,
    52776214578485229, 32845107305773121, 29220616439288111, 36964328879145728, 37819289320992647, 52776214579825982,
    36964328879145728, 31883581455254742, 31883581455254742, 32845107305773121, 32845107305773121, 37819289320992647,
    32845107305773121, 46756916811321373, 29220616439288111, 8861086908132560, 13459559693122857, 13059175437915101,
    12215229625747926, 8861086908132560, 12215229625747926, 13212952285036860, 8861086908132560, 13459559693122857,
    8861086908132560, 25390679644535597, 32845107305773121, 30845107478736336, 23390649308092819, 34108484704014136,
    39514366178253725, 12805945352531863, 43876851477434507, 8124121311829188, 8861086908132560, 13796546654402698,
    8861086908132560, 8124121311829188, 17798313580599046, 13833779561266426, 39514367461320319, 13796546654402698,
    8861086908132560, 13833779561266426, 8861086908132560, 13796546654402698
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
noncomputable def negativeCeiling : ℝ := 4544952847 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 438829729582893900080854597632, coefficient := (-438829729582893900080854597632) }, { argument := 21696476673786136237824802816, coefficient := (-21696476673786136237824802816) }, { argument := 438129984909572704356087627776, coefficient := (-438129984909572704356087627776) }, { argument := 445827034645111371239167885312, coefficient := (-445827034645111371239167885312) }, { argument := 71099631073568512674487074816, coefficient := (-71099631073568512674487074816) }, { argument := 531912346640967803929561661440, coefficient := (-531912346640967803929561661440) }, { argument := 21696476673786136237824802816, coefficient := (-21696476673786136237824802816) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 1547727280561629000917581824, coefficient := (-1547727280561629000917581824) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 1721812598586135602075271168, coefficient := (-1721812598586135602075271168) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 33471431219704693636097638400, coefficient := (-33471431219704693636097638400) }, { argument := 2171018066247111462361235456000, coefficient := (-2171018066247111462361235456000) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 23079784965413869382428262400, coefficient := (-23079784965413869382428262400) }, { argument := 309172952765856625268778598400, coefficient := (-309172952765856625268778598400) }, { argument := 559203956557840210245084774400, coefficient := (-559203956557840210245084774400) }, { argument := 2171018068264724095423217664000, coefficient := (-2171018068264724095423217664000) }, { argument := 309172952765856625268778598400, coefficient := (-309172952765856625268778598400) }, { argument := 18271496430952646594422374400, coefficient := (-18271496430952646594422374400) }, { argument := 18271496430952646594422374400, coefficient := (-18271496430952646594422374400) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 559203956557840210245084774400, coefficient := (-559203956557840210245084774400) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 33471429202092060574115430400, coefficient := (-33471429202092060574115430400) }, { argument := 23079784965413869382428262400, coefficient := (-23079784965413869382428262400) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 80610795862584843797790720, coefficient := (-80610795862584843797790720) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 89677739509694562608087040, coefficient := (-89677739509694562608087040) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 41706791550403593937879040, coefficient := (-41706791550403593937879040) }, { argument := 7072928201305535774051008512, coefficient := (-7072928201305535774051008512) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 72745843450763691042063515648, coefficient := (-72745843450763691042063515648) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 7072934491645264909008109568, coefficient := (-7072934491645264909008109568) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
