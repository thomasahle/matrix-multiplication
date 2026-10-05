import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-237989293983990327348053619507200)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    28992118158459, 131439, 596638323160181, 5121, 8535, 261171,
    8535, 5121, 4183857, 267999, 28992130819195, 261171,
    8535, 267999, 8535, 261171, 8535, 696429582751,
    22589575, 3961999225, 990499925, 5647275, 6473427, 2373043833,
    73227, 24342126801, 2853, 4755, 145503, 4755,
    2853, 2330901, 149307, 1186525365, 145503, 4755,
    149307, 4755, 145503, 4755, 6473427, 240074911,
    37803449181, 9450864161, 960309667, 465, 11265, 8535,
    4755, 465, 4755, 9495, 465, 11265,
    465, 14601, 353721, 267999, 149307, 14601,
    149307, 298143, 14601, 353721
  ]
def negativeCoefficients : Array ℕ := #[
    261137785070234686208058851328, 2482812512567613188971954176, 2687020129859148725030041419776, 1547727280561629000917581824, 80610795862584843797790720, 2466690353395096220212396032,
    2579545467602715001529303040, 1547727280561629000917581824, 39515412131839090429677010944, 2531178990085164095250628608, 261137899108006549880506941440, 2466690353395096220212396032,
    80610795862584843797790720, 2531178990085164095250628608, 80610795862584843797790720, 2466690353395096220212396032, 2579545467602715001529303040, 1568220004683596804283957248,
    104176027189716861111500800, 18271496430952646594422374400, 18271498621503505347431628800, 104173836638858108102246400, 238827302297682803177816064, 43774932263045748895543984128,
    2766437843528764080506535936, 449032983307833195881526460416, 1724532681680268517718360064, 89819410504180651964497920, 2748473961427927950113636352, 2874221136133780862863933440,
    1724532681680268517718360064, 44029475029149355592996880384, 2820329489831272471685234688, 43775059490239625270321479680, 2748473961427927950113636352, 89819410504180651964497920,
    2820329489831272471685234688, 89819410504180651964497920, 2748473961427927950113636352, 2874221136133780862863933440, 238827302297682803177816064, 4428600441735598044061106176,
    174337638036347988167438106624, 174337672453360743691034034176, 4428646664664560741770067968, 4391800829068770048737280, 106394916859053106664570880, 80610795862584843797790720,
    89819410504180651964497920, 4391800829068770048737280, 89819410504180651964497920, 89677739509694562608087040, 4391800829068770048737280, 106394916859053106664570880,
    4391800829068770048737280, 137902546032759379530350592, 3340800389374267549267525632, 2531178990085164095250628608, 2820329489831272471685234688, 137902546032759379530350592,
    2820329489831272471685234688, 2815881020604409265893933056, 137902546032759379530350592, 3340800389374267549267525632
  ]
def negativeScales : Array ℕ := #[
    44, 17, 49, 12, 13, 17,
    13, 12, 21, 18, 44, 17,
    13, 18, 13, 17, 13, 39,
    24, 31, 29, 22, 22, 31,
    16, 34, 11, 12, 17, 12,
    11, 21, 17, 30, 17, 12,
    17, 12, 17, 12, 22, 27,
    35, 33, 29, 8, 13, 13,
    12, 8, 12, 13, 8, 13,
    8, 13, 18, 18, 17, 13,
    17, 18, 13, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    44720725973918920, 17004033883722640, 49083849975988022, 12322209843748895, 13059175437915101, 17994635207450153,
    13059175437915101, 12322209843748895, 21996402134248402, 18031868091919366, 44720726603937637, 17994635207450153,
    13059175437915101, 18031868091919366, 13059175437915101, 17994635207450153, 13059175437915101, 39341186530468696,
    24429153792350249, 31883581455254742, 29883581628217962, 22429123455907472, 22626098239355420, 31144091603092790,
    16160088071555465, 34502736172439536, 11478264031581849, 12215229625747926, 17150689373553216, 12215229625747926,
    11478264031581849, 21152456299727404, 17187922279752191, 30144095796126690, 17150689373553216, 12215229625747926,
    17187922279752191, 12215229625747926, 17150689373553216, 12215229625747926, 22626098239355420, 27838909403270697,
    35137798820603223, 33137799105414060, 29838924461130412, 8861086908132560, 13459559693122857, 13059175437915101,
    12215229625747926, 8861086908132560, 12215229625747926, 13212952285036860, 8861086908132560, 13459559693122857,
    8861086908132560, 13833779561266426, 18432252347127079, 18031868091919366, 17187922279752191, 13833779561266426,
    17187922279752191, 18185644939041125, 13833779561266426, 18432252347127079
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
noncomputable def negativeCeiling : ℝ := 1783819 / 781250000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 261137785070234686208058851328, coefficient := (-261137785070234686208058851328) }, { argument := 2482812512567613188971954176, coefficient := (-2482812512567613188971954176) }, { argument := 2687020129859148725030041419776, coefficient := (-2687020129859148725030041419776) }, { argument := 1547727280561629000917581824, coefficient := (-1547727280561629000917581824) }, { argument := 80610795862584843797790720, coefficient := (-80610795862584843797790720) }, { argument := 2466690353395096220212396032, coefficient := (-2466690353395096220212396032) }, { argument := 2579545467602715001529303040, coefficient := (-2579545467602715001529303040) }, { argument := 1547727280561629000917581824, coefficient := (-1547727280561629000917581824) }, { argument := 39515412131839090429677010944, coefficient := (-39515412131839090429677010944) }, { argument := 2531178990085164095250628608, coefficient := (-2531178990085164095250628608) }, { argument := 261137899108006549880506941440, coefficient := (-261137899108006549880506941440) }, { argument := 2466690353395096220212396032, coefficient := (-2466690353395096220212396032) }, { argument := 80610795862584843797790720, coefficient := (-80610795862584843797790720) }, { argument := 2531178990085164095250628608, coefficient := (-2531178990085164095250628608) }, { argument := 80610795862584843797790720, coefficient := (-80610795862584843797790720) }, { argument := 2466690353395096220212396032, coefficient := (-2466690353395096220212396032) }, { argument := 2579545467602715001529303040, coefficient := (-2579545467602715001529303040) }, { argument := 1568220004683596804283957248, coefficient := (-1568220004683596804283957248) }, { argument := 104176027189716861111500800, coefficient := (-104176027189716861111500800) }, { argument := 18271496430952646594422374400, coefficient := (-18271496430952646594422374400) }, { argument := 18271498621503505347431628800, coefficient := (-18271498621503505347431628800) }, { argument := 104173836638858108102246400, coefficient := (-104173836638858108102246400) }, { argument := 238827302297682803177816064, coefficient := (-238827302297682803177816064) }, { argument := 43774932263045748895543984128, coefficient := (-43774932263045748895543984128) }, { argument := 2766437843528764080506535936, coefficient := (-2766437843528764080506535936) }, { argument := 449032983307833195881526460416, coefficient := (-449032983307833195881526460416) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 44029475029149355592996880384, coefficient := (-44029475029149355592996880384) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 43775059490239625270321479680, coefficient := (-43775059490239625270321479680) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 238827302297682803177816064, coefficient := (-238827302297682803177816064) }, { argument := 4428600441735598044061106176, coefficient := (-4428600441735598044061106176) }, { argument := 174337638036347988167438106624, coefficient := (-174337638036347988167438106624) }, { argument := 174337672453360743691034034176, coefficient := (-174337672453360743691034034176) }, { argument := 4428646664664560741770067968, coefficient := (-4428646664664560741770067968) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 80610795862584843797790720, coefficient := (-80610795862584843797790720) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 89677739509694562608087040, coefficient := (-89677739509694562608087040) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }, { argument := 2531178990085164095250628608, coefficient := (-2531178990085164095250628608) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 2815881020604409265893933056, coefficient := (-2815881020604409265893933056) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-45821235486801429318164344209408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14601, 22589575, 3961999225, 990499925, 5647275, 465,
    11265, 8535, 4755, 465, 4755, 9495,
    465, 11265, 465, 43990225, 7715472175, 1928868275,
    10997325, 318463, 117281277, 7161, 1203515573, 279,
    465, 14229, 465, 279, 227943, 14601,
    58640809, 14229, 465, 14601, 465, 14229,
    465, 318463, 14229, 344709, 261171, 145503,
    14229, 145503, 290547, 14229, 344709, 14229,
    43990225, 7715472175, 1928868275, 10997325, 465, 11265,
    8535, 4755, 465, 4755, 9495, 465,
    11265, 465, 1382719775, 242516057825
  ]
def negativeCoefficients : Array ℕ := #[
    137902546032759379530350592, 104176027189716861111500800, 18271496430952646594422374400, 18271498621503505347431628800, 104173836638858108102246400, 4391800829068770048737280,
    106394916859053106664570880, 80610795862584843797790720, 89819410504180651964497920, 4391800829068770048737280, 89819410504180651964497920, 89677739509694562608087040,
    4391800829068770048737280, 106394916859053106664570880, 4391800829068770048737280, 101434552789987470029619200, 17790667577506524315621785600, 17790669710411307838288691200,
    101432419885203947362713600, 11749210915891529872572416, 2163457701456838340621893632, 135267465535318117501108224, 22200943763854905248703315968, 84322575918120384935755776,
    4391800829068770048737280, 134389105369504363491360768, 140537626530200641559592960, 84322575918120384935755776, 2152860766409511077891014656, 137902546032759379530350592,
    2163463991796567475578994688, 134389105369504363491360768, 4391800829068770048737280, 137902546032759379530350592, 4391800829068770048737280, 134389105369504363491360768,
    140537626530200641559592960, 11749210915891529872572416, 134389105369504363491360768, 3255684455887025063935868928, 2466690353395096220212396032, 2748473961427927950113636352,
    134389105369504363491360768, 2748473961427927950113636352, 2744138828996653615807463424, 134389105369504363491360768, 3255684455887025063935868928, 134389105369504363491360768,
    101434552789987470029619200, 17790667577506524315621785600, 17790669710411307838288691200, 101432419885203947362713600, 140537626530200641559592960, 3404637339489699413266268160,
    2579545467602715001529303040, 2874221136133780862863933440, 140537626530200641559592960, 2874221136133780862863933440, 2869687664310226003458785280, 140537626530200641559592960,
    3404637339489699413266268160, 140537626530200641559592960, 3188334726885281828228300800, 559203956557840210245084774400
  ]
def negativeScales : Array ℕ := #[
    13, 24, 31, 29, 22, 8,
    13, 13, 12, 8, 12, 13,
    8, 13, 8, 25, 32, 30,
    23, 18, 26, 12, 30, 8,
    8, 13, 8, 8, 17, 13,
    25, 13, 8, 13, 8, 13,
    8, 18, 13, 18, 17, 17,
    13, 17, 18, 13, 18, 13,
    25, 32, 30, 23, 8, 13,
    13, 12, 8, 12, 13, 8,
    13, 8, 30, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13833779561266426, 24429153792350249, 31883581455254742, 29883581628217962, 22429123455907472, 8861086908132560,
    13459559693122857, 13059175437915101, 12215229625747926, 8861086908132560, 12215229625747926, 13212952285036860,
    8861086908132560, 13459559693122857, 8861086908132560, 25390679644535597, 32845107305773121, 30845107478736336,
    23390649308092819, 18280766239956687, 26805397477063239, 12805945352531863, 30164607663804084, 8124121311829188,
    8861086908132560, 13796546654402698, 8861086908132560, 8124121311829188, 17798313580599046, 13833779561266426,
    25805401671750691, 13796546654402698, 8861086908132560, 13833779561266426, 8861086908132560, 13796546654402698,
    8861086908132560, 18280766239956687, 13796546654402698, 18395019440928086, 17994635207450153, 17150689373553216,
    13796546654402698, 17150689373553216, 18148412032842150, 13796546654402698, 18395019440928086, 13796546654402698,
    25390679644535597, 32845107305773121, 30845107478736336, 23390649308092819, 8861086908132560, 13459559693122857,
    13059175437915101, 12215229625747926, 8861086908132560, 12215229625747926, 13212952285036860, 8861086908132560,
    13459559693122857, 8861086908132560, 30364861660379862, 37819289320992647
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
noncomputable def negativeCeiling : ℝ := 31363599 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 104176027189716861111500800, coefficient := (-104176027189716861111500800) }, { argument := 18271496430952646594422374400, coefficient := (-18271496430952646594422374400) }, { argument := 18271498621503505347431628800, coefficient := (-18271498621503505347431628800) }, { argument := 104173836638858108102246400, coefficient := (-104173836638858108102246400) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 80610795862584843797790720, coefficient := (-80610795862584843797790720) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 89677739509694562608087040, coefficient := (-89677739509694562608087040) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 11749210915891529872572416, coefficient := (-11749210915891529872572416) }, { argument := 2163457701456838340621893632, coefficient := (-2163457701456838340621893632) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 22200943763854905248703315968, coefficient := (-22200943763854905248703315968) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2163463991796567475578994688, coefficient := (-2163463991796567475578994688) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 11749210915891529872572416, coefficient := (-11749210915891529872572416) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 2466690353395096220212396032, coefficient := (-2466690353395096220212396032) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 2744138828996653615807463424, coefficient := (-2744138828996653615807463424) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 2579545467602715001529303040, coefficient := (-2579545467602715001529303040) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 2869687664310226003458785280, coefficient := (-2869687664310226003458785280) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 3188334726885281828228300800, coefficient := (-3188334726885281828228300800) }, { argument := 559203956557840210245084774400, coefficient := (-559203956557840210245084774400) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
