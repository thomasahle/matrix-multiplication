import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-141784453543867089299943150583808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    60629021725, 345672675, 3233881, 1184697099, 73227, 12151655699,
    2853, 4755, 145503, 4755, 2853, 2330901,
    149307, 592350271, 145503, 4755, 149307, 4755,
    145503, 4755, 3233881, 43990225, 7715472175, 1928868275,
    10997325, 6525469, 2409406551, 146223, 24730273151, 5697,
    9495, 290547, 9495, 5697, 4654449, 298143,
    1204706779, 290547, 9495, 298143, 9495, 290547,
    9495, 6525469, 958261855, 150894792285, 37723705505, 3833087395,
    72346369603, 3834079, 2714164166677, 25570803, 1257887, 12774329,
    25773821, 9077813301, 3834079, 1257887, 1108556391701, 118914404375275,
    10997325, 891675, 191115675, 345672675
  ]
def negativeCoefficients : Array ℕ := #[
    559204023600225703133236428800, 3188267684499788940076646400, 238618300687327673958006784, 43707608380238295936131923968, 2766437843528764080506535936, 448316965502574297930602119168,
    1724532681680268517718360064, 89819410504180651964497920, 2748473961427927950113636352, 2874221136133780862863933440, 1724532681680268517718360064, 44029475029149355592996880384,
    2820329489831272471685234688, 43707735404517987500104351744, 2748473961427927950113636352, 89819410504180651964497920, 2820329489831272471685234688, 89819410504180651964497920,
    2748473961427927950113636352, 2874221136133780862863933440, 238618300687327673958006784, 101434552789987470029619200, 17790667577506524315621785600, 17790669710411307838288691200,
    101432419885203947362713600, 240747313207850788148215808, 44445706015816220534863036416, 2762074376898592528329080832, 456193019689427689301413462016, 1721812598586135602075271168,
    89677739509694562608087040, 2744138828996653615807463424, 2869687664310226003458785280, 1721812598586135602075271168, 43960027907652274590484267008, 2815881020604409265893933056,
    44445835272151945017691209728, 2744138828996653615807463424, 89677739509694562608087040, 2815881020604409265893933056, 89677739509694562608087040, 2744138828996653615807463424,
    2869687664310226003458785280, 240747313207850788148215808, 4419202798695792915691601920, 173969850958559845032300380160, 173969885240680784516895211520, 4419248886732939574399467520,
    40727385398209872329179136, 282905096285536975801286656, 1527938591208611249572020224, 235849029350122211795533824, 11601959781323143376797696, 235644777776366062785265664,
    237721539894300394670522368, 40882836599722532243767296, 282905096285536975801286656, 11601959781323143376797696, 312030884536487825276665856, 33471429202092060574115430400,
    101432419885203947362713600, 131588004175399715497574400, 1762730972599625355519590400, 3188267684499788940076646400
  ]
def negativeScales : Array ℕ := #[
    35, 28, 21, 30, 16, 33,
    11, 12, 17, 12, 11, 21,
    17, 29, 17, 12, 17, 12,
    17, 12, 21, 25, 32, 30,
    23, 22, 31, 17, 34, 12,
    13, 18, 13, 12, 22, 18,
    30, 18, 13, 18, 13, 18,
    13, 22, 29, 37, 35, 31,
    36, 21, 41, 24, 20, 23,
    24, 33, 21, 20, 40, 46,
    23, 19, 27, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35819289493955860, 28364831323937085, 21624835160988955, 30141871094856067, 16160088071555465, 33500433847560719,
    11478264031581849, 12215229625747926, 17150689373553216, 12215229625747926, 11478264031581849, 21152456299727404,
    17187922279752191, 29141875287650843, 17150689373553216, 12215229625747926, 17187922279752191, 12215229625747926,
    17150689373553216, 12215229625747926, 21624835160988955, 25390679644535597, 32845107305773121, 30845107478736336,
    23390649308092819, 22637650164456439, 31166030701122137, 17157810730844399, 34525559123556275, 12475986690870773,
    13212952285036860, 18148412032842150, 13212952285036860, 12475986690870773, 22150178959016338, 18185644939041125,
    30166034896740120, 18148412032842150, 13212952285036860, 18185644939041125, 13212952285036860, 18148412032842150,
    13212952285036860, 22637650164456439, 29835844701649961, 37134752059869114, 35134752344163437, 31835859747494348,
    36074201571889664, 21870448635463357, 41303645123696905, 24607994130466023, 20262570895466728, 23606744176610483,
    24619403098551404, 33079697671355347, 21870448635463357, 20262570895466728, 40011819299884760, 46756916811321373,
    23390649308092819, 19766158443503858, 27509870869792188, 28364831323937085
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
noncomputable def negativeCeiling : ℝ := 449895257 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 559204023600225703133236428800, coefficient := (-559204023600225703133236428800) }, { argument := 3188267684499788940076646400, coefficient := (-3188267684499788940076646400) }, { argument := 238618300687327673958006784, coefficient := (-238618300687327673958006784) }, { argument := 43707608380238295936131923968, coefficient := (-43707608380238295936131923968) }, { argument := 2766437843528764080506535936, coefficient := (-2766437843528764080506535936) }, { argument := 448316965502574297930602119168, coefficient := (-448316965502574297930602119168) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 44029475029149355592996880384, coefficient := (-44029475029149355592996880384) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 43707735404517987500104351744, coefficient := (-43707735404517987500104351744) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 89819410504180651964497920, coefficient := (-89819410504180651964497920) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 238618300687327673958006784, coefficient := (-238618300687327673958006784) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 240747313207850788148215808, coefficient := (-240747313207850788148215808) }, { argument := 44445706015816220534863036416, coefficient := (-44445706015816220534863036416) }, { argument := 2762074376898592528329080832, coefficient := (-2762074376898592528329080832) }, { argument := 456193019689427689301413462016, coefficient := (-456193019689427689301413462016) }, { argument := 1721812598586135602075271168, coefficient := (-1721812598586135602075271168) }, { argument := 89677739509694562608087040, coefficient := (-89677739509694562608087040) }, { argument := 2744138828996653615807463424, coefficient := (-2744138828996653615807463424) }, { argument := 2869687664310226003458785280, coefficient := (-2869687664310226003458785280) }, { argument := 1721812598586135602075271168, coefficient := (-1721812598586135602075271168) }, { argument := 43960027907652274590484267008, coefficient := (-43960027907652274590484267008) }, { argument := 2815881020604409265893933056, coefficient := (-2815881020604409265893933056) }, { argument := 44445835272151945017691209728, coefficient := (-44445835272151945017691209728) }, { argument := 2744138828996653615807463424, coefficient := (-2744138828996653615807463424) }, { argument := 89677739509694562608087040, coefficient := (-89677739509694562608087040) }, { argument := 2815881020604409265893933056, coefficient := (-2815881020604409265893933056) }, { argument := 89677739509694562608087040, coefficient := (-89677739509694562608087040) }, { argument := 2744138828996653615807463424, coefficient := (-2744138828996653615807463424) }, { argument := 2869687664310226003458785280, coefficient := (-2869687664310226003458785280) }, { argument := 240747313207850788148215808, coefficient := (-240747313207850788148215808) }, { argument := 4419202798695792915691601920, coefficient := (-4419202798695792915691601920) }, { argument := 173969850958559845032300380160, coefficient := (-173969850958559845032300380160) }, { argument := 173969885240680784516895211520, coefficient := (-173969885240680784516895211520) }, { argument := 4419248886732939574399467520, coefficient := (-4419248886732939574399467520) }, { argument := 40727385398209872329179136, coefficient := (-40727385398209872329179136) }, { argument := 282905096285536975801286656, coefficient := (-282905096285536975801286656) }, { argument := 1527938591208611249572020224, coefficient := (-1527938591208611249572020224) }, { argument := 235849029350122211795533824, coefficient := (-235849029350122211795533824) }, { argument := 11601959781323143376797696, coefficient := (-11601959781323143376797696) }, { argument := 235644777776366062785265664, coefficient := (-235644777776366062785265664) }, { argument := 237721539894300394670522368, coefficient := (-237721539894300394670522368) }, { argument := 40882836599722532243767296, coefficient := (-40882836599722532243767296) }, { argument := 282905096285536975801286656, coefficient := (-282905096285536975801286656) }, { argument := 11601959781323143376797696, coefficient := (-11601959781323143376797696) }, { argument := 312030884536487825276665856, coefficient := (-312030884536487825276665856) }, { argument := 33471429202092060574115430400, coefficient := (-33471429202092060574115430400) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 131588004175399715497574400, coefficient := (-131588004175399715497574400) }, { argument := 1762730972599625355519590400, coefficient := (-1762730972599625355519590400) }, { argument := 3188267684499788940076646400, coefficient := (-3188267684499788940076646400) }] }

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


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-83502608205016002566888070578176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    118914414000875, 191115675, 5647275, 5647275, 10997325, 10997325,
    345672675, 10997325, 1108546766101, 891675, 2324067839, 98520240987,
    7161, 2026590474901, 279, 465, 14229, 465,
    279, 227943, 14601, 98520328283, 14229, 465,
    14601, 465, 14229, 465, 2324067839, 3566775,
    625578825, 156394725, 891675, 970751, 359260029, 173481,
    3688184245, 6759, 11265, 344709, 11265, 6759,
    5522103, 353721, 179630537, 344709, 11265, 353721,
    11265, 344709, 11265, 970751, 476753507, 75075224297,
    18768809757, 1907033879, 318463, 117281277, 7161, 1203515573,
    279, 465, 14229, 465
  ]
def negativeCoefficients : Array ℕ := #[
    33471431911457596400205824000, 1762730972599625355519590400, 104173836638858108102246400, 104173836638858108102246400, 101432419885203947362713600, 101432419885203947362713600,
    3188267684499788940076646400, 101432419885203947362713600, 312028175170951999186272256, 131588004175399715497574400, 41866684214816615564312576, 7099131529560074672859512832,
    135267465535318117501108224, 73015616860773921012127367168, 84322575918120384935755776, 4391800829068770048737280, 134389105369504363491360768, 140537626530200641559592960,
    84322575918120384935755776, 2152860766409511077891014656, 137902546032759379530350592, 7099137819899803807816613888, 134389105369504363491360768, 4391800829068770048737280,
    137902546032759379530350592, 4391800829068770048737280, 134389105369504363491360768, 140537626530200641559592960, 41866684214816615564312576, 131590771187010771930316800,
    23079784965413869382428262400, 23079787732425480438861004800, 131588004175399715497574400, 286515124100761935052537856, 53017422487011773209129254912, 3276963439258835685268783104,
    544279926913621495809163919360, 2042782403693819647959760896, 106394916859053106664570880, 3255684455887025063935868928, 3404637339489699413266268160, 2042782403693819647959760896,
    52154788244307832886972645376, 3340800389374267549267525632, 53017576701792229420980764672, 3255684455887025063935868928, 106394916859053106664570880, 3340800389374267549267525632,
    106394916859053106664570880, 3255684455887025063935868928, 3404637339489699413266268160, 286515124100761935052537856, 4397274964936247616162758656, 173111681110387511050312351744,
    173111715077760879777237958656, 4397320738225823517201399808, 11749210915891529872572416, 2163457701456838340621893632, 135267465535318117501108224, 22200943763854905248703315968,
    84322575918120384935755776, 4391800829068770048737280, 134389105369504363491360768, 140537626530200641559592960
  ]
def negativeScales : Array ℕ := #[
    46, 27, 22, 22, 23, 23,
    28, 23, 40, 19, 31, 36,
    12, 40, 8, 8, 13, 8,
    8, 17, 13, 36, 13, 8,
    13, 8, 13, 8, 31, 21,
    29, 27, 19, 19, 28, 17,
    31, 12, 13, 18, 13, 12,
    22, 18, 27, 18, 13, 18,
    13, 18, 13, 19, 28, 36,
    34, 30, 18, 26, 12, 30,
    8, 8, 13, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    46756916928101212, 27509870869792188, 22429123455907472, 22429123455907472, 23390649308092819, 23390649308092819,
    28364831323937085, 23390649308092819, 40011806772903021, 19766158443503858, 31114005035276229, 36519701105642446,
    12805945352531863, 40882191726165601, 8124121311829188, 8861086908132560, 13796546654402698, 8861086908132560,
    8124121311829188, 17798313580599046, 13833779561266426, 36519702383973165, 13796546654402698, 8861086908132560,
    13833779561266426, 8861086908132560, 13796546654402698, 8861086908132560, 31114005035276229, 21766188779946842,
    29220616439288111, 27220616612251320, 19766158443503858, 19888741766299506, 28420453190204936, 17404418138930338,
    31780263582501075, 12722594099078657, 13459559693122857, 18395019440928086, 13459559693122857, 12722594099078657,
    22396786367102274, 18432252347127079, 27420457386647633, 18395019440928086, 13459559693122857, 18432252347127079,
    13459559693122857, 18395019440928086, 13459559693122857, 19888741766299506, 28828668311290579, 36127617828901619,
    34127618111982206, 30828683328899481, 18280766239956687, 26805397477063239, 12805945352531863, 30164607663804084,
    8124121311829188, 8861086908132560, 13796546654402698, 8861086908132560
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
noncomputable def negativeCeiling : ℝ := 15686349 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33471431911457596400205824000, coefficient := (-33471431911457596400205824000) }, { argument := 1762730972599625355519590400, coefficient := (-1762730972599625355519590400) }, { argument := 104173836638858108102246400, coefficient := (-104173836638858108102246400) }, { argument := 104173836638858108102246400, coefficient := (-104173836638858108102246400) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 3188267684499788940076646400, coefficient := (-3188267684499788940076646400) }, { argument := 101432419885203947362713600, coefficient := (-101432419885203947362713600) }, { argument := 312028175170951999186272256, coefficient := (-312028175170951999186272256) }, { argument := 131588004175399715497574400, coefficient := (-131588004175399715497574400) }, { argument := 41866684214816615564312576, coefficient := (-41866684214816615564312576) }, { argument := 7099131529560074672859512832, coefficient := (-7099131529560074672859512832) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 73015616860773921012127367168, coefficient := (-73015616860773921012127367168) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 7099137819899803807816613888, coefficient := (-7099137819899803807816613888) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 41866684214816615564312576, coefficient := (-41866684214816615564312576) }, { argument := 131590771187010771930316800, coefficient := (-131590771187010771930316800) }, { argument := 23079784965413869382428262400, coefficient := (-23079784965413869382428262400) }, { argument := 23079787732425480438861004800, coefficient := (-23079787732425480438861004800) }, { argument := 131588004175399715497574400, coefficient := (-131588004175399715497574400) }, { argument := 286515124100761935052537856, coefficient := (-286515124100761935052537856) }, { argument := 53017422487011773209129254912, coefficient := (-53017422487011773209129254912) }, { argument := 3276963439258835685268783104, coefficient := (-3276963439258835685268783104) }, { argument := 544279926913621495809163919360, coefficient := (-544279926913621495809163919360) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 52154788244307832886972645376, coefficient := (-52154788244307832886972645376) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }, { argument := 53017576701792229420980764672, coefficient := (-53017576701792229420980764672) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 286515124100761935052537856, coefficient := (-286515124100761935052537856) }, { argument := 4397274964936247616162758656, coefficient := (-4397274964936247616162758656) }, { argument := 173111681110387511050312351744, coefficient := (-173111681110387511050312351744) }, { argument := 173111715077760879777237958656, coefficient := (-173111715077760879777237958656) }, { argument := 4397320738225823517201399808, coefficient := (-4397320738225823517201399808) }, { argument := 11749210915891529872572416, coefficient := (-11749210915891529872572416) }, { argument := 2163457701456838340621893632, coefficient := (-2163457701456838340621893632) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 22200943763854905248703315968, coefficient := (-22200943763854905248703315968) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
