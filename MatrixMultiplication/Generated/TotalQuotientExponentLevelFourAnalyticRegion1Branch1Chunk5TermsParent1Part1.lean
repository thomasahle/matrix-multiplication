import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-137187093964915411848026853998592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    465, 18521536105, 14229, 344709, 261171, 145503,
    14229, 145503, 290547, 14229, 344709, 14229,
    465, 11265, 8535, 4755, 465, 4755,
    9495, 465, 11265, 465, 3566775, 625578825,
    156394725, 891675, 279, 6759, 5121, 2853,
    279, 2853, 5697, 279, 6759, 279,
    227943, 5522103, 4183857, 2330901, 227943, 2330901,
    4654449, 227943, 5522103, 227943, 764478775, 134082394825,
    33520602725, 191115675, 14601, 353721, 267999, 149307,
    14601, 149307, 298143, 14601, 353721, 14601,
    1382719775, 242516057825, 60629021725, 345672675
  ]
def negativeCoefficients : Array ℕ := #[
    140537626530200641559592960, 41706791550403593937879040, 134389105369504363491360768, 3255684455887025063935868928, 2466690353395096220212396032, 2748473961427927950113636352,
    134389105369504363491360768, 2748473961427927950113636352, 2744138828996653615807463424, 134389105369504363491360768, 3255684455887025063935868928, 134389105369504363491360768,
    140537626530200641559592960, 3404637339489699413266268160, 2579545467602715001529303040, 2874221136133780862863933440, 140537626530200641559592960, 2874221136133780862863933440,
    2869687664310226003458785280, 140537626530200641559592960, 3404637339489699413266268160, 140537626530200641559592960, 131590771187010771930316800, 23079784965413869382428262400,
    23079787732425480438861004800, 131588004175399715497574400, 84322575918120384935755776, 2042782403693819647959760896, 1547727280561629000917581824, 1724532681680268517718360064,
    84322575918120384935755776, 1724532681680268517718360064, 1721812598586135602075271168, 84322575918120384935755776, 2042782403693819647959760896, 84322575918120384935755776,
    2152860766409511077891014656, 52154788244307832886972645376, 39515412131839090429677010944, 44029475029149355592996880384, 2152860766409511077891014656, 44029475029149355592996880384,
    43960027907652274590484267008, 2152860766409511077891014656, 52154788244307832886972645376, 2152860766409511077891014656, 1762768039025998465649868800, 309172952765856625268778598400,
    309172989832282998378908876800, 1762730972599625355519590400, 137902546032759379530350592, 3340800389374267549267525632, 2531178990085164095250628608, 2820329489831272471685234688,
    137902546032759379530350592, 2820329489831272471685234688, 2815881020604409265893933056, 137902546032759379530350592, 3340800389374267549267525632, 137902546032759379530350592,
    3188334726885281828228300800, 559203956557840210245084774400, 559204023600225703133236428800, 3188267684499788940076646400
  ]
def negativeScales : Array ℕ := #[
    8, 34, 13, 18, 17, 17,
    13, 17, 18, 13, 18, 13,
    8, 13, 13, 12, 8, 12,
    13, 8, 13, 8, 21, 29,
    27, 19, 8, 12, 12, 11,
    8, 11, 12, 8, 12, 8,
    17, 22, 21, 21, 17, 21,
    22, 17, 22, 17, 29, 36,
    34, 27, 13, 18, 18, 17,
    13, 17, 18, 13, 18, 13,
    30, 37, 35, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    8861086908132560, 34108484704014136, 13796546654402698, 18395019440928086, 17994635207450153, 17150689373553216,
    13796546654402698, 17150689373553216, 18148412032842150, 13796546654402698, 18395019440928086, 13796546654402698,
    8861086908132560, 13459559693122857, 13059175437915101, 12215229625747926, 8861086908132560, 12215229625747926,
    13212952285036860, 8861086908132560, 13459559693122857, 8861086908132560, 21766188779946842, 29220616439288111,
    27220616612251320, 19766158443503858, 8124121311829188, 12722594099078657, 12322209843748895, 11478264031581849,
    8124121311829188, 11478264031581849, 12475986690870773, 8124121311829188, 12722594099078657, 8124121311829188,
    17798313580599046, 22396786367102274, 21996402134248402, 21152456299727404, 17798313580599046, 21152456299727404,
    22150178959016338, 17798313580599046, 22396786367102274, 17798313580599046, 29509901206234966, 36964328879145728,
    34964329052108976, 27509870869792188, 13833779561266426, 18432252347127079, 18031868091919366, 17187922279752191,
    13833779561266426, 17187922279752191, 18185644939041125, 13833779561266426, 18432252347127079, 13833779561266426,
    30364861660379862, 37819289320992647, 35819289493955860, 28364831323937085
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
noncomputable def negativeCeiling : ℝ := 8693713 / 10000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 41706791550403593937879040, coefficient := (-41706791550403593937879040) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 2466690353395096220212396032, coefficient := (-2466690353395096220212396032) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 2744138828996653615807463424, coefficient := (-2744138828996653615807463424) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 2579545467602715001529303040, coefficient := (-2579545467602715001529303040) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 2874221136133780862863933440, coefficient := (-2874221136133780862863933440) }, { argument := 2869687664310226003458785280, coefficient := (-2869687664310226003458785280) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 140537626530200641559592960, coefficient := (-140537626530200641559592960) }, { argument := 131590771187010771930316800, coefficient := (-131590771187010771930316800) }, { argument := 23079784965413869382428262400, coefficient := (-23079784965413869382428262400) }, { argument := 23079787732425480438861004800, coefficient := (-23079787732425480438861004800) }, { argument := 131588004175399715497574400, coefficient := (-131588004175399715497574400) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 1547727280561629000917581824, coefficient := (-1547727280561629000917581824) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1724532681680268517718360064, coefficient := (-1724532681680268517718360064) }, { argument := 1721812598586135602075271168, coefficient := (-1721812598586135602075271168) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 52154788244307832886972645376, coefficient := (-52154788244307832886972645376) }, { argument := 39515412131839090429677010944, coefficient := (-39515412131839090429677010944) }, { argument := 44029475029149355592996880384, coefficient := (-44029475029149355592996880384) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 44029475029149355592996880384, coefficient := (-44029475029149355592996880384) }, { argument := 43960027907652274590484267008, coefficient := (-43960027907652274590484267008) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 52154788244307832886972645376, coefficient := (-52154788244307832886972645376) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 1762768039025998465649868800, coefficient := (-1762768039025998465649868800) }, { argument := 309172952765856625268778598400, coefficient := (-309172952765856625268778598400) }, { argument := 309172989832282998378908876800, coefficient := (-309172989832282998378908876800) }, { argument := 1762730972599625355519590400, coefficient := (-1762730972599625355519590400) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }, { argument := 2531178990085164095250628608, coefficient := (-2531178990085164095250628608) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2820329489831272471685234688, coefficient := (-2820329489831272471685234688) }, { argument := 2815881020604409265893933056, coefficient := (-2815881020604409265893933056) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3188334726885281828228300800, coefficient := (-3188334726885281828228300800) }, { argument := 559203956557840210245084774400, coefficient := (-559203956557840210245084774400) }, { argument := 559204023600225703133236428800, coefficient := (-559204023600225703133236428800) }, { argument := 3188267684499788940076646400, coefficient := (-3188267684499788940076646400) }] }

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
def constantNumerator : ℤ := (-450805457159110935982819709550592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    970751, 359260029, 173481, 3688184245, 6759, 11265,
    344709, 11265, 6759, 5522103, 353721, 179630537,
    344709, 11265, 353721, 11265, 344709, 11265,
    970751, 507012233, 2023659785, 1006709221, 2023659785, 3059387158063,
    702762313, 112849339676809, 4642086549, 229420553, 2317476575, 4713153275,
    383837566761, 702762313, 229420553, 118914421168875, 7713005588047125, 1928868275,
    156394725, 33520602725, 60629021725, 7713005595215125, 33520602725, 990499925,
    990499925, 1928868275, 1928868275, 60629021725, 1928868275, 118914414000875,
    156394725, 14229, 344709, 261171, 145503, 14229,
    145503, 290547, 14229, 344709, 14229, 764478775,
    134082394825, 33520602725, 191115675, 696429582751
  ]
def negativeCoefficients : Array ℕ := #[
    286515124100761935052537856, 53017422487011773209129254912, 3276963439258835685268783104, 544279926913621495809163919360, 2042782403693819647959760896, 106394916859053106664570880,
    3255684455887025063935868928, 3404637339489699413266268160, 2042782403693819647959760896, 52154788244307832886972645376, 3340800389374267549267525632, 53017576701792229420980764672,
    3255684455887025063935868928, 106394916859053106664570880, 3340800389374267549267525632, 106394916859053106664570880, 3255684455887025063935868928, 3404637339489699413266268160,
    286515124100761935052537856, 4676362452195498179128459264, 4666241768269136921960120320, 4642626839107627321900662784, 4666241768269136921960120320, 6889127432517303773507354624,
    51854706130236667935412191232, 254114122058741770951571013632, 42815691268706287044727406592, 2116031113219959046562381824, 42749897275841959223833395200, 43471166122045507298865971200,
    6914602890542549925126733824, 51854706130236667935412191232, 2116031113219959046562381824, 33471433929070229462188032000, 2171018068264724095423217664000, 17790669710411307838288691200,
    23079787732425480438861004800, 309172989832282998378908876800, 559204023600225703133236428800, 2171018070282336728485199872000, 309172989832282998378908876800, 18271498621503505347431628800,
    18271498621503505347431628800, 17790669710411307838288691200, 17790669710411307838288691200, 559204023600225703133236428800, 17790669710411307838288691200, 33471431911457596400205824000,
    23079787732425480438861004800, 134389105369504363491360768, 3255684455887025063935868928, 2466690353395096220212396032, 2748473961427927950113636352, 134389105369504363491360768,
    2748473961427927950113636352, 2744138828996653615807463424, 134389105369504363491360768, 3255684455887025063935868928, 134389105369504363491360768, 1762768039025998465649868800,
    309172952765856625268778598400, 309172989832282998378908876800, 1762730972599625355519590400, 1568220004683596804283957248
  ]
def negativeScales : Array ℕ := #[
    19, 28, 17, 31, 12, 13,
    18, 13, 12, 22, 18, 27,
    18, 13, 18, 13, 18, 13,
    19, 28, 30, 29, 30, 41,
    29, 46, 32, 27, 31, 32,
    38, 29, 27, 46, 52, 30,
    27, 34, 35, 52, 34, 29,
    29, 30, 30, 35, 30, 46,
    27, 13, 18, 17, 17, 13,
    17, 18, 13, 18, 13, 29,
    36, 34, 27, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19888741766299506, 28420453190204936, 17404418138930338, 31780263582501075, 12722594099078657, 13459559693122857,
    18395019440928086, 13459559693122857, 12722594099078657, 22396786367102274, 18432252347127079, 27420457386647633,
    18395019440928086, 13459559693122857, 18432252347127079, 13459559693122857, 18395019440928086, 13459559693122857,
    19888741766299506, 28917445321501164, 30914319626060190, 29906999892825428, 30914319626060190, 41476379826673842,
    29388461585183594, 46681391305282106, 32112126275128175, 27773419402711936, 31109907610182426, 32134045453541674,
    38481704960941952, 29388461585183594, 27773419402711936, 46756917015064915, 52776214579825982, 30845107478736336,
    27220616612251320, 34964329052108976, 35819289493955860, 52776214581166736, 34964329052108976, 29883581628217962,
    29883581628217962, 30845107478736336, 30845107478736336, 35819289493955860, 30845107478736336, 46756916928101212,
    27220616612251320, 13796546654402698, 18395019440928086, 17994635207450153, 17150689373553216, 13796546654402698,
    17150689373553216, 18148412032842150, 13796546654402698, 18395019440928086, 13796546654402698, 29509901206234966,
    36964328879145728, 34964329052108976, 27509870869792188, 39341186530468696
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
noncomputable def negativeCeiling : ℝ := 4374459257 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 286515124100761935052537856, coefficient := (-286515124100761935052537856) }, { argument := 53017422487011773209129254912, coefficient := (-53017422487011773209129254912) }, { argument := 3276963439258835685268783104, coefficient := (-3276963439258835685268783104) }, { argument := 544279926913621495809163919360, coefficient := (-544279926913621495809163919360) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 2042782403693819647959760896, coefficient := (-2042782403693819647959760896) }, { argument := 52154788244307832886972645376, coefficient := (-52154788244307832886972645376) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }, { argument := 53017576701792229420980764672, coefficient := (-53017576701792229420980764672) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 3340800389374267549267525632, coefficient := (-3340800389374267549267525632) }, { argument := 106394916859053106664570880, coefficient := (-106394916859053106664570880) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 3404637339489699413266268160, coefficient := (-3404637339489699413266268160) }, { argument := 286515124100761935052537856, coefficient := (-286515124100761935052537856) }, { argument := 4676362452195498179128459264, coefficient := (-4676362452195498179128459264) }, { argument := 4666241768269136921960120320, coefficient := (-4666241768269136921960120320) }, { argument := 4642626839107627321900662784, coefficient := (-4642626839107627321900662784) }, { argument := 4666241768269136921960120320, coefficient := (-4666241768269136921960120320) }, { argument := 6889127432517303773507354624, coefficient := (-6889127432517303773507354624) }, { argument := 51854706130236667935412191232, coefficient := (-51854706130236667935412191232) }, { argument := 254114122058741770951571013632, coefficient := (-254114122058741770951571013632) }, { argument := 42815691268706287044727406592, coefficient := (-42815691268706287044727406592) }, { argument := 2116031113219959046562381824, coefficient := (-2116031113219959046562381824) }, { argument := 42749897275841959223833395200, coefficient := (-42749897275841959223833395200) }, { argument := 43471166122045507298865971200, coefficient := (-43471166122045507298865971200) }, { argument := 6914602890542549925126733824, coefficient := (-6914602890542549925126733824) }, { argument := 51854706130236667935412191232, coefficient := (-51854706130236667935412191232) }, { argument := 2116031113219959046562381824, coefficient := (-2116031113219959046562381824) }, { argument := 33471433929070229462188032000, coefficient := (-33471433929070229462188032000) }, { argument := 2171018068264724095423217664000, coefficient := (-2171018068264724095423217664000) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 23079787732425480438861004800, coefficient := (-23079787732425480438861004800) }, { argument := 309172989832282998378908876800, coefficient := (-309172989832282998378908876800) }, { argument := 559204023600225703133236428800, coefficient := (-559204023600225703133236428800) }, { argument := 2171018070282336728485199872000, coefficient := (-2171018070282336728485199872000) }, { argument := 309172989832282998378908876800, coefficient := (-309172989832282998378908876800) }, { argument := 18271498621503505347431628800, coefficient := (-18271498621503505347431628800) }, { argument := 18271498621503505347431628800, coefficient := (-18271498621503505347431628800) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 559204023600225703133236428800, coefficient := (-559204023600225703133236428800) }, { argument := 17790669710411307838288691200, coefficient := (-17790669710411307838288691200) }, { argument := 33471431911457596400205824000, coefficient := (-33471431911457596400205824000) }, { argument := 23079787732425480438861004800, coefficient := (-23079787732425480438861004800) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 2466690353395096220212396032, coefficient := (-2466690353395096220212396032) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 2748473961427927950113636352, coefficient := (-2748473961427927950113636352) }, { argument := 2744138828996653615807463424, coefficient := (-2744138828996653615807463424) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3255684455887025063935868928, coefficient := (-3255684455887025063935868928) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 1762768039025998465649868800, coefficient := (-1762768039025998465649868800) }, { argument := 309172952765856625268778598400, coefficient := (-309172952765856625268778598400) }, { argument := 309172989832282998378908876800, coefficient := (-309172989832282998378908876800) }, { argument := 1762730972599625355519590400, coefficient := (-1762730972599625355519590400) }, { argument := 1568220004683596804283957248, coefficient := (-1568220004683596804283957248) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
