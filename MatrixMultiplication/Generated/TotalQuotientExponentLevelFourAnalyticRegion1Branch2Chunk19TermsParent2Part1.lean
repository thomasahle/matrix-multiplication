import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 19, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 125414244057264338723816286776721408
def positiveArguments : Array ℕ := #[
    8351, 1235, 5187, 22477, 741, 741,
    1729, 22477, 22477, 741, 277381, 11115,
    5187, 22477, 1729, 11115, 1729, 22477,
    22477, 741, 257, 4883
  ]
def positiveCoefficients : Array ℕ := #[
    1323268770313242966487371058511872, 23888374195585072492194037760, 401324686485829217868859834368, 869536820719296638715862974464, 28666049034702086990632845312, 458656784555233391850125524992,
    33443723873819101489071652864, 869536820719296638715862974464, 869536820719296638715862974464, 458656784555233391850125524992, 10730657688656814563493561761792, 859981471041062609718985359360,
    401324686485829217868859834368, 869536820719296638715862974464, 33443723873819101489071652864, 859981471041062609718985359360, 33443723873819101489071652864, 869536820719296638715862974464,
    869536820719296638715862974464, 28666049034702086990632845312, 318150590096342730649074925568, 377803825739406992645776474112
  ]
def positiveScales : Array ℕ := #[
    13, 10, 12, 14, 9, 9,
    10, 14, 14, 9, 18, 13,
    12, 14, 10, 13, 10, 14,
    14, 9, 8, 12
  ]
def negativeArguments : Array ℕ := #[
    9, 14515820559, 24602355697, 14515820559, 771, 771,
    22539, 9, 9, 22473, 4778944623, 8099665809,
    4778944623, 299, 299, 11965, 771, 771,
    278709, 5559, 871323463927323, 126069771, 871323254479333, 126069771,
    241079825, 22539, 268480035, 455037405, 268480035, 9,
    9, 433, 9, 9, 5559, 433,
    19, 19, 5635, 22473, 2926891, 247
  ]
def negativeCoefficients : Array ℕ := #[
    89131682828547379792736944128, 133884813435882260371102236672, 453833359152929175123213156352, 133884813435882260371102236672, 3817807081156112767788899106816, 3817807081156112767788899106816,
    435967664772706031499240013824, 89131682828547379792736944128, 89131682828547379792736944128, 434691039107192983090750291968, 88155968402911377359024160768, 298824924522397262041671794688,
    88155968402911377359024160768, 740288143492657404389676285952, 740288143492657404389676285952, 231436758907024609205750333440, 3817807081156112767788899106816, 3817807081156112767788899106816,
    5391016100143578922450937708544, 430106792399214309260264472576, 1962046013731130837999869231104, 1162788400534085146370899968, 1962045542096185979250182979584, 1162788400534085146370899968,
    2276934570552159131859838566400, 435967664772706031499240013824, 4952582494545582997697986560, 16787917107999846182116392960, 4952582494545582997697986560, 89131682828547379792736944128,
    89131682828547379792736944128, 16750876156580301844728774656, 89131682828547379792736944128, 89131682828547379792736944128, 430106792399214309260264472576, 16750876156580301844728774656,
    94083442985688900892333441024, 94083442985688900892333441024, 435987007585819865566035312640, 434691039107192983090750291968, 27643703914825637498319798272, 19569356141023291385605355732992
  ]
def negativeScales : Array ℕ := #[
    3, 33, 34, 33, 9, 9,
    14, 3, 3, 14, 32, 32,
    32, 8, 8, 13, 9, 9,
    18, 12, 49, 26, 49, 26,
    27, 14, 28, 28, 28, 3,
    3, 8, 3, 3, 12, 8,
    4, 4, 12, 14, 21, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13027733249752832, 10270295326472039, 12340684654363437, 14456161871783369, 9533329732305783, 9533329732305783,
    10755722153626485, 14456161871783369, 14456161871783369, 9533329732305783, 18081509443985278, 13440220327914349,
    12340684654363437, 14456161871783369, 10755722153626485, 13440220327914349, 10755722153626485, 14456161871783369,
    14456161871783369, 9533329732305783, 8005624549193878, 12253552062637463
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 33756907076934159, 34518077410360067, 33756907076934159, 9590587049919383, 9590587049919383,
    14460135887648612, 3169925001442313, 3169925001442313, 14455905107370583, 32154044904143112, 32915215243552797,
    32154044904143112, 8224001674198106, 8224001674198106, 13546532776427058, 9590587049919383, 9590587049919383,
    18088400064771335, 12440609666748455, 49630201722545172, 26909647152112851, 49630201375751329, 26909647152112851,
    27844935683323046, 14460135887648612, 28000239568064076, 28761409902038808, 28000239568064076, 3169925001442313,
    3169925001442313, 8758223214995597, 3169925001442313, 3169925001442313, 12440609666748455, 8758223214995597,
    4247927513443586, 4247927513443586, 12460199895059652, 14455905107370583, 21480937588836762, 7948367241724988
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 21136424501 / 100000000000
noncomputable def negativeCeiling : ℝ := 9136034437 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 133884813435882260371102236672, coefficient := (-133884813435882260371102236672) }, { argument := 453833359152929175123213156352, coefficient := (-453833359152929175123213156352) }, { argument := 133884813435882260371102236672, coefficient := (-133884813435882260371102236672) }, { argument := 3817807081156112767788899106816, coefficient := (-3817807081156112767788899106816) }, { argument := 3817807081156112767788899106816, coefficient := (-3817807081156112767788899106816) }, { argument := 435967664772706031499240013824, coefficient := (-435967664772706031499240013824) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 434691039107192983090750291968, coefficient := (-434691039107192983090750291968) }, { argument := 88155968402911377359024160768, coefficient := (-88155968402911377359024160768) }, { argument := 298824924522397262041671794688, coefficient := (-298824924522397262041671794688) }, { argument := 88155968402911377359024160768, coefficient := (-88155968402911377359024160768) }, { argument := 740288143492657404389676285952, coefficient := (-740288143492657404389676285952) }, { argument := 740288143492657404389676285952, coefficient := (-740288143492657404389676285952) }, { argument := 231436758907024609205750333440, coefficient := (-231436758907024609205750333440) }, { argument := 3817807081156112767788899106816, coefficient := (-3817807081156112767788899106816) }, { argument := 3817807081156112767788899106816, coefficient := (-3817807081156112767788899106816) }, { argument := 5391016100143578922450937708544, coefficient := (-5391016100143578922450937708544) }, { argument := 430106792399214309260264472576, coefficient := (-430106792399214309260264472576) }, { argument := 1962046013731130837999869231104, coefficient := (-1962046013731130837999869231104) }, { argument := 1162788400534085146370899968, coefficient := (-1162788400534085146370899968) }, { argument := 1962045542096185979250182979584, coefficient := (-1962045542096185979250182979584) }, { argument := 1162788400534085146370899968, coefficient := (-1162788400534085146370899968) }, { argument := 2276934570552159131859838566400, coefficient := (-2276934570552159131859838566400) }, { argument := 435967664772706031499240013824, coefficient := (-435967664772706031499240013824) }, { argument := 4952582494545582997697986560, coefficient := (-4952582494545582997697986560) }, { argument := 16787917107999846182116392960, coefficient := (-16787917107999846182116392960) }, { argument := 4952582494545582997697986560, coefficient := (-4952582494545582997697986560) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 16750876156580301844728774656, coefficient := (-16750876156580301844728774656) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 89131682828547379792736944128, coefficient := (-89131682828547379792736944128) }, { argument := 430106792399214309260264472576, coefficient := (-430106792399214309260264472576) }, { argument := 16750876156580301844728774656, coefficient := (-16750876156580301844728774656) }, { argument := 94083442985688900892333441024, coefficient := (-94083442985688900892333441024) }, { argument := 94083442985688900892333441024, coefficient := (-94083442985688900892333441024) }, { argument := 435987007585819865566035312640, coefficient := (-435987007585819865566035312640) }, { argument := 434691039107192983090750291968, coefficient := (-434691039107192983090750291968) }, { argument := 27643703914825637498319798272, coefficient := (-27643703914825637498319798272) }, { argument := 1323268770313242966487371058511872, coefficient := 1323268770313242966487371058511872 }, { argument := 23888374195585072492194037760, coefficient := 23888374195585072492194037760 }, { argument := 401324686485829217868859834368, coefficient := 401324686485829217868859834368 }, { argument := 869536820719296638715862974464, coefficient := 869536820719296638715862974464 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 458656784555233391850125524992, coefficient := 458656784555233391850125524992 }, { argument := 33443723873819101489071652864, coefficient := 33443723873819101489071652864 }, { argument := 869536820719296638715862974464, coefficient := 869536820719296638715862974464 }, { argument := 869536820719296638715862974464, coefficient := 869536820719296638715862974464 }, { argument := 458656784555233391850125524992, coefficient := 458656784555233391850125524992 }, { argument := 10730657688656814563493561761792, coefficient := 10730657688656814563493561761792 }, { argument := 859981471041062609718985359360, coefficient := 859981471041062609718985359360 }, { argument := 401324686485829217868859834368, coefficient := 401324686485829217868859834368 }, { argument := 869536820719296638715862974464, coefficient := 869536820719296638715862974464 }, { argument := 33443723873819101489071652864, coefficient := 33443723873819101489071652864 }, { argument := 859981471041062609718985359360, coefficient := 859981471041062609718985359360 }, { argument := 33443723873819101489071652864, coefficient := 33443723873819101489071652864 }, { argument := 869536820719296638715862974464, coefficient := 869536820719296638715862974464 }, { argument := 869536820719296638715862974464, coefficient := 869536820719296638715862974464 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 19569356141023291385605355732992, coefficient := (-19569356141023291385605355732992) }, { argument := 318150590096342730649074925568, coefficient := 318150590096342730649074925568 }, { argument := 377803825739406992645776474112, coefficient := 377803825739406992645776474112 }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-53224430693632758098476608929136640)
def positiveArguments : Array ℕ := #[
    7453, 76843, 2313, 7453, 2313, 2313,
    198147, 2313, 76843, 198147, 257, 2313,
    2313, 4883, 1425, 25365, 1425, 45125,
    77045, 1425, 77045, 77045, 25365, 1425,
    483, 541, 483, 541, 1, 877,
    32505859785, 32505852215, 12033311087, 43189043157, 3008327599, 49723985,
    7396988603, 59173902083, 1593174277, 2822431, 438440625, 153,
    4403677535, 157, 5, 153, 87, 157,
    2451, 3, 219220315, 153, 5, 3,
    5, 77
  ]
def positiveCoefficients : Array ℕ := #[
    288323972274810599650724151296, 2972719576212702389502293835776, 357919413858385571980209291264, 288323972274810599650724151296, 357919413858385571980209291264, 357919413858385571980209291264,
    15330881560267515333152297975808, 357919413858385571980209291264, 2972719576212702389502293835776, 15330881560267515333152297975808, 318150590096342730649074925568, 357919413858385571980209291264,
    357919413858385571980209291264, 377803825739406992645776474112, 55127017374427090366601625600, 981260909264802208525508935680, 55127017374427090366601625600, 872844441761762264137859072000,
    1490267036355345676243797278720, 55127017374427090366601625600, 1490267036355345676243797278720, 1490267036355345676243797278720, 981260909264802208525508935680, 55127017374427090366601625600,
    149481259743709668194069250048, 167431390313347682180106551296, 149481259743709668194069250048, 167431390313347682180106551296, 158456325028528675187087900672, 69483098525009824069538044444672,
    307009165491088583498197075230720, 307009093994460032851768539873280, 227302819820769989302898244190208, 815817959327309633358380125913088, 227302806768149030651198873534464, 7514076165078815857956534353920,
    279450328423807683042902492053504, 279440851857369482728196714528768, 7523552807074879898576635297792, 26657107109224511220274429952, 4140954624456838082042265600000, 5918900812833224439361437696,
    41591558385300037921946699038720, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696, 3365649481807127622381993984, 6073643317743896973723828224,
    94818469884014595430554796032, 3713820117856140824697372672, 4140954671680502910738717736960, 5918900812833224439361437696, 193428131138340667952988160, 3713820117856140824697372672,
    193428131138340667952988160, 5957586439060892572952035328
  ]
def positiveScales : Array ℕ := #[
    12, 16, 11, 12, 11, 11,
    17, 11, 16, 17, 8, 11,
    11, 12, 10, 14, 10, 15,
    16, 10, 16, 16, 14, 10,
    8, 9, 8, 9, 0, 9,
    34, 34, 33, 35, 31, 25,
    32, 35, 30, 21, 28, 7,
    32, 7, 2, 7, 6, 7,
    11, 1, 27, 7, 2, 1,
    2, 6
  ]
def negativeArguments : Array ℕ := #[
    257, 95, 1, 1, 877, 3875,
    16035, 1811
  ]
def negativeCoefficients : Array ℕ := #[
    40723275532331869523081590472704, 7526675438855112071386675281920, 633825300114114700748351602688, 158456325028528675187087900672, 69483098525009824069538044444672, 614018259485548616349965615104000,
    1270423585916228653312477243637760, 573928809253330861527632376233984
  ]
def negativeScales : Array ℕ := #[
    8, 6, 0, 0, 9, 11,
    13, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12863605544182823, 16229626223391982, 11175549550636190, 12863605544182823, 11175549550636190, 11175549550636190,
    17596211599108595, 11175549550636190, 16229626223391982, 17596211599108595, 8005624549193878, 11175549550636190,
    11175549550636190, 12253552062637463, 10476746203939458, 14630551540017700, 10476746203939458, 15461639311549253,
    16233413712548220, 10476746203939458, 16233413712548220, 16233413712548220, 14630551540017700, 10476746203939458,
    8915879378478017, 9079484783826815, 8915879378478017, 9079484783826815, 0, 9776433032420156,
    34919980762652764, 34919980426676336, 33486314618114948, 35329946303206414, 31486314535269728, 25567438586292800,
    32784290906894691, 35784241982181329, 30569256945589625, 21428506881172896, 28707806240719123, 7257387842692651,
    32036061683540435, 7294620748891626, 2321928094887362, 7257387842692651, 6442943495848725, 7294620748891626,
    11259154768866839, 1584962500720924, 27707806257171693, 7257387842692651, 2321928094887362, 1584962500720924,
    2321928094887362, 6266786540694901
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8005624549193879, 6569855608333349, 0, 0, 9776433032841194, 11919980601271074,
    13968936747630685, 10822570831966667
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 527588792681 / 500000000000
noncomputable def negativeCeiling : ℝ := 77835733907 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 288323972274810599650724151296, coefficient := 288323972274810599650724151296 }, { argument := 2972719576212702389502293835776, coefficient := 2972719576212702389502293835776 }, { argument := 357919413858385571980209291264, coefficient := 357919413858385571980209291264 }, { argument := 288323972274810599650724151296, coefficient := 288323972274810599650724151296 }, { argument := 357919413858385571980209291264, coefficient := 357919413858385571980209291264 }, { argument := 357919413858385571980209291264, coefficient := 357919413858385571980209291264 }, { argument := 15330881560267515333152297975808, coefficient := 15330881560267515333152297975808 }, { argument := 357919413858385571980209291264, coefficient := 357919413858385571980209291264 }, { argument := 2972719576212702389502293835776, coefficient := 2972719576212702389502293835776 }, { argument := 15330881560267515333152297975808, coefficient := 15330881560267515333152297975808 }, { argument := 318150590096342730649074925568, coefficient := 318150590096342730649074925568 }, { argument := 357919413858385571980209291264, coefficient := 357919413858385571980209291264 }, { argument := 357919413858385571980209291264, coefficient := 357919413858385571980209291264 }, { argument := 377803825739406992645776474112, coefficient := 377803825739406992645776474112 }, { argument := 40723275532331869523081590472704, coefficient := (-40723275532331869523081590472704) }, { argument := 55127017374427090366601625600, coefficient := 55127017374427090366601625600 }, { argument := 981260909264802208525508935680, coefficient := 981260909264802208525508935680 }, { argument := 55127017374427090366601625600, coefficient := 55127017374427090366601625600 }, { argument := 872844441761762264137859072000, coefficient := 872844441761762264137859072000 }, { argument := 1490267036355345676243797278720, coefficient := 1490267036355345676243797278720 }, { argument := 55127017374427090366601625600, coefficient := 55127017374427090366601625600 }, { argument := 1490267036355345676243797278720, coefficient := 1490267036355345676243797278720 }, { argument := 1490267036355345676243797278720, coefficient := 1490267036355345676243797278720 }, { argument := 981260909264802208525508935680, coefficient := 981260909264802208525508935680 }, { argument := 55127017374427090366601625600, coefficient := 55127017374427090366601625600 }, { argument := 7526675438855112071386675281920, coefficient := (-7526675438855112071386675281920) }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 69483098525009824069538044444672, coefficient := 69483098525009824069538044444672 }, { argument := 69483098525009824069538044444672, coefficient := (-69483098525009824069538044444672) }, { argument := 307009165491088583498197075230720, coefficient := 307009165491088583498197075230720 }, { argument := 307009093994460032851768539873280, coefficient := 307009093994460032851768539873280 }, { argument := 614018259485548616349965615104000, coefficient := (-614018259485548616349965615104000) }, { argument := 227302819820769989302898244190208, coefficient := 227302819820769989302898244190208 }, { argument := 815817959327309633358380125913088, coefficient := 815817959327309633358380125913088 }, { argument := 227302806768149030651198873534464, coefficient := 227302806768149030651198873534464 }, { argument := 1270423585916228653312477243637760, coefficient := (-1270423585916228653312477243637760) }, { argument := 7514076165078815857956534353920, coefficient := 7514076165078815857956534353920 }, { argument := 279450328423807683042902492053504, coefficient := 279450328423807683042902492053504 }, { argument := 279440851857369482728196714528768, coefficient := 279440851857369482728196714528768 }, { argument := 7523552807074879898576635297792, coefficient := 7523552807074879898576635297792 }, { argument := 573928809253330861527632376233984, coefficient := (-573928809253330861527632376233984) }, { argument := 26657107109224511220274429952, coefficient := 26657107109224511220274429952 }, { argument := 4140954624456838082042265600000, coefficient := 4140954624456838082042265600000 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 41591558385300037921946699038720, coefficient := 41591558385300037921946699038720 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4140954671680502910738717736960, coefficient := 4140954671680502910738717736960 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }] }

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


end Parent2

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4954915802428595769117607693647872)
def positiveArguments : Array ℕ := #[
    87, 2822171
  ]
def positiveCoefficients : Array ℕ := #[
    3365649481807127622381993984, 26654651478653419004763308032
  ]
def positiveScales : Array ℕ := #[
    6, 21
  ]
def negativeArguments : Array ℕ := #[
    79
  ]
def negativeCoefficients : Array ℕ := #[
    50072198709015061359119776612352
  ]
def negativeScales : Array ℕ := #[
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6442943495848725, 21428373975182040
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6303780748177104
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 3568089 / 500000000000
noncomputable def negativeCeiling : ℝ := 3799428399 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 26654651478653419004763308032, coefficient := 26654651478653419004763308032 }, { argument := 50072198709015061359119776612352, coefficient := (-50072198709015061359119776612352) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
