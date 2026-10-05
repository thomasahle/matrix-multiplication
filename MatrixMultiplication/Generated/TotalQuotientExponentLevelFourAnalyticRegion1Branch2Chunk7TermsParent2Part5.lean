import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 300865345544583451266984088109580288
def positiveArguments : Array ℕ := #[
    13793, 135, 105, 15, 141, 1665,
    117, 105, 1665, 15, 117, 117,
    117, 117, 117, 135, 141, 1,
    19, 19, 3012274879, 285, 93, 10295587509,
    939, 753068707, 1881, 843, 285, 93,
    5324811577, 611, 94701084001, 15119, 481, 47349965551,
    247, 247, 8359, 455, 15119, 8359,
    5327129673, 481, 455, 611, 159624693, 1794403633,
    586755, 17439826433, 602095, 19175, 586755, 333645,
    602095, 9399585, 11505, 7177617835, 586755
  ]
def positiveCoefficients : Array ℕ := #[
    2185588091118496016855503413968896, 5222559540735198034730680320, 4061990753905154027012751360, 4642275147320176030871715840, 5454673298101206836274266112, 64411567669067442428345057280,
    144838984596389492163197534208, 4061990753905154027012751360, 64411567669067442428345057280, 4642275147320176030871715840, 4526218268637171630099922944, 4526218268637171630099922944,
    4526218268637171630099922944, 144838984596389492163197534208, 4526218268637171630099922944, 5222559540735198034730680320, 5454673298101206836274266112, 158456325028528675187087900672,
    3010670175542044828554670112768, 3010670175542044828554670112768, 56900263703119264435436190171136, 88203227799083344586562600960, 3597763239173136423925579776, 194478149495811926949560693293056,
    72651606055560754883142352896, 56900262739756501930028566577152, 72767662934243759283914145792, 65223965819848473233747607552, 88203227799083344586562600960, 3597763239173136423925579776,
    25145711718821059015771099758592, 378190682001683673981682450432, 894426449955490397830584983355392, 9358207726977832188099929571328, 297724579448133956113239375872, 894415561132298929968390533545984,
    305771189703488927900083683328, 305771189703488927900083683328, 5173970394193246858940889694208, 281631358937424012539550760960, 9358207726977832188099929571328, 5173970394193246858940889694208,
    25156658617675533208862387601408, 297724579448133956113239375872, 281631358937424012539550760960, 378190682001683673981682450432, 1507612600123113752510286790656, 135581305171499578190034620121088,
    11349492308607707862475556782080, 1317716029028212484658358950821888, 11646211061773922447115440619520, 370898441457768230799854796800, 11349492308607707862475556782080, 6453632881365167215917473464320,
    11646211061773922447115440619520, 181814416002597986738088821391360, 7121250075989150031357212098560, 135581367563405549863787183472640, 11349492308607707862475556782080
  ]
def positiveScales : Array ℕ := #[
    13, 7, 6, 3, 7, 10,
    6, 6, 10, 3, 6, 6,
    6, 6, 6, 7, 7, 0,
    4, 4, 31, 8, 6, 33,
    9, 29, 10, 9, 8, 6,
    32, 9, 36, 13, 8, 35,
    7, 7, 13, 8, 13, 13,
    32, 8, 8, 9, 27, 30,
    19, 34, 19, 14, 19, 18,
    19, 23, 13, 32, 19
  ]
def negativeArguments : Array ℕ := #[
    3, 1, 19, 487, 5903
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 158456325028528675187087900672, 6021340351084089657109340225536, 308672921155573859264447230509056, 1870735373286809539258759755333632
  ]
def negativeScales : Array ℕ := #[
    1, 0, 4, 8, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13751648659041397, 7076815597050830, 6714245517659862, 3906890595303263, 7139551352398793, 10701306461953989,
    6870364719426147, 6714245517659862, 10701306461953989, 3906890595303263, 6870364719426147, 6870364719426147,
    6870364719426147, 6870364719426147, 6870364719426147, 7076815597050830, 7139551352398793, 0,
    4247927513443585, 4247927513443585, 31488206280196507, 8154818109052103, 6539158811107971, 33261307107366047,
    9874981347482478, 29488206255770633, 10877284133344468, 9719388820935039, 8154818109052103, 6539158811107971,
    32310083329233239, 9255028569818729, 36462661888547389, 13884075099411883, 8909893083448106, 35462644324949125,
    7948367230958674, 7948367230958674, 13029114645469039, 8829722735013603, 13884075099411883, 13029114645469039,
    32310711253398010, 8909893083448106, 8829722735013603, 9255028569818729, 27250108604349976, 30740857300435536,
    19162398705082947, 34021666630875147, 19199631611281922, 14226938957277657, 19162398705082947, 18347954358239023,
    19199631611281922, 23164165631257135, 13489973363111439, 32740857964335861, 19162398705082947
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 0, 4247927513443586, 8927777969209522, 12527232626448224
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 1991051419243 / 1000000000000
noncomputable def negativeCeiling : ℝ := 157789226537 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2185588091118496016855503413968896, coefficient := 2185588091118496016855503413968896 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3010670175542044828554670112768, coefficient := 3010670175542044828554670112768 }, { argument := 3010670175542044828554670112768, coefficient := 3010670175542044828554670112768 }, { argument := 6021340351084089657109340225536, coefficient := (-6021340351084089657109340225536) }, { argument := 56900263703119264435436190171136, coefficient := 56900263703119264435436190171136 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 194478149495811926949560693293056, coefficient := 194478149495811926949560693293056 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 56900262739756501930028566577152, coefficient := 56900262739756501930028566577152 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 308672921155573859264447230509056, coefficient := (-308672921155573859264447230509056) }, { argument := 25145711718821059015771099758592, coefficient := 25145711718821059015771099758592 }, { argument := 378190682001683673981682450432, coefficient := 378190682001683673981682450432 }, { argument := 894426449955490397830584983355392, coefficient := 894426449955490397830584983355392 }, { argument := 9358207726977832188099929571328, coefficient := 9358207726977832188099929571328 }, { argument := 297724579448133956113239375872, coefficient := 297724579448133956113239375872 }, { argument := 894415561132298929968390533545984, coefficient := 894415561132298929968390533545984 }, { argument := 305771189703488927900083683328, coefficient := 305771189703488927900083683328 }, { argument := 305771189703488927900083683328, coefficient := 305771189703488927900083683328 }, { argument := 5173970394193246858940889694208, coefficient := 5173970394193246858940889694208 }, { argument := 281631358937424012539550760960, coefficient := 281631358937424012539550760960 }, { argument := 9358207726977832188099929571328, coefficient := 9358207726977832188099929571328 }, { argument := 5173970394193246858940889694208, coefficient := 5173970394193246858940889694208 }, { argument := 25156658617675533208862387601408, coefficient := 25156658617675533208862387601408 }, { argument := 297724579448133956113239375872, coefficient := 297724579448133956113239375872 }, { argument := 281631358937424012539550760960, coefficient := 281631358937424012539550760960 }, { argument := 378190682001683673981682450432, coefficient := 378190682001683673981682450432 }, { argument := 1870735373286809539258759755333632, coefficient := (-1870735373286809539258759755333632) }, { argument := 1507612600123113752510286790656, coefficient := 1507612600123113752510286790656 }, { argument := 135581305171499578190034620121088, coefficient := 135581305171499578190034620121088 }, { argument := 11349492308607707862475556782080, coefficient := 11349492308607707862475556782080 }, { argument := 1317716029028212484658358950821888, coefficient := 1317716029028212484658358950821888 }, { argument := 11646211061773922447115440619520, coefficient := 11646211061773922447115440619520 }, { argument := 370898441457768230799854796800, coefficient := 370898441457768230799854796800 }, { argument := 11349492308607707862475556782080, coefficient := 11349492308607707862475556782080 }, { argument := 6453632881365167215917473464320, coefficient := 6453632881365167215917473464320 }, { argument := 11646211061773922447115440619520, coefficient := 11646211061773922447115440619520 }, { argument := 181814416002597986738088821391360, coefficient := 181814416002597986738088821391360 }, { argument := 7121250075989150031357212098560, coefficient := 7121250075989150031357212098560 }, { argument := 135581367563405549863787183472640, coefficient := 135581367563405549863787183472640 }, { argument := 11349492308607707862475556782080, coefficient := 11349492308607707862475556782080 }] }

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


end Parent2

namespace Parent2

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-186640601053088944211144093663756288)
def positiveArguments : Array ℕ := #[
    19175, 11505, 19175, 295295, 333645, 159624485,
    487548379, 13430139429, 80885, 71641, 3353261, 912845,
    6715071573, 3353261, 80885, 80885, 34665, 80885,
    912845, 34665, 243772331, 71641, 30447803, 29559,
    219819845, 47613, 1475, 47613, 31801, 30689467,
    29559, 177, 535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    370898441457768230799854796800, 7121250075989150031357212098560, 370898441457768230799854796800, 11423671996899261508635527741440, 6453632881365167215917473464320, 1507610635618656878737877893120,
    2302382123767026792242593398784, 63422040299775675251699780419584, 1564543438712468492737744732160, 1385738474288186379282002477056, 64861500844908336656070503038976, 17656990236897858703754547691520,
    63422057852811892078171039727616, 64861500844908336656070503038976, 1564543438712468492737744732160, 1564543438712468492737744732160, 1341037233182115850918066913280, 1564543438712468492737744732160,
    17656990236897858703754547691520, 1341037233182115850918066913280, 2302364570730809965771334090752, 1385738474288186379282002477056, 143785684364217832146508709888, 571754212831821180402237702144,
    2076139736595201132159293194240, 920969360788981422324562526208, 28530649342905248523065753600, 920969360788981422324562526208, 615120799833037158157297647616, 144926910337934042087431340032,
    571754212831821180402237702144, 27389423369189038582143123456, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    14, 13, 14, 18, 18, 27,
    28, 33, 16, 16, 21, 19,
    32, 21, 16, 16, 15, 16,
    19, 15, 27, 16, 24, 14,
    27, 15, 10, 15, 14, 24,
    14, 7, 9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    5903, 1945, 19, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1870735373286809539258759755333632, 308197552180488273238885966807040, 6021340351084089657109340225536, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    12, 10, 4, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14226938957277657, 13489973363111439, 14226938957277657, 18171797403085196, 18347954358239023, 27250106724435545,
    28860970142301749, 33644755231484632, 16303584561412597, 16128497854854506, 21677133348531774, 19800010387492060,
    32644755630772871, 21677133348531774, 16303584561412597, 16303584561412597, 15081192140076149, 16303584561412597,
    19800010387492060, 15081192140076149, 27860959143356565, 16128497854854506, 24859834796471617, 14851309842447145,
    27711746395565294, 15539067912639561, 10526499239136525, 15539067912639561, 14956784511393203, 24871240254035500,
    14851309842447145, 7467605550082991, 9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    12527232626448224, 10925554446730883, 4247927513443586, 0
  ]

abbrev PositiveTerm := Fin 36
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 103860353489 / 1000000000000
noncomputable def negativeCeiling : ℝ := 10091551127 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 370898441457768230799854796800, coefficient := 370898441457768230799854796800 }, { argument := 7121250075989150031357212098560, coefficient := 7121250075989150031357212098560 }, { argument := 370898441457768230799854796800, coefficient := 370898441457768230799854796800 }, { argument := 11423671996899261508635527741440, coefficient := 11423671996899261508635527741440 }, { argument := 6453632881365167215917473464320, coefficient := 6453632881365167215917473464320 }, { argument := 1507610635618656878737877893120, coefficient := 1507610635618656878737877893120 }, { argument := 1870735373286809539258759755333632, coefficient := (-1870735373286809539258759755333632) }, { argument := 2302382123767026792242593398784, coefficient := 2302382123767026792242593398784 }, { argument := 63422040299775675251699780419584, coefficient := 63422040299775675251699780419584 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 1385738474288186379282002477056, coefficient := 1385738474288186379282002477056 }, { argument := 64861500844908336656070503038976, coefficient := 64861500844908336656070503038976 }, { argument := 17656990236897858703754547691520, coefficient := 17656990236897858703754547691520 }, { argument := 63422057852811892078171039727616, coefficient := 63422057852811892078171039727616 }, { argument := 64861500844908336656070503038976, coefficient := 64861500844908336656070503038976 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 1341037233182115850918066913280, coefficient := 1341037233182115850918066913280 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 17656990236897858703754547691520, coefficient := 17656990236897858703754547691520 }, { argument := 1341037233182115850918066913280, coefficient := 1341037233182115850918066913280 }, { argument := 2302364570730809965771334090752, coefficient := 2302364570730809965771334090752 }, { argument := 1385738474288186379282002477056, coefficient := 1385738474288186379282002477056 }, { argument := 308197552180488273238885966807040, coefficient := (-308197552180488273238885966807040) }, { argument := 143785684364217832146508709888, coefficient := 143785684364217832146508709888 }, { argument := 571754212831821180402237702144, coefficient := 571754212831821180402237702144 }, { argument := 2076139736595201132159293194240, coefficient := 2076139736595201132159293194240 }, { argument := 920969360788981422324562526208, coefficient := 920969360788981422324562526208 }, { argument := 28530649342905248523065753600, coefficient := 28530649342905248523065753600 }, { argument := 920969360788981422324562526208, coefficient := 920969360788981422324562526208 }, { argument := 615120799833037158157297647616, coefficient := 615120799833037158157297647616 }, { argument := 144926910337934042087431340032, coefficient := 144926910337934042087431340032 }, { argument := 571754212831821180402237702144, coefficient := 571754212831821180402237702144 }, { argument := 27389423369189038582143123456, coefficient := 27389423369189038582143123456 }, { argument := 6021340351084089657109340225536, coefficient := (-6021340351084089657109340225536) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
