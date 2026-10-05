import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 9, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-58699679677990024577739615371264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    41469, 7057, 6827, 7057, 6827, 1531395,
    372257, 370325, 372257, 370325, 48685, 44499,
    48685, 44499, 139905891, 128013921, 1443034125, 55553211,
    10696581, 221867793, 111451473, 139905891, 128013921, 10696581,
    12251157, 13967813, 13967261, 13967813, 13967261, 1605,
    1467, 1605, 1467, 999963517, 10764593567, 17076780595,
    4671427397, 899467387, 18656694511, 9371869871, 999963517, 10764593567,
    899467387, 3745, 3423, 3745, 3423, 7178295,
    34764745, 7178295, 139905891, 999963517, 7178295, 67475973,
    796790745, 55990701, 249990825, 796790745, 7178295, 55990701,
    55990701, 55990701, 55990701, 55990701
  ]
def negativeCoefficients : Array ℕ := #[
    3133309050849941077868150784, 66651480539222172546105344, 64479191957102135747805184, 66651480539222172546105344, 64479191957102135747805184, 115708934720546565312447774720,
    7031735919254422073259327488, 6995241471074805455047884800, 7031735919254422073259327488, 6995241471074805455047884800, 919633648874034708915159040, 840562344484865369457033216,
    919633648874034708915159040, 840562344484865369457033216, 322601020710163061755871232, 590360009639768179379011584, 3327410149188049790042112000, 512387932894893136819519488,
    24664636521338023666778112, 511592299458720942507687936, 513979199767237525443182592, 322601020710163061755871232, 590360009639768179379011584, 24664636521338023666778112,
    115708906386347668094576492544, 65961131950190907721250766848, 65958525203892363677092806656, 65961131950190907721250766848, 65958525203892363677092806656, 485081485120369956350853120,
    443373544343665249823490048, 485081485120369956350853120, 443373544343665249823490048, 2305758885143188808803549184, 49642925646987303288012013568, 39376375154856815087782461440,
    43086312825687093419784011776, 2074030586329658223623143424, 43019408613224846380312297472, 43220121250611587498727440384, 2305758885143188808803549184, 49642925646987303288012013568,
    2074030586329658223623143424, 35370524956693642650583040, 32329320941725591132962816, 35370524956693642650583040, 32329320941725591132962816, 264832341501177811634749440,
    2565185415211095063978311680, 264832341501177811634749440, 322601020710163061755871232, 2305758885143188808803549184, 264832341501177811634749440, 311178001263883928670830592,
    3674548738328842136432148480, 8262769054836747723004182528, 2305758384775255809431961600, 3674548738328842136432148480, 264832341501177811634749440, 258211532963648366343880704,
    258211532963648366343880704, 258211532963648366343880704, 8262769054836747723004182528, 258211532963648366343880704
  ]
def negativeScales : Array ℕ := #[
    15, 12, 12, 12, 12, 20,
    18, 18, 18, 18, 15, 15,
    15, 15, 27, 26, 30, 25,
    23, 27, 26, 27, 26, 23,
    23, 23, 23, 23, 23, 10,
    10, 10, 10, 29, 33, 33,
    32, 29, 34, 33, 29, 33,
    29, 11, 11, 11, 11, 22,
    25, 22, 27, 29, 22, 26,
    29, 25, 27, 29, 22, 25,
    25, 25, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15339745637489356, 12784839295125895, 12737036036709178, 12784839295125895, 12737036036709178, 20546415021360256,
    18505939452244746, 18498432421080211, 18505939452244746, 18498432421080211, 15571189721489702, 15441485295150964,
    15571189721489702, 15441485295150964, 27059881470261694, 26931725472780020, 30426458271200107, 25727366966779088,
    23350646398915330, 27725125015985692, 26731840443372805, 27059881470261694, 26931725472780020, 23350646398915330,
    23546414668080595, 23735602813894843, 23735545798283173, 23735602813894843, 23735545798283173, 10648357582030099,
    10518653155673890, 10648357582030099, 10518653155673890, 29897300223343855, 33325574798342279, 33991316985568338,
    32121216299836093, 29744495732307649, 34118974349049423, 33125689776415401, 29897300223343855, 33325574798342279,
    29744495732307649, 11870750005906678, 11741045577194516, 11870750005906678, 11741045577194516, 22775209783236756,
    25051121671587514, 22775209783236756, 27059881470261694, 29897300223343855, 22775209783236756, 26007870539640660,
    29569625649202875, 25738683907000526, 27897299910267552, 29569625649202875, 22775209783236756, 25738683907000526,
    25738683907000526, 25738683907000526, 25738683907000526, 25738683907000526
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
noncomputable def negativeCeiling : ℝ := 33557871 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3133309050849941077868150784, coefficient := (-3133309050849941077868150784) }, { argument := 66651480539222172546105344, coefficient := (-66651480539222172546105344) }, { argument := 64479191957102135747805184, coefficient := (-64479191957102135747805184) }, { argument := 66651480539222172546105344, coefficient := (-66651480539222172546105344) }, { argument := 64479191957102135747805184, coefficient := (-64479191957102135747805184) }, { argument := 115708934720546565312447774720, coefficient := (-115708934720546565312447774720) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 322601020710163061755871232, coefficient := (-322601020710163061755871232) }, { argument := 590360009639768179379011584, coefficient := (-590360009639768179379011584) }, { argument := 3327410149188049790042112000, coefficient := (-3327410149188049790042112000) }, { argument := 512387932894893136819519488, coefficient := (-512387932894893136819519488) }, { argument := 24664636521338023666778112, coefficient := (-24664636521338023666778112) }, { argument := 511592299458720942507687936, coefficient := (-511592299458720942507687936) }, { argument := 513979199767237525443182592, coefficient := (-513979199767237525443182592) }, { argument := 322601020710163061755871232, coefficient := (-322601020710163061755871232) }, { argument := 590360009639768179379011584, coefficient := (-590360009639768179379011584) }, { argument := 24664636521338023666778112, coefficient := (-24664636521338023666778112) }, { argument := 115708906386347668094576492544, coefficient := (-115708906386347668094576492544) }, { argument := 65961131950190907721250766848, coefficient := (-65961131950190907721250766848) }, { argument := 65958525203892363677092806656, coefficient := (-65958525203892363677092806656) }, { argument := 65961131950190907721250766848, coefficient := (-65961131950190907721250766848) }, { argument := 65958525203892363677092806656, coefficient := (-65958525203892363677092806656) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 2305758885143188808803549184, coefficient := (-2305758885143188808803549184) }, { argument := 49642925646987303288012013568, coefficient := (-49642925646987303288012013568) }, { argument := 39376375154856815087782461440, coefficient := (-39376375154856815087782461440) }, { argument := 43086312825687093419784011776, coefficient := (-43086312825687093419784011776) }, { argument := 2074030586329658223623143424, coefficient := (-2074030586329658223623143424) }, { argument := 43019408613224846380312297472, coefficient := (-43019408613224846380312297472) }, { argument := 43220121250611587498727440384, coefficient := (-43220121250611587498727440384) }, { argument := 2305758885143188808803549184, coefficient := (-2305758885143188808803549184) }, { argument := 49642925646987303288012013568, coefficient := (-49642925646987303288012013568) }, { argument := 2074030586329658223623143424, coefficient := (-2074030586329658223623143424) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 2565185415211095063978311680, coefficient := (-2565185415211095063978311680) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 322601020710163061755871232, coefficient := (-322601020710163061755871232) }, { argument := 2305758885143188808803549184, coefficient := (-2305758885143188808803549184) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }, { argument := 2305758384775255809431961600, coefficient := (-2305758384775255809431961600) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }] }

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
def constantNumerator : ℤ := (-55681392572654278923789776453632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    34976527, 67475973, 48685, 44499, 48685, 44499,
    48685, 44499, 48685, 44499, 67475973, 326788603,
    67475973, 1605, 1467, 1605, 1467, 600805,
    549147, 600805, 549147, 796790745, 3858886695, 796790745,
    24075, 22005, 24075, 22005, 55990701, 271165011,
    55990701, 128013921, 10764593567, 5382295485, 64008259, 331755,
    372257, 370325, 372257, 370325, 249990825, 5382295485,
    8538388355, 2335713135, 449733585, 9328345005, 4685933805, 249990825,
    5382295485, 449733585, 48685, 44499, 48685, 44499,
    796790745, 3858886695, 796790745, 1443034125, 17076780595, 34764745,
    326788603, 3858886695, 271165011, 8538388355
  ]
def negativeCoefficients : Array ℕ := #[
    322601521078096061127458816, 311178001263883928670830592, 919633648874034708915159040, 840562344484865369457033216, 919633648874034708915159040, 840562344484865369457033216,
    919633648874034708915159040, 840562344484865369457033216, 919633648874034708915159040, 840562344484865369457033216, 311178001263883928670830592, 3014092862873036700174516224,
    311178001263883928670830592, 485081485120369956350853120, 443373544343665249823490048, 485081485120369956350853120, 443373544343665249823490048, 11348885578961988770458501120,
    10373093547873668240662069248, 11348885578961988770458501120, 10373093547873668240662069248, 3674548738328842136432148480, 35591947636053944012699074560, 3674548738328842136432148480,
    909527784600693668157849600, 831325395644372343419043840, 909527784600693668157849600, 831325395644372343419043840, 8262769054836747723004182528, 80033784954586165996123324416,
    8262769054836747723004182528, 590360009639768179379011584, 49642925646987303288012013568, 49642913670438713432085626880, 590371986188358035305398272, 3133337385048838295739432960,
    7031735919254422073259327488, 6995241471074805455047884800, 7031735919254422073259327488, 6995241471074805455047884800, 2305758384775255809431961600, 49642913670438713432085626880,
    39376366196656724292581457920, 43086302430946807884451676160, 2074030085961725224251555840, 43019398234625461909475819520, 43220110823589499834403389440, 2305758384775255809431961600,
    49642913670438713432085626880, 2074030085961725224251555840, 919633648874034708915159040, 840562344484865369457033216, 919633648874034708915159040, 840562344484865369457033216,
    3674548738328842136432148480, 35591947636053944012699074560, 3674548738328842136432148480, 3327410149188049790042112000, 39376375154856815087782461440, 2565185415211095063978311680,
    3014092862873036700174516224, 35591947636053944012699074560, 80033784954586165996123324416, 39376366196656724292581457920
  ]
def negativeScales : Array ℕ := #[
    25, 26, 15, 15, 15, 15,
    15, 15, 15, 15, 26, 28,
    26, 10, 10, 10, 10, 19,
    19, 19, 19, 29, 31, 29,
    14, 14, 14, 14, 25, 28,
    25, 26, 33, 32, 25, 18,
    18, 18, 18, 18, 27, 32,
    32, 31, 28, 33, 32, 27,
    32, 28, 15, 15, 15, 15,
    29, 31, 29, 30, 33, 25,
    28, 31, 28, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25059883707941457, 26007870539640660, 15571189721489702, 15441485295150964, 15571189721489702, 15441485295150964,
    15571189721489702, 15441485295150964, 15571189721489702, 15441485295150964, 26007870539640660, 28283782428377789,
    26007870539640660, 10648357582030099, 10518653155673890, 10648357582030099, 10518653155673890, 19196537293689111,
    19066832867352835, 19196537293689111, 19066832867352835, 29569625649202875, 31845537539527922, 29569625649202875,
    14555248177619742, 14425543751281927, 14555248177619742, 14425543751281927, 25738683907000526, 28014595795562400,
    25738683907000526, 26931725472780020, 33325574798342279, 32325574450286456, 25931754740233760, 18339758683576654,
    18505939452244746, 18498432421080211, 18505939452244746, 18498432421080211, 27897299910267552, 32325574450286456,
    32991316657352332, 31121215951780270, 28744495384251824, 33118974000993600, 32125689428359578, 27897299910267552,
    32325574450286456, 28744495384251824, 15571189721489702, 15441485295150964, 15571189721489702, 15441485295150964,
    29569625649202875, 31845537539527922, 29569625649202875, 30426458271200107, 33991316985568338, 25051121671587514,
    28283782428377789, 31845537539527922, 28014595795562400, 32991316657352332
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
noncomputable def negativeCeiling : ℝ := 154032491 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 322601521078096061127458816, coefficient := (-322601521078096061127458816) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 3014092862873036700174516224, coefficient := (-3014092862873036700174516224) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 11348885578961988770458501120, coefficient := (-11348885578961988770458501120) }, { argument := 10373093547873668240662069248, coefficient := (-10373093547873668240662069248) }, { argument := 11348885578961988770458501120, coefficient := (-11348885578961988770458501120) }, { argument := 10373093547873668240662069248, coefficient := (-10373093547873668240662069248) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 35591947636053944012699074560, coefficient := (-35591947636053944012699074560) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }, { argument := 80033784954586165996123324416, coefficient := (-80033784954586165996123324416) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }, { argument := 590360009639768179379011584, coefficient := (-590360009639768179379011584) }, { argument := 49642925646987303288012013568, coefficient := (-49642925646987303288012013568) }, { argument := 49642913670438713432085626880, coefficient := (-49642913670438713432085626880) }, { argument := 590371986188358035305398272, coefficient := (-590371986188358035305398272) }, { argument := 3133337385048838295739432960, coefficient := (-3133337385048838295739432960) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 2305758384775255809431961600, coefficient := (-2305758384775255809431961600) }, { argument := 49642913670438713432085626880, coefficient := (-49642913670438713432085626880) }, { argument := 39376366196656724292581457920, coefficient := (-39376366196656724292581457920) }, { argument := 43086302430946807884451676160, coefficient := (-43086302430946807884451676160) }, { argument := 2074030085961725224251555840, coefficient := (-2074030085961725224251555840) }, { argument := 43019398234625461909475819520, coefficient := (-43019398234625461909475819520) }, { argument := 43220110823589499834403389440, coefficient := (-43220110823589499834403389440) }, { argument := 2305758384775255809431961600, coefficient := (-2305758384775255809431961600) }, { argument := 49642913670438713432085626880, coefficient := (-49642913670438713432085626880) }, { argument := 2074030085961725224251555840, coefficient := (-2074030085961725224251555840) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 35591947636053944012699074560, coefficient := (-35591947636053944012699074560) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 3327410149188049790042112000, coefficient := (-3327410149188049790042112000) }, { argument := 39376375154856815087782461440, coefficient := (-39376375154856815087782461440) }, { argument := 2565185415211095063978311680, coefficient := (-2565185415211095063978311680) }, { argument := 3014092862873036700174516224, coefficient := (-3014092862873036700174516224) }, { argument := 35591947636053944012699074560, coefficient := (-35591947636053944012699074560) }, { argument := 80033784954586165996123324416, coefficient := (-80033784954586165996123324416) }, { argument := 39376366196656724292581457920, coefficient := (-39376366196656724292581457920) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
