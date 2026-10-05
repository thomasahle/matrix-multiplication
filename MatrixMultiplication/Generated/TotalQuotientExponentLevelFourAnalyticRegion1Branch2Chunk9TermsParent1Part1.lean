import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-23257319978702706405581447495680)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3858886695, 34764745, 271165011, 271165011, 271165011, 271165011,
    271165011, 721519005, 326788603, 7178295, 34764745, 7178295,
    55553211, 4671427397, 2335713135, 27777169, 7057, 372257,
    48685, 13967813, 1605, 3745, 48685, 48685,
    1605, 600805, 24075, 372257, 48685, 3745,
    24075, 3745, 48685, 48685, 15183, 3745,
    3423, 3745, 3423, 24075, 22005, 24075,
    22005, 55990701, 271165011, 55990701, 3745, 3423,
    3745, 3423, 55990701, 271165011, 55990701, 10696581,
    899467387, 449733585, 5348399, 48685, 44499, 48685,
    44499, 55990701, 271165011, 55990701
  ]
def negativeCoefficients : Array ℕ := #[
    35591947636053944012699074560, 2565185415211095063978311680, 2501055779830817687378853888, 2501055779830817687378853888, 2501055779830817687378853888, 80033784954586165996123324416,
    2501055779830817687378853888, 3327419107388140585243115520, 3014092862873036700174516224, 264832341501177811634749440, 2565185415211095063978311680, 264832341501177811634749440,
    512387932894893136819519488, 43086312825687093419784011776, 43086302430946807884451676160, 512398327635178672151855104, 66651480539222172546105344, 7031735919254422073259327488,
    919633648874034708915159040, 65961131950190907721250766848, 485081485120369956350853120, 35370524956693642650583040, 919633648874034708915159040, 919633648874034708915159040,
    485081485120369956350853120, 11348885578961988770458501120, 909527784600693668157849600, 7031735919254422073259327488, 919633648874034708915159040, 35370524956693642650583040,
    909527784600693668157849600, 35370524956693642650583040, 919633648874034708915159040, 919633648874034708915159040, 71699690309409823279546368, 35370524956693642650583040,
    32329320941725591132962816, 35370524956693642650583040, 32329320941725591132962816, 909527784600693668157849600, 831325395644372343419043840, 909527784600693668157849600,
    831325395644372343419043840, 258211532963648366343880704, 2501055779830817687378853888, 258211532963648366343880704, 35370524956693642650583040, 32329320941725591132962816,
    35370524956693642650583040, 32329320941725591132962816, 258211532963648366343880704, 2501055779830817687378853888, 258211532963648366343880704, 24664636521338023666778112,
    2074030586329658223623143424, 2074030085961725224251555840, 24665136889271023038365696, 919633648874034708915159040, 840562344484865369457033216, 919633648874034708915159040,
    840562344484865369457033216, 258211532963648366343880704, 2501055779830817687378853888, 258211532963648366343880704
  ]
def negativeScales : Array ℕ := #[
    31, 25, 28, 28, 28, 28,
    28, 29, 28, 22, 25, 22,
    25, 32, 31, 24, 12, 18,
    15, 23, 10, 11, 15, 15,
    10, 19, 14, 18, 15, 11,
    14, 11, 15, 15, 13, 11,
    11, 11, 11, 14, 14, 14,
    14, 25, 28, 25, 11, 11,
    11, 11, 25, 28, 25, 23,
    29, 28, 22, 15, 15, 15,
    15, 25, 28, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31845537539527922, 25051121671587514, 28014595795562400, 28014595795562400, 28014595795562400, 28014595795562400,
    28014595795562400, 29426462155281982, 28283782428377789, 22775209783236756, 25051121671587514, 22775209783236756,
    25727366966779088, 32121216299836093, 31121215951780270, 24727396234229064, 12784839295125895, 18505939452244746,
    15571189721489702, 23735602813894843, 10648357582030099, 11870750005906678, 15571189721489702, 15571189721489702,
    10648357582030099, 19196537293689111, 14555248177619742, 18505939452244746, 15571189721489702, 11870750005906678,
    14555248177619742, 11870750005906678, 15571189721489702, 15571189721489702, 13890169263387826, 11870750005906678,
    11741045577194516, 11870750005906678, 11741045577194516, 14555248177619742, 14425543751281927, 14555248177619742,
    14425543751281927, 25738683907000526, 28014595795562400, 25738683907000526, 11870750005906678, 11741045577194516,
    11870750005906678, 11741045577194516, 25738683907000526, 28014595795562400, 25738683907000526, 23350646398915330,
    29744495732307649, 28744495384251824, 22350675666365216, 15571189721489702, 15441485295150964, 15571189721489702,
    15441485295150964, 25738683907000526, 28014595795562400, 25738683907000526
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
noncomputable def negativeCeiling : ℝ := 22583101 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 35591947636053944012699074560, coefficient := (-35591947636053944012699074560) }, { argument := 2565185415211095063978311680, coefficient := (-2565185415211095063978311680) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 80033784954586165996123324416, coefficient := (-80033784954586165996123324416) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 3327419107388140585243115520, coefficient := (-3327419107388140585243115520) }, { argument := 3014092862873036700174516224, coefficient := (-3014092862873036700174516224) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 2565185415211095063978311680, coefficient := (-2565185415211095063978311680) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 512387932894893136819519488, coefficient := (-512387932894893136819519488) }, { argument := 43086312825687093419784011776, coefficient := (-43086312825687093419784011776) }, { argument := 43086302430946807884451676160, coefficient := (-43086302430946807884451676160) }, { argument := 512398327635178672151855104, coefficient := (-512398327635178672151855104) }, { argument := 66651480539222172546105344, coefficient := (-66651480539222172546105344) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 65961131950190907721250766848, coefficient := (-65961131950190907721250766848) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 485081485120369956350853120, coefficient := (-485081485120369956350853120) }, { argument := 11348885578961988770458501120, coefficient := (-11348885578961988770458501120) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 7031735919254422073259327488, coefficient := (-7031735919254422073259327488) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 71699690309409823279546368, coefficient := (-71699690309409823279546368) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 909527784600693668157849600, coefficient := (-909527784600693668157849600) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 35370524956693642650583040, coefficient := (-35370524956693642650583040) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 24664636521338023666778112, coefficient := (-24664636521338023666778112) }, { argument := 2074030586329658223623143424, coefficient := (-2074030586329658223623143424) }, { argument := 2074030085961725224251555840, coefficient := (-2074030085961725224251555840) }, { argument := 24665136889271023038365696, coefficient := (-24665136889271023038365696) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }] }

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
def constantNumerator : ℤ := (-27368190765866333306340276961280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    48685, 44499, 48685, 44499, 55990701, 271165011,
    55990701, 221867793, 18656694511, 9328345005, 110936147, 55990701,
    271165011, 55990701, 111451473, 9371869871, 4685933805, 55726867,
    6827, 370325, 44499, 13967261, 1467, 3423,
    44499, 44499, 1467, 549147, 22005, 370325,
    44499, 3423, 22005, 3423, 44499, 44499,
    14631, 15183, 14631, 15183, 14631, 34976527,
    64008259, 721519005, 27777169, 5348399, 110936147, 55726867,
    34976527, 64008259, 5348399, 139905891, 999963517, 7178295,
    67475973, 796790745, 55990701, 249990825, 796790745, 7178295,
    55990701, 55990701, 55990701, 55990701
  ]
def negativeCoefficients : Array ℕ := #[
    919633648874034708915159040, 840562344484865369457033216, 919633648874034708915159040, 840562344484865369457033216, 8262769054836747723004182528, 80033784954586165996123324416,
    8262769054836747723004182528, 511592299458720942507687936, 43019408613224846380312297472, 43019398234625461909475819520, 511602678058105413344165888, 258211532963648366343880704,
    2501055779830817687378853888, 258211532963648366343880704, 513979199767237525443182592, 43220121250611587498727440384, 43220110823589499834403389440, 513989626789325189767233536,
    64479191957102135747805184, 6995241471074805455047884800, 840562344484865369457033216, 65958525203892363677092806656, 443373544343665249823490048, 32329320941725591132962816,
    840562344484865369457033216, 840562344484865369457033216, 443373544343665249823490048, 10373093547873668240662069248, 831325395644372343419043840, 6995241471074805455047884800,
    840562344484865369457033216, 32329320941725591132962816, 831325395644372343419043840, 32329320941725591132962816, 840562344484865369457033216, 840562344484865369457033216,
    69092944010865779121586176, 71699690309409823279546368, 69092944010865779121586176, 71699690309409823279546368, 69092944010865779121586176, 322601521078096061127458816,
    590371986188358035305398272, 3327419107388140585243115520, 512398327635178672151855104, 24665136889271023038365696, 511602678058105413344165888, 513989626789325189767233536,
    322601521078096061127458816, 590371986188358035305398272, 24665136889271023038365696, 322601020710163061755871232, 2305758885143188808803549184, 264832341501177811634749440,
    311178001263883928670830592, 3674548738328842136432148480, 8262769054836747723004182528, 2305758384775255809431961600, 3674548738328842136432148480, 264832341501177811634749440,
    258211532963648366343880704, 258211532963648366343880704, 258211532963648366343880704, 8262769054836747723004182528
  ]
def negativeScales : Array ℕ := #[
    15, 15, 15, 15, 25, 28,
    25, 27, 34, 33, 26, 25,
    28, 25, 26, 33, 32, 25,
    12, 18, 15, 23, 10, 11,
    15, 15, 10, 19, 14, 18,
    15, 11, 14, 11, 15, 15,
    13, 13, 13, 13, 13, 25,
    25, 29, 24, 22, 26, 25,
    25, 25, 22, 27, 29, 22,
    26, 29, 25, 27, 29, 22,
    25, 25, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15571189721489702, 15441485295150964, 15571189721489702, 15441485295150964, 25738683907000526, 28014595795562400,
    25738683907000526, 27725125015985692, 34118974349049423, 33118974000993600, 26725154283435664, 25738683907000526,
    28014595795562400, 25738683907000526, 26731840443372805, 33125689776415401, 32125689428359578, 25731869710822789,
    12737036036709178, 18498432421080211, 15441485295150964, 23735545798283173, 10518653155673890, 11741045577194516,
    15441485295150964, 15441485295150964, 10518653155673890, 19066832867352835, 14425543751281927, 18498432421080211,
    15441485295150964, 11741045577194516, 14425543751281927, 11741045577194516, 15441485295150964, 15441485295150964,
    13836740759098915, 13890169263387826, 13836740759098915, 13890169263387826, 13836740759098915, 25059883707941457,
    25931754740233760, 29426462155281982, 24727396234229064, 22350675666365216, 26725154283435664, 25731869710822789,
    25059883707941457, 25931754740233760, 22350675666365216, 27059881470261694, 29897300223343855, 22775209783236756,
    26007870539640660, 29569625649202875, 25738683907000526, 27897299910267552, 29569625649202875, 22775209783236756,
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
noncomputable def negativeCeiling : ℝ := 141113069 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 919633648874034708915159040, coefficient := (-919633648874034708915159040) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }, { argument := 80033784954586165996123324416, coefficient := (-80033784954586165996123324416) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }, { argument := 511592299458720942507687936, coefficient := (-511592299458720942507687936) }, { argument := 43019408613224846380312297472, coefficient := (-43019408613224846380312297472) }, { argument := 43019398234625461909475819520, coefficient := (-43019398234625461909475819520) }, { argument := 511602678058105413344165888, coefficient := (-511602678058105413344165888) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 2501055779830817687378853888, coefficient := (-2501055779830817687378853888) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 513979199767237525443182592, coefficient := (-513979199767237525443182592) }, { argument := 43220121250611587498727440384, coefficient := (-43220121250611587498727440384) }, { argument := 43220110823589499834403389440, coefficient := (-43220110823589499834403389440) }, { argument := 513989626789325189767233536, coefficient := (-513989626789325189767233536) }, { argument := 64479191957102135747805184, coefficient := (-64479191957102135747805184) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 65958525203892363677092806656, coefficient := (-65958525203892363677092806656) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 443373544343665249823490048, coefficient := (-443373544343665249823490048) }, { argument := 10373093547873668240662069248, coefficient := (-10373093547873668240662069248) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 6995241471074805455047884800, coefficient := (-6995241471074805455047884800) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 831325395644372343419043840, coefficient := (-831325395644372343419043840) }, { argument := 32329320941725591132962816, coefficient := (-32329320941725591132962816) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 840562344484865369457033216, coefficient := (-840562344484865369457033216) }, { argument := 69092944010865779121586176, coefficient := (-69092944010865779121586176) }, { argument := 71699690309409823279546368, coefficient := (-71699690309409823279546368) }, { argument := 69092944010865779121586176, coefficient := (-69092944010865779121586176) }, { argument := 71699690309409823279546368, coefficient := (-71699690309409823279546368) }, { argument := 69092944010865779121586176, coefficient := (-69092944010865779121586176) }, { argument := 322601521078096061127458816, coefficient := (-322601521078096061127458816) }, { argument := 590371986188358035305398272, coefficient := (-590371986188358035305398272) }, { argument := 3327419107388140585243115520, coefficient := (-3327419107388140585243115520) }, { argument := 512398327635178672151855104, coefficient := (-512398327635178672151855104) }, { argument := 24665136889271023038365696, coefficient := (-24665136889271023038365696) }, { argument := 511602678058105413344165888, coefficient := (-511602678058105413344165888) }, { argument := 513989626789325189767233536, coefficient := (-513989626789325189767233536) }, { argument := 322601521078096061127458816, coefficient := (-322601521078096061127458816) }, { argument := 590371986188358035305398272, coefficient := (-590371986188358035305398272) }, { argument := 24665136889271023038365696, coefficient := (-24665136889271023038365696) }, { argument := 322601020710163061755871232, coefficient := (-322601020710163061755871232) }, { argument := 2305758885143188808803549184, coefficient := (-2305758885143188808803549184) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }, { argument := 2305758384775255809431961600, coefficient := (-2305758384775255809431961600) }, { argument := 3674548738328842136432148480, coefficient := (-3674548738328842136432148480) }, { argument := 264832341501177811634749440, coefficient := (-264832341501177811634749440) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 258211532963648366343880704, coefficient := (-258211532963648366343880704) }, { argument := 8262769054836747723004182528, coefficient := (-8262769054836747723004182528) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
