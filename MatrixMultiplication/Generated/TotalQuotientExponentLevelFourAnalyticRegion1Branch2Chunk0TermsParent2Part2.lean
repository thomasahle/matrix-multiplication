import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 276289262516115249010750848499712
def positiveArguments : Array ℕ := #[
    5, 3, 1, 1, 1, 1
  ]
def positiveCoefficients : Array ℕ := #[
    3169126500570573503741758013440, 475368975085586025561263702016, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168
  ]
def positiveScales : Array ℕ := #[
    2, 1, 0, 0, 0, 0
  ]
def negativeArguments : Array ℕ := #[
    21534885, 3422041, 44505429, 44505429, 215541419, 44505429,
    347210535, 29071637721, 14535824121, 173600007, 46028437, 3842247295,
    153, 37809238885, 157, 5, 153, 87,
    157, 2451, 3, 1921124985, 153, 5,
    3, 5, 77, 87, 46028437, 2079105,
    174081663, 87040863, 1039521, 43152747, 3540736385, 153,
    34559252635, 157, 5, 153, 87, 157,
    2451, 3, 1770369415, 153, 5, 3,
    5, 77, 87, 43152747, 699099, 12233361,
    12233367, 699093, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    198624256125883358726062080, 252502058146964430886273024, 205245064663412804016930816, 205245064663412804016930816, 1988018696788598674583191552, 205245064663412804016930816,
    400306492427548303200092160, 33517316302680487822356381696, 33517328432567637790993416192, 400294362540398334563057664, 106134349681482931606913024, 8859619064845975664029859840,
    739862601604153054920179712, 87182169166667810644447723520, 759205414717987121715478528, 24178516392292583494123520, 739862601604153054920179712, 420706185225890952797749248,
    759205414717987121715478528, 11852308735501824428819349504, 464227514732017603087171584, 8859625232976025310661181440, 739862601604153054920179712, 24178516392292583494123520,
    464227514732017603087171584, 24178516392292583494123520, 744698304882611571619004416, 420706185225890952797749248, 106134349681482931606913024, 19176358918684948656291840,
    1605619942643376662148808704, 1605620523715814983999684608, 19175777846246626805415936, 99503459998317204046086144, 8164382240820816416100843520, 739862601604153054920179712,
    79688211092064681988739563520, 759205414717987121715478528, 24178516392292583494123520, 739862601604153054920179712, 420706185225890952797749248, 759205414717987121715478528,
    11852308735501824428819349504, 464227514732017603087171584, 8164387878606973943582556160, 739862601604153054920179712, 24178516392292583494123520, 464227514732017603087171584,
    24178516392292583494123520, 744698304882611571619004416, 420706185225890952797749248, 99503459998317204046086144, 3301401685807686099249659904, 115540827918489371682130624512,
    115540884586887166117873188864, 3301373351608788881378377728, 475368975085586025561263702016, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    24, 21, 25, 25, 27, 25,
    28, 34, 33, 27, 25, 31,
    7, 35, 7, 2, 7, 6,
    7, 11, 1, 30, 7, 2,
    1, 2, 6, 6, 25, 20,
    27, 26, 19, 25, 31, 7,
    35, 7, 2, 7, 6, 7,
    11, 1, 30, 7, 2, 1,
    2, 6, 6, 25, 19, 23,
    23, 19, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 1584962500720924, 0, 0, 0, 0
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24360172283571542, 21706425614490557, 25407477998349906, 25407477998349906, 27683389887135756, 25407477998349906,
    28371235481540493, 34758893295660562, 33758893817770531, 27371191765054480, 25456022117622099, 31839303232231434,
    7257387842692652, 35138019756466739, 7294620748891628, 2321928094887363, 7257387842692652, 6442943495848765,
    7294620748891628, 11259154768866840, 1584962500724866, 30839304236645700, 7257387842692652, 2321928094887363,
    1584962500724866, 2321928094887363, 6266786540694902, 6442943495848765, 25456022117622099, 20987531208446993,
    27375189002913723, 26375189525023689, 19987487491947284, 25362949065032558, 31721402290262447, 7257387842692652,
    35008352967548682, 7294620748891628, 2321928094887363, 7257387842692652, 6442943495848765, 7294620748891628,
    11259154768866840, 1584962500724866, 30721403286492548, 7257387842692652, 2321928094887363, 1584962500724866,
    2321928094887363, 6266786540694902, 6442943495848765, 25362949065032558, 19415137245768091, 23544317489327099,
    23544318196914173, 19415124863820197, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 19528751 / 200000000000
noncomputable def negativeCeiling : ℝ := 193588203 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }, { argument := 252502058146964430886273024, coefficient := (-252502058146964430886273024) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 1988018696788598674583191552, coefficient := (-1988018696788598674583191552) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 400306492427548303200092160, coefficient := (-400306492427548303200092160) }, { argument := 33517316302680487822356381696, coefficient := (-33517316302680487822356381696) }, { argument := 33517328432567637790993416192, coefficient := (-33517328432567637790993416192) }, { argument := 400294362540398334563057664, coefficient := (-400294362540398334563057664) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 8859619064845975664029859840, coefficient := (-8859619064845975664029859840) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 87182169166667810644447723520, coefficient := (-87182169166667810644447723520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 8859625232976025310661181440, coefficient := (-8859625232976025310661181440) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 19176358918684948656291840, coefficient := (-19176358918684948656291840) }, { argument := 1605619942643376662148808704, coefficient := (-1605619942643376662148808704) }, { argument := 1605620523715814983999684608, coefficient := (-1605620523715814983999684608) }, { argument := 19175777846246626805415936, coefficient := (-19175777846246626805415936) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 8164382240820816416100843520, coefficient := (-8164382240820816416100843520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 79688211092064681988739563520, coefficient := (-79688211092064681988739563520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 8164387878606973943582556160, coefficient := (-8164387878606973943582556160) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 3301401685807686099249659904, coefficient := (-3301401685807686099249659904) }, { argument := 115540827918489371682130624512, coefficient := (-115540827918489371682130624512) }, { argument := 115540884586887166117873188864, coefficient := (-115540884586887166117873188864) }, { argument := 3301373351608788881378377728, coefficient := (-3301373351608788881378377728) }, { argument := 3169126500570573503741758013440, coefficient := 3169126500570573503741758013440 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-103163119436209585538147964420096)
def positiveArguments : Array ℕ := #[
    699099, 12233361, 12233367, 699093, 87091, 7209945,
    153, 70672355, 157, 5, 153, 87,
    157, 2451, 3, 3604975, 153, 5,
    3, 5, 77, 87, 87091, 1266475,
    58617045, 35, 31, 1451, 395, 29308533,
    1451, 35, 35, 15, 35, 395,
    15, 633227, 31, 1614859, 3507, 9967093,
    5649, 175, 5649, 3773, 1622027, 3507,
    21, 2675, 2445, 2675, 2445
  ]
def positiveCoefficients : Array ℕ := #[
    6602803371615372198499319808, 231081655836978743364261249024, 231081769173774332235746377728, 6602746703217577762756755456, 822551238719200542611996672, 68096005222667168320522813440,
    5918900812833224439361437696, 667481521034929970532749148160, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696, 3365649481807127622381993984,
    6073643317743896973723828224, 94818469884014595430554796032, 3713820117856140824697372672, 68096052446331997016974950400, 5918900812833224439361437696, 193428131138340667952988160,
    3713820117856140824697372672, 193428131138340667952988160, 5957586439060892572952035328, 3365649481807127622381993984, 822551238719200542611996672, 11961518182784667844031283200,
    553622337265723445250506096640, 5415987671873538702683668480, 4797017652230848565234106368, 224531374625385847359828656128, 61123289439715651073144258560, 553622535605115725775605071872,
    224531374625385847359828656128, 5415987671873538702683668480, 5415987671873538702683668480, 4642275147320176030871715840, 5415987671873538702683668480, 61123289439715651073144258560,
    4642275147320176030871715840, 11961319843392387318932307968, 4797017652230848565234106368, 61007648129283139201151270912, 135670491180432144502225895424, 753092254637514571550606491648,
    218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168, 145960867756991868037324865536, 61278447512876816136285454336, 135670491180432144502225895424,
    6499185206248246443220402176, 206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480
  ]
def positiveScales : Array ℕ := #[
    19, 23, 23, 19, 16, 22,
    7, 26, 7, 2, 7, 6,
    7, 11, 1, 21, 7, 2,
    1, 2, 6, 6, 16, 20,
    25, 5, 4, 10, 8, 24,
    10, 5, 5, 3, 5, 8,
    3, 19, 4, 20, 11, 23,
    12, 7, 12, 11, 20, 11,
    4, 11, 11, 11, 11
  ]
def negativeArguments : Array ℕ := #[
    3, 3, 11, 11, 5
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 950737950171172051122527404032, 1743019575313815427057966907392, 1743019575313815427057966907392, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    1, 1, 3, 3, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    19415137245768077, 23544317489325909, 23544318196912984, 19415124863820182, 16410236017704902, 22781556823418956,
    7257387842692651, 26074642648638129, 7294620748891626, 2321928094887362, 7257387842692651, 6442943495848725,
    7294620748891626, 11259154768866839, 1584962500720924, 21781557823908238, 7257387842692651, 2321928094887362,
    1584962500720924, 2321928094887362, 6266786540694901, 6442943495848725, 16410236017704902, 20272387168102182,
    25804816904946451, 5129283016944966, 4954196309696329, 10502831804066725, 8625708843063759, 24804817421802775,
    10502831804066725, 5129283016944966, 5129283016944966, 3906890595303263, 5129283016944966, 8625708843063759,
    3906890595303263, 19272363245918923, 4954196309696329, 20622976772087159, 11776021715228447, 23248741359201158,
    12463779785335379, 7451211111832325, 12463779785335379, 11881496384617007, 20629366403947572, 11776021715228447,
    4392317422778759, 11385323176175871, 11255618749839595, 11385323176175871, 11255618749839595
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 1584962500724866, 3459431618637364, 3459431618637364, 2321928094887363
  ]

abbrev PositiveTerm := Fin 53
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
noncomputable def positiveFloor : ℝ := 1286739027 / 1000000000000
noncomputable def negativeCeiling : ℝ := 38902969 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6602803371615372198499319808, coefficient := 6602803371615372198499319808 }, { argument := 231081655836978743364261249024, coefficient := 231081655836978743364261249024 }, { argument := 231081769173774332235746377728, coefficient := 231081769173774332235746377728 }, { argument := 6602746703217577762756755456, coefficient := 6602746703217577762756755456 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 822551238719200542611996672, coefficient := 822551238719200542611996672 }, { argument := 68096005222667168320522813440, coefficient := 68096005222667168320522813440 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 667481521034929970532749148160, coefficient := 667481521034929970532749148160 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 68096052446331997016974950400, coefficient := 68096052446331997016974950400 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 822551238719200542611996672, coefficient := 822551238719200542611996672 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 11961518182784667844031283200, coefficient := 11961518182784667844031283200 }, { argument := 553622337265723445250506096640, coefficient := 553622337265723445250506096640 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }, { argument := 553622535605115725775605071872, coefficient := 553622535605115725775605071872 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 11961319843392387318932307968, coefficient := 11961319843392387318932307968 }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 61007648129283139201151270912, coefficient := 61007648129283139201151270912 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 753092254637514571550606491648, coefficient := 753092254637514571550606491648 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 61278447512876816136285454336, coefficient := 61278447512876816136285454336 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
