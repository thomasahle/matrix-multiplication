import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 24, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24

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
def constantNumerator : ℤ := 19963300562053964470105604620288
def positiveArguments : Array ℕ := #[
    5, 1, 19, 29, 299, 9,
    29, 9
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 1237940039285380274899124224, 1470053796651389076442710016, 1121883160602375874127331328, 11567002242072771943588691968, 1392682544196052809261514752,
    1121883160602375874127331328, 1392682544196052809261514752
  ]
def positiveScales : Array ℕ := #[
    2, 0, 4, 4, 8, 3,
    4, 3
  ]
def negativeArguments : Array ℕ := #[
    49661, 19, 1538819, 299, 9, 12310549,
    9, 9, 771, 9, 299, 771,
    397291, 9, 9, 19, 1452889599, 5197616613,
    363222279, 1452889599, 1627356673, 1452889599, 1627356673, 1627356673,
    5821761051, 406839033, 49661, 19, 1452889599, 5197616613,
    363222279, 5197616613, 5821761051, 5197616613, 5821761051, 1538819,
    299, 9, 363222279, 406839033, 363222279, 406839033,
    12310549, 9, 1627356673, 5821761051, 406839033, 9,
    771, 9, 299, 771, 397291, 9,
    9, 19
  ]
def negativeCoefficients : Array ℕ := #[
    3752279070492631215317712896, 735026898325694538221355008, 116269876300847753249511440384, 5783501121036385971794345984, 696341272098026404630757376, 116269847966648856031640158208,
    696341272098026404630757376, 696341272098026404630757376, 29826617821532130998350774272, 696341272098026404630757376, 5783501121036385971794345984, 29826617821532130998350774272,
    3752307404691528433188995072, 696341272098026404630757376, 696341272098026404630757376, 735026898325694538221355008, 3350135325013437111230005248, 11984887931659007752012824576,
    3350134211291263661015826432, 3350135325013437111230005248, 3752429007934305335766941696, 3350135325013437111230005248, 3752429007934305335766941696, 3752429007934305335766941696,
    13424067020760917585587863552, 3752427760473237351158513664, 3752279070492631215317712896, 735026898325694538221355008, 3350135325013437111230005248, 11984887931659007752012824576,
    3350134211291263661015826432, 11984887931659007752012824576, 13424067020760917585587863552, 11984887931659007752012824576, 13424067020760917585587863552, 116269876300847753249511440384,
    5783501121036385971794345984, 696341272098026404630757376, 3350134211291263661015826432, 3752427760473237351158513664, 3350134211291263661015826432, 3752427760473237351158513664,
    116269847966648856031640158208, 696341272098026404630757376, 3752429007934305335766941696, 13424067020760917585587863552, 3752427760473237351158513664, 696341272098026404630757376,
    29826617821532130998350774272, 696341272098026404630757376, 5783501121036385971794345984, 29826617821532130998350774272, 3752307404691528433188995072, 696341272098026404630757376,
    696341272098026404630757376, 735026898325694538221355008
  ]
def negativeScales : Array ℕ := #[
    15, 4, 20, 8, 3, 23,
    3, 3, 9, 3, 8, 9,
    18, 3, 3, 4, 30, 32,
    28, 30, 30, 30, 30, 30,
    32, 28, 15, 4, 30, 32,
    28, 32, 32, 32, 32, 20,
    8, 3, 28, 28, 28, 28,
    23, 3, 30, 32, 28, 3,
    9, 3, 8, 9, 18, 3,
    3, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 4247927513443585, 4857980995002857, 8224001674198104, 3169925001442312,
    4857980995002857, 3169925001442312
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15599825692228014, 4247927513443586, 20553392117327656, 8224001674198106, 3169925001442313, 23553391765752385,
    3169925001442313, 3169925001442313, 9590587049919383, 3169925001442313, 8224001674198106, 9590587049919383,
    18599836586261517, 3169925001442313, 3169925001442313, 4247927513443586, 30436277934777770, 32275203075537347,
    28436277455166779, 30436277934777770, 30599883339774420, 30436277934777770, 30599883339774420, 30599883339774420,
    32438808480528419, 28599882860163429, 15599825692228014, 4247927513443586, 30436277934777770, 32275203075537347,
    28436277455166779, 32275203075537347, 32438808480528419, 32275203075537347, 32438808480528419, 20553392117327656,
    8224001674198106, 3169925001442313, 28436277455166779, 28599882860163429, 28436277455166779, 28599882860163429,
    23553391765752385, 3169925001442313, 30599883339774420, 32438808480528419, 28599882860163429, 3169925001442313,
    9590587049919383, 3169925001442313, 8224001674198106, 9590587049919383, 18599836586261517, 3169925001442313,
    3169925001442313, 4247927513443586
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 56
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
noncomputable def positiveFloor : ℝ := 4720267 / 200000000000
noncomputable def negativeCeiling : ℝ := 12679 / 62500000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3752279070492631215317712896, coefficient := (-3752279070492631215317712896) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 116269876300847753249511440384, coefficient := (-116269876300847753249511440384) }, { argument := 5783501121036385971794345984, coefficient := (-5783501121036385971794345984) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 116269847966648856031640158208, coefficient := (-116269847966648856031640158208) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 29826617821532130998350774272, coefficient := (-29826617821532130998350774272) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 5783501121036385971794345984, coefficient := (-5783501121036385971794345984) }, { argument := 29826617821532130998350774272, coefficient := (-29826617821532130998350774272) }, { argument := 3752307404691528433188995072, coefficient := (-3752307404691528433188995072) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 3350135325013437111230005248, coefficient := (-3350135325013437111230005248) }, { argument := 11984887931659007752012824576, coefficient := (-11984887931659007752012824576) }, { argument := 3350134211291263661015826432, coefficient := (-3350134211291263661015826432) }, { argument := 3350135325013437111230005248, coefficient := (-3350135325013437111230005248) }, { argument := 3752429007934305335766941696, coefficient := (-3752429007934305335766941696) }, { argument := 3350135325013437111230005248, coefficient := (-3350135325013437111230005248) }, { argument := 3752429007934305335766941696, coefficient := (-3752429007934305335766941696) }, { argument := 3752429007934305335766941696, coefficient := (-3752429007934305335766941696) }, { argument := 13424067020760917585587863552, coefficient := (-13424067020760917585587863552) }, { argument := 3752427760473237351158513664, coefficient := (-3752427760473237351158513664) }, { argument := 3752279070492631215317712896, coefficient := (-3752279070492631215317712896) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 3350135325013437111230005248, coefficient := (-3350135325013437111230005248) }, { argument := 11984887931659007752012824576, coefficient := (-11984887931659007752012824576) }, { argument := 3350134211291263661015826432, coefficient := (-3350134211291263661015826432) }, { argument := 11984887931659007752012824576, coefficient := (-11984887931659007752012824576) }, { argument := 13424067020760917585587863552, coefficient := (-13424067020760917585587863552) }, { argument := 11984887931659007752012824576, coefficient := (-11984887931659007752012824576) }, { argument := 13424067020760917585587863552, coefficient := (-13424067020760917585587863552) }, { argument := 116269876300847753249511440384, coefficient := (-116269876300847753249511440384) }, { argument := 5783501121036385971794345984, coefficient := (-5783501121036385971794345984) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 3350134211291263661015826432, coefficient := (-3350134211291263661015826432) }, { argument := 3752427760473237351158513664, coefficient := (-3752427760473237351158513664) }, { argument := 3350134211291263661015826432, coefficient := (-3350134211291263661015826432) }, { argument := 3752427760473237351158513664, coefficient := (-3752427760473237351158513664) }, { argument := 116269847966648856031640158208, coefficient := (-116269847966648856031640158208) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 3752429007934305335766941696, coefficient := (-3752429007934305335766941696) }, { argument := 13424067020760917585587863552, coefficient := (-13424067020760917585587863552) }, { argument := 3752427760473237351158513664, coefficient := (-3752427760473237351158513664) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 29826617821532130998350774272, coefficient := (-29826617821532130998350774272) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 5783501121036385971794345984, coefficient := (-5783501121036385971794345984) }, { argument := 29826617821532130998350774272, coefficient := (-29826617821532130998350774272) }, { argument := 3752307404691528433188995072, coefficient := (-3752307404691528433188995072) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }] }

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
def constantNumerator : ℤ := (-19113802895720599924589671219200)
def positiveArguments : Array ℕ := #[
    9, 771, 9, 299, 771, 1,
    9, 9, 19, 483, 541, 483,
    541, 3, 1, 3008053, 10761111, 752013,
    41469, 1531395, 12251157, 331755
  ]
def positiveCoefficients : Array ℕ := #[
    1392682544196052809261514752, 59653235643064261996701548544, 1392682544196052809261514752, 11567002242072771943588691968, 59653235643064261996701548544, 1237940039285380274899124224,
    1392682544196052809261514752, 1392682544196052809261514752, 1470053796651389076442710016, 37370314935927417048517312512, 41857847578336920545026637824, 37370314935927417048517312512,
    41857847578336920545026637824, 475368975085586025561263702016, 158456325028528675187087900672, 28410257331790969787987787776, 101635819809679701350402752512, 28410247887058004048697360384,
    6266618101699882155736301568, 231417869441093130624895549440, 231417812772695336189152985088, 6266674770097676591478865920
  ]
def positiveScales : Array ℕ := #[
    3, 9, 3, 8, 9, 0,
    3, 3, 4, 8, 9, 8,
    9, 1, 0, 21, 23, 19,
    15, 20, 23, 18
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 3, 1, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016, 158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    0, 0, 1, 0, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 9590587049914763, 3169925001442312, 8224001674198104, 9590587049914763, 0,
    3169925001442312, 3169925001442312, 4247927513443585, 8915879378478017, 9079484783826815, 8915879378478017,
    9079484783826815, 1584962500720924, 0, 21520398555941934, 23359323696701572, 19520398076330943,
    15339745637489354, 20546415021358988, 23546414668079327, 18339758683576652
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 1584962500724866, 0, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 209423381 / 1000000000000
noncomputable def negativeCeiling : ℝ := 18138457 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28410257331790969787987787776, coefficient := 28410257331790969787987787776 }, { argument := 101635819809679701350402752512, coefficient := 101635819809679701350402752512 }, { argument := 28410247887058004048697360384, coefficient := 28410247887058004048697360384 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 6266618101699882155736301568, coefficient := 6266618101699882155736301568 }, { argument := 231417869441093130624895549440, coefficient := 231417869441093130624895549440 }, { argument := 231417812772695336189152985088, coefficient := 231417812772695336189152985088 }, { argument := 6266674770097676591478865920, coefficient := 6266674770097676591478865920 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24
