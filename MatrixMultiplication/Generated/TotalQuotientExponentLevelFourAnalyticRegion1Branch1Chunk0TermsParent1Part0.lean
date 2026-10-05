import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0

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
def constantNumerator : ℤ := (-60616980256123474459807512002560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    614103, 6137931, 12275859, 614103, 388642947, 501,
    13, 3778485259, 807, 779383535, 807, 841,
    501, 25, 388642947, 397669245, 388642947, 397669245,
    397669245, 2897227765, 795339025, 501, 501, 741079,
    13, 13, 35, 388642947, 501, 13,
    3778485259, 807, 779383535, 807, 841, 501,
    25, 3778485259, 2897227765, 3778485259, 2897227765, 6168651,
    807, 807, 395, 35, 779383535, 795339025,
    779383535, 795339025, 12337299, 35, 397669245, 2897227765,
    795339025, 807, 807, 35, 841, 841,
    1451, 9, 501, 501
  ]
def negativeCoefficients : Array ℕ := #[
    2900019424229697734666354688, 115942238514266257264585211904, 115942210180067360046713929728, 2900019424229697734666354688, 3584598489680632681045426176, 4845374685015433732222353408,
    251456570479842868338884608, 17425187639764287557138907136, 7804825091432045951903072256, 3594272151352012725435760640, 7804825091432045951903072256, 8133652914367225087423152128,
    4845374685015433732222353408, 241785163922925834941235200, 3584598489680632681045426176, 3667851394250150870211624960, 3584598489680632681045426176, 3667851394250150870211624960,
    3667851394250150870211624960, 13361104776050129871893954560, 3667853861502170728864153600, 4845374685015433732222353408, 4845374685015433732222353408, 3499646630758553805320617984,
    251456570479842868338884608, 251456570479842868338884608, 676998458984192337835458560, 3584598489680632681045426176, 4845374685015433732222353408, 251456570479842868338884608,
    17425187639764287557138907136, 7804825091432045951903072256, 3594272151352012725435760640, 7804825091432045951903072256, 8133652914367225087423152128, 4845374685015433732222353408,
    241785163922925834941235200, 17425187639764287557138907136, 13361104776050129871893954560, 17425187639764287557138907136, 13361104776050129871893954560, 116522522907681279268444176384,
    7804825091432045951903072256, 7804825091432045951903072256, 7640411179964456384143032320, 676998458984192337835458560, 3594272151352012725435760640, 3667853861502170728864153600,
    3594272151352012725435760640, 3667853861502170728864153600, 116522494573482382050572894208, 676998458984192337835458560, 3667851394250150870211624960, 13361104776050129871893954560,
    3667853861502170728864153600, 7804825091432045951903072256, 7804825091432045951903072256, 676998458984192337835458560, 8133652914367225087423152128, 8133652914367225087423152128,
    28066421828173230919978582016, 696341272098026404630757376, 4845374685015433732222353408, 4845374685015433732222353408
  ]
def negativeScales : Array ℕ := #[
    19, 22, 23, 19, 28, 8,
    3, 31, 9, 29, 9, 9,
    8, 4, 28, 28, 28, 28,
    28, 31, 29, 8, 8, 19,
    3, 3, 5, 28, 8, 3,
    31, 9, 29, 9, 9, 8,
    4, 31, 31, 31, 31, 22,
    9, 9, 8, 5, 29, 29,
    29, 29, 23, 5, 28, 31,
    29, 9, 9, 5, 9, 9,
    10, 3, 8, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19228121125352790, 22549320997059275, 23549320644490498, 19228121125352790, 28533870093889104, 8968666807433246,
    3700439718214233, 31815160849283391, 9656424863302849, 29537758213028170, 9656424863302849, 9715961990360049,
    8968666807433246, 4643856189792934, 28533870093889104, 28566993750206544, 28533870093889104, 28566993750206544,
    28566993750206544, 31432025960244383, 29566994720663270, 8968666807433246, 8968666807433246, 19499267818362495,
    3700439718214233, 3700439718214233, 5129283016944967, 28533870093889104, 8968666807433246, 3700439718214233,
    31815160849283391, 9656424863302849, 29537758213028170, 9656424863302849, 9715961990360049, 8968666807433246,
    4643856189792934, 31815160849283391, 31432025960244383, 31815160849283391, 31432025960244383, 22556523595426922,
    9656424863302849, 9656424863302849, 8625708843075807, 5129283016944967, 29537758213028170, 29566994720663270,
    29537758213028170, 29566994720663270, 23556523244613944, 5129283016944967, 28566993750206544, 31432025960244383,
    29566994720663270, 9656424863302849, 9656424863302849, 5129283016944967, 9715961990360049, 9715961990360049,
    10502831804067043, 3169925001442313, 8968666807433246, 8968666807433246
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
noncomputable def negativeCeiling : ℝ := 218247583 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2900019424229697734666354688, coefficient := (-2900019424229697734666354688) }, { argument := 115942238514266257264585211904, coefficient := (-115942238514266257264585211904) }, { argument := 115942210180067360046713929728, coefficient := (-115942210180067360046713929728) }, { argument := 2900019424229697734666354688, coefficient := (-2900019424229697734666354688) }, { argument := 3584598489680632681045426176, coefficient := (-3584598489680632681045426176) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 17425187639764287557138907136, coefficient := (-17425187639764287557138907136) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 3594272151352012725435760640, coefficient := (-3594272151352012725435760640) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 3584598489680632681045426176, coefficient := (-3584598489680632681045426176) }, { argument := 3667851394250150870211624960, coefficient := (-3667851394250150870211624960) }, { argument := 3584598489680632681045426176, coefficient := (-3584598489680632681045426176) }, { argument := 3667851394250150870211624960, coefficient := (-3667851394250150870211624960) }, { argument := 3667851394250150870211624960, coefficient := (-3667851394250150870211624960) }, { argument := 13361104776050129871893954560, coefficient := (-13361104776050129871893954560) }, { argument := 3667853861502170728864153600, coefficient := (-3667853861502170728864153600) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 3499646630758553805320617984, coefficient := (-3499646630758553805320617984) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 3584598489680632681045426176, coefficient := (-3584598489680632681045426176) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 251456570479842868338884608, coefficient := (-251456570479842868338884608) }, { argument := 17425187639764287557138907136, coefficient := (-17425187639764287557138907136) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 3594272151352012725435760640, coefficient := (-3594272151352012725435760640) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 17425187639764287557138907136, coefficient := (-17425187639764287557138907136) }, { argument := 13361104776050129871893954560, coefficient := (-13361104776050129871893954560) }, { argument := 17425187639764287557138907136, coefficient := (-17425187639764287557138907136) }, { argument := 13361104776050129871893954560, coefficient := (-13361104776050129871893954560) }, { argument := 116522522907681279268444176384, coefficient := (-116522522907681279268444176384) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 7640411179964456384143032320, coefficient := (-7640411179964456384143032320) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 3594272151352012725435760640, coefficient := (-3594272151352012725435760640) }, { argument := 3667853861502170728864153600, coefficient := (-3667853861502170728864153600) }, { argument := 3594272151352012725435760640, coefficient := (-3594272151352012725435760640) }, { argument := 3667853861502170728864153600, coefficient := (-3667853861502170728864153600) }, { argument := 116522494573482382050572894208, coefficient := (-116522494573482382050572894208) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 3667851394250150870211624960, coefficient := (-3667851394250150870211624960) }, { argument := 13361104776050129871893954560, coefficient := (-13361104776050129871893954560) }, { argument := 3667853861502170728864153600, coefficient := (-3667853861502170728864153600) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 7804825091432045951903072256, coefficient := (-7804825091432045951903072256) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 8133652914367225087423152128, coefficient := (-8133652914367225087423152128) }, { argument := 28066421828173230919978582016, coefficient := (-28066421828173230919978582016) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }, { argument := 4845374685015433732222353408, coefficient := (-4845374685015433732222353408) }] }

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
def constantNumerator : ℤ := 61124264872846886695581018750976
def positiveArguments : Array ℕ := #[
    11, 3, 489, 535, 489, 535,
    3, 501, 13, 539, 807, 25,
    807, 841, 501, 25, 31, 35,
    15, 395, 35, 15, 35, 35,
    1451, 9, 395, 1451, 31, 35,
    9, 35, 1, 1, 1, 743307,
    5415379, 1486615, 614103, 6137931, 12275859, 614103
  ]
def positiveCoefficients : Array ℕ := #[
    871509787656907713528983453696, 475368975085586025561263702016, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240,
    928455029464035206174343168, 19381498740061734928889413632, 1005826281919371473355538432, 20851552536713124005332123648, 31219300365728183807612289024, 967140655691703339764940800,
    31219300365728183807612289024, 32534611657468900349692608512, 19381498740061734928889413632, 967140655691703339764940800, 599627206528856070654263296, 676998458984192337835458560,
    580284393415022003858964480, 7640411179964456384143032320, 676998458984192337835458560, 580284393415022003858964480, 676998458984192337835458560, 676998458984192337835458560,
    28066421828173230919978582016, 696341272098026404630757376, 7640411179964456384143032320, 28066421828173230919978582016, 599627206528856070654263296, 676998458984192337835458560,
    696341272098026404630757376, 676998458984192337835458560, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 28081344506259098998853861376,
    102293617126544545710799323136, 28081363395725030477434716160, 5800038848459395469332709376, 231884477028532514529170423808, 231884420360134720093427859456, 5800038848459395469332709376
  ]
def positiveScales : Array ℕ := #[
    3, 1, 8, 9, 8, 9,
    1, 8, 3, 9, 9, 4,
    9, 9, 8, 4, 4, 5,
    3, 8, 5, 3, 5, 5,
    10, 3, 8, 10, 4, 5,
    3, 5, 0, 0, 0, 19,
    22, 20, 19, 22, 23, 19
  ]
def negativeArguments : Array ℕ := #[
    395, 1451, 741079, 25, 25, 35,
    9, 35, 3, 1, 1, 1,
    1, 1, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    7640411179964456384143032320, 28066421828173230919978582016, 3499646630758553805320617984, 241785163922925834941235200, 241785163922925834941235200, 676998458984192337835458560,
    696341272098026404630757376, 676998458984192337835458560, 475368975085586025561263702016, 158456325028528675187087900672, 158456325028528675187087900672, 79228162514264337593543950336,
    79228162514264337593543950336, 158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    8, 10, 19, 4, 4, 5,
    3, 5, 1, 0, 0, 0,
    0, 0, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 1584962500720924, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509,
    1584962500720924, 8968666792316714, 3700439718136550, 9074141462752505, 9656424863276222, 4643856189773592,
    9656424863276222, 9715961990248632, 8968666792316714, 4643856189773592, 4954196309696329, 5129283016944966,
    3906890595303263, 8625708843063759, 5129283016944966, 3906890595303263, 5129283016944966, 5129283016944966,
    10502831804066725, 3169925001442312, 8625708843063759, 10502831804066725, 4954196309696329, 5129283016944966,
    3169925001442312, 5129283016944966, 0, 0, 0, 19503598668915806,
    22368630878955848, 20503599639372533, 19228121125352788, 22549320997057889, 23549320644489112, 19228121125352788
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8625708843075807, 10502831804067043, 19499267818362495, 4643856189792934, 4643856189792934, 5129283016944967,
    3169925001442313, 5129283016944967, 1584962500724866, 0, 0, 0,
    0, 0, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 42
abbrev NegativeTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 261759189 / 1000000000000
noncomputable def negativeCeiling : ℝ := 23438609 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7640411179964456384143032320, coefficient := (-7640411179964456384143032320) }, { argument := 28066421828173230919978582016, coefficient := (-28066421828173230919978582016) }, { argument := 3499646630758553805320617984, coefficient := (-3499646630758553805320617984) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 241785163922925834941235200, coefficient := (-241785163922925834941235200) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 696341272098026404630757376, coefficient := (-696341272098026404630757376) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 871509787656907713528983453696, coefficient := 871509787656907713528983453696 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 928455029464035206174343168, coefficient := 928455029464035206174343168 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 1005826281919371473355538432, coefficient := 1005826281919371473355538432 }, { argument := 20851552536713124005332123648, coefficient := 20851552536713124005332123648 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 967140655691703339764940800, coefficient := 967140655691703339764940800 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 32534611657468900349692608512, coefficient := 32534611657468900349692608512 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 967140655691703339764940800, coefficient := 967140655691703339764940800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 580284393415022003858964480, coefficient := 580284393415022003858964480 }, { argument := 7640411179964456384143032320, coefficient := 7640411179964456384143032320 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 580284393415022003858964480, coefficient := 580284393415022003858964480 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 28066421828173230919978582016, coefficient := 28066421828173230919978582016 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 7640411179964456384143032320, coefficient := 7640411179964456384143032320 }, { argument := 28066421828173230919978582016, coefficient := 28066421828173230919978582016 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28081344506259098998853861376, coefficient := 28081344506259098998853861376 }, { argument := 102293617126544545710799323136, coefficient := 102293617126544545710799323136 }, { argument := 28081363395725030477434716160, coefficient := 28081363395725030477434716160 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5800038848459395469332709376, coefficient := 5800038848459395469332709376 }, { argument := 231884477028532514529170423808, coefficient := 231884477028532514529170423808 }, { argument := 231884420360134720093427859456, coefficient := 231884420360134720093427859456 }, { argument := 5800038848459395469332709376, coefficient := 5800038848459395469332709376 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0
