import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 208787932718779070014428113094574080
def positiveArguments : Array ℕ := #[
    27027, 9, 1503, 39, 1617, 2421,
    75, 2421, 2523, 1503, 75, 9889,
    11165, 4785, 126005, 11165, 4785, 11165,
    11165, 462869, 2871, 126005, 462869, 9889,
    11165, 2871, 11165, 13737, 398373, 352583,
    22895, 13737, 22895, 700587, 22895, 13737,
    11223129, 718903, 398373, 700587, 22895, 718903,
    22895, 700587, 22895, 13737, 56729, 42245,
    44659, 3621, 776101, 1403741, 42245, 776101,
    22933, 22933, 44659, 44659, 1403741, 44659,
    56729
  ]
def positiveCoefficients : Array ℕ := #[
    2141299548273022252140712345731072, 2785365088392105618523029504, 58144496220185204786668240896, 3017478845758114420066615296, 62554657610139372015996370944, 93657901097184551422836867072,
    2901421967075110019294822400, 93657901097184551422836867072, 97603834972406701049077825536, 58144496220185204786668240896, 2901421967075110019294822400, 382562157765410173077419982848,
    431925016831914711539022561280, 370221442998784038462019338240, 4874582332817323173083254620160, 431925016831914711539022561280, 370221442998784038462019338240, 431925016831914711539022561280,
    431925016831914711539022561280, 17906377126374521326946335326208, 444265731598540846154423205888, 4874582332817323173083254620160, 17906377126374521326946335326208, 382562157765410173077419982848,
    431925016831914711539022561280, 444265731598540846154423205888, 431925016831914711539022561280, 531424447489477151134039670784, 7705654488597418691443575226368, 13639894152229913545773684883456,
    442853706241230959278366392320, 8502791159831634418144634732544, 442853706241230959278366392320, 13551323410981667353918011604992, 14171318599719390696907724554240, 8502791159831634418144634732544,
    217086886799451416238255205515264, 13905606375974652121340704718848, 7705654488597418691443575226368, 13551323410981667353918011604992, 442853706241230959278366392320, 13905606375974652121340704718848,
    442853706241230959278366392320, 13551323410981667353918011604992, 14171318599719390696907724554240, 531424447489477151134039670784, 1097298445134692775230506532864, 817137139993920151767398481920,
    863830690850715589011249823744, 1120645220563090493852432203776, 15011976600459733073898206396416, 27152299823226546757299555270656, 817137139993920151767398481920, 15011976600459733073898206396416,
    887177466279113307633175494656, 887177466279113307633175494656, 863830690850715589011249823744, 863830690850715589011249823744, 27152299823226546757299555270656, 863830690850715589011249823744,
    1097298445134692775230506532864
  ]
def positiveScales : Array ℕ := #[
    14, 3, 10, 5, 10, 11,
    6, 11, 11, 10, 6, 13,
    13, 12, 16, 13, 12, 13,
    13, 18, 11, 16, 18, 13,
    13, 11, 13, 13, 18, 18,
    14, 13, 14, 19, 14, 13,
    23, 19, 18, 19, 14, 19,
    14, 19, 14, 13, 15, 15,
    15, 11, 19, 20, 15, 19,
    14, 14, 15, 15, 20, 15,
    15
  ]
def negativeArguments : Array ℕ := #[
    3, 319, 4579
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 50547567684100647384681040314368, 362785756152816401840837748588544
  ]
def negativeScales : Array ℕ := #[
    1, 8, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14722113760991968, 3169925001442312, 10553629293916271, 5285402218862248, 10659103963471994, 11241387363998936,
    6228818690495880, 11241387363998936, 11300924490976300, 10553629293916271, 6228818690495880, 13271608924151744,
    13446695630709832, 12224303209373387, 16943121456256572, 13446695630709832, 12224303209373387, 13446695630709832,
    13446695630709832, 18820244417771497, 11487337615207170, 16943121456256572, 18820244417771497, 13271608924151744,
    13446695630709832, 11487337615207170, 13446695630709832, 13745779350381986, 18603760345521884, 18427603390368446,
    14482744944560899, 13745779350381986, 14482744944560899, 19418204692366197, 14482744944560899, 13745779350381986,
    23419971618540385, 19455437598565170, 18603760345521884, 19418204692366197, 14482744944560899, 19455437598565170,
    14482744944560899, 19418204692366197, 14482744944560899, 13745779350381986, 15791798812398820, 15366492977699987,
    15446663326383968, 11822172461413723, 19565884888082835, 20420845342228238, 15366492977699987, 19565884888082835,
    14485137474198596, 14485137474198596, 15446663326383968, 15446663326383968, 20420845342228238, 15446663326383968,
    15791798812398820
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 8317412613764870, 12160816849673548
  ]

abbrev PositiveTerm := Fin 61
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 252289496759 / 500000000000
noncomputable def negativeCeiling : ℝ := 58174514177 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2141299548273022252140712345731072, coefficient := 2141299548273022252140712345731072 }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 3017478845758114420066615296, coefficient := 3017478845758114420066615296 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 97603834972406701049077825536, coefficient := 97603834972406701049077825536 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 382562157765410173077419982848, coefficient := 382562157765410173077419982848 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 370221442998784038462019338240, coefficient := 370221442998784038462019338240 }, { argument := 4874582332817323173083254620160, coefficient := 4874582332817323173083254620160 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 370221442998784038462019338240, coefficient := 370221442998784038462019338240 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 17906377126374521326946335326208, coefficient := 17906377126374521326946335326208 }, { argument := 444265731598540846154423205888, coefficient := 444265731598540846154423205888 }, { argument := 4874582332817323173083254620160, coefficient := 4874582332817323173083254620160 }, { argument := 17906377126374521326946335326208, coefficient := 17906377126374521326946335326208 }, { argument := 382562157765410173077419982848, coefficient := 382562157765410173077419982848 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 444265731598540846154423205888, coefficient := 444265731598540846154423205888 }, { argument := 431925016831914711539022561280, coefficient := 431925016831914711539022561280 }, { argument := 50547567684100647384681040314368, coefficient := (-50547567684100647384681040314368) }, { argument := 531424447489477151134039670784, coefficient := 531424447489477151134039670784 }, { argument := 7705654488597418691443575226368, coefficient := 7705654488597418691443575226368 }, { argument := 13639894152229913545773684883456, coefficient := 13639894152229913545773684883456 }, { argument := 442853706241230959278366392320, coefficient := 442853706241230959278366392320 }, { argument := 8502791159831634418144634732544, coefficient := 8502791159831634418144634732544 }, { argument := 442853706241230959278366392320, coefficient := 442853706241230959278366392320 }, { argument := 13551323410981667353918011604992, coefficient := 13551323410981667353918011604992 }, { argument := 14171318599719390696907724554240, coefficient := 14171318599719390696907724554240 }, { argument := 8502791159831634418144634732544, coefficient := 8502791159831634418144634732544 }, { argument := 217086886799451416238255205515264, coefficient := 217086886799451416238255205515264 }, { argument := 13905606375974652121340704718848, coefficient := 13905606375974652121340704718848 }, { argument := 7705654488597418691443575226368, coefficient := 7705654488597418691443575226368 }, { argument := 13551323410981667353918011604992, coefficient := 13551323410981667353918011604992 }, { argument := 442853706241230959278366392320, coefficient := 442853706241230959278366392320 }, { argument := 13905606375974652121340704718848, coefficient := 13905606375974652121340704718848 }, { argument := 442853706241230959278366392320, coefficient := 442853706241230959278366392320 }, { argument := 13551323410981667353918011604992, coefficient := 13551323410981667353918011604992 }, { argument := 14171318599719390696907724554240, coefficient := 14171318599719390696907724554240 }, { argument := 531424447489477151134039670784, coefficient := 531424447489477151134039670784 }, { argument := 362785756152816401840837748588544, coefficient := (-362785756152816401840837748588544) }, { argument := 1097298445134692775230506532864, coefficient := 1097298445134692775230506532864 }, { argument := 817137139993920151767398481920, coefficient := 817137139993920151767398481920 }, { argument := 863830690850715589011249823744, coefficient := 863830690850715589011249823744 }, { argument := 1120645220563090493852432203776, coefficient := 1120645220563090493852432203776 }, { argument := 15011976600459733073898206396416, coefficient := 15011976600459733073898206396416 }, { argument := 27152299823226546757299555270656, coefficient := 27152299823226546757299555270656 }, { argument := 817137139993920151767398481920, coefficient := 817137139993920151767398481920 }, { argument := 15011976600459733073898206396416, coefficient := 15011976600459733073898206396416 }, { argument := 887177466279113307633175494656, coefficient := 887177466279113307633175494656 }, { argument := 887177466279113307633175494656, coefficient := 887177466279113307633175494656 }, { argument := 863830690850715589011249823744, coefficient := 863830690850715589011249823744 }, { argument := 863830690850715589011249823744, coefficient := 863830690850715589011249823744 }, { argument := 27152299823226546757299555270656, coefficient := 27152299823226546757299555270656 }, { argument := 863830690850715589011249823744, coefficient := 863830690850715589011249823744 }, { argument := 1097298445134692775230506532864, coefficient := 1097298445134692775230506532864 }] }

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


end Parent3

namespace Parent3

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-97403555061824818157065061988827136)
def positiveArguments : Array ℕ := #[
    3621, 1643, 5035, 14893, 33231, 1643,
    16589, 33761, 1643, 5035, 1643, 257,
    1025, 509, 1025, 9, 27, 57,
    147, 123, 3441, 105, 123, 111,
    57, 57, 111, 3441, 111, 9,
    147, 1, 578813851, 578814053, 7965198343, 29048962315,
    3982777719, 2454655149, 96660927897, 96660939225, 2454673377, 8586169,
    3331576661, 138381685409, 13326320763, 8586169, 15796339, 3075405709,
    12301623047, 63185145, 355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    1120645220563090493852432203776, 31780241946029371744675954688, 779128512225236210514636308480, 576145031408661513564770533376, 642781022585819873674574954496, 31780241946029371744675954688,
    641755853490786668134424117248, 653032713536151929076083326976, 31780241946029371744675954688, 779128512225236210514636308480, 31780241946029371744675954688, 39768823762042841331134365696,
    39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 5570730176784211237046059008, 4178047632588158427784544256, 4410161389954167229328130048,
    5686787055467215637817851904, 76133312416050886906296139776, 133117239849406047685246451712, 4061990753905154027012751360, 76133312416050886906296139776, 4294104511271162828556337152,
    4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 133117239849406047685246451712, 4294104511271162828556337152, 5570730176784211237046059008,
    5686787055467215637817851904, 158456325028528675187087900672, 2733371129783104877143099703296, 2733372083701134416811432869888, 37614585684392035941129260105728, 137179845998499416870075225866240,
    37616272017851236277086844878848, 23183562405281989839204183441408, 912936652207744523302080425754624, 912936759197679559196762387251200, 23183734563874489334990093942784, 648752587229670060397359529984,
    125863407672137330394399609192448, 1306978066036946063034244900323328, 125863541022322073667441153540096, 648752587229670060397359529984, 298384407382586434421077835776, 58092771365630230372020813561856,
    58092772362049558257515953651712, 298383410963258548925937745920, 26855002599055646572599574528, 1213797261762630048879977955328, 26998335866543706044125675520
  ]
def positiveScales : Array ℕ := #[
    11, 10, 12, 13, 15, 10,
    14, 15, 10, 12, 10, 8,
    10, 8, 10, 3, 4, 5,
    7, 6, 11, 6, 6, 6,
    5, 5, 6, 11, 6, 3,
    7, 0, 29, 29, 32, 34,
    31, 31, 36, 36, 31, 23,
    31, 37, 33, 23, 23, 31,
    33, 25, 18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    1207, 53, 1, 3, 1, 69,
    2681, 23631, 9845, 737, 1
  ]
def negativeCoefficients : Array ℕ := #[
    95628392154717055475407548055552, 4199092613256009892457829367808, 158456325028528675187087900672, 475368975085586025561263702016, 158456325028528675187087900672, 5466743213484239293954532573184,
    212410703700742689088291330850816, 1872240708374580561673037090390016, 1560002519905864807216880382115840, 116782311546025633612883782795264, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    10, 5, 0, 1, 0, 6,
    11, 14, 13, 9, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11822172461413723, 10682116764947138, 12297776062894146, 13862346774648731, 15020242087365238, 10682116764947138,
    14017939301495817, 15043070016819499, 10682116764947138, 12297776062894146, 10682116764947138, 8005624549193878,
    10001408194392808, 8991521844801183, 10001408194392808, 3169925001442312, 4754887502147955, 5832890014087662,
    7199672344836364, 6942514504772358, 11748612176723449, 6714245517659862, 6942514504772358, 6794415866314396,
    5832890014087662, 5832890014087662, 6794415866314396, 11748612176723449, 6794415866314396, 3169925001442312,
    7199672344836364, 0, 29108524205035426, 29108524708520867, 32891063140792589, 34757767577556032,
    31891127818106751, 31192873210594056, 36492213792863074, 36492213961937061, 31192883923849471, 23033583138693000,
    31633557945001637, 37009862061027434, 33633559473512202, 23033583138693000, 23913086898314551, 31518129598016374,
    33518129622761780, 25913082080597609, 18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10237209960755022, 5727920454700926, 0, 1584962500724866, 0, 6108524456778170,
    11388555503982566, 14528393061105437, 13265175490788917, 9525520809095692, 0
  ]

abbrev PositiveTerm := Fin 53
abbrev NegativeTerm := Fin 11
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
noncomputable def positiveFloor : ℝ := 1636503450209 / 1000000000000
noncomputable def negativeCeiling : ℝ := 631500231733 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1120645220563090493852432203776, coefficient := 1120645220563090493852432203776 }, { argument := 95628392154717055475407548055552, coefficient := (-95628392154717055475407548055552) }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 779128512225236210514636308480, coefficient := 779128512225236210514636308480 }, { argument := 576145031408661513564770533376, coefficient := 576145031408661513564770533376 }, { argument := 642781022585819873674574954496, coefficient := 642781022585819873674574954496 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 641755853490786668134424117248, coefficient := 641755853490786668134424117248 }, { argument := 653032713536151929076083326976, coefficient := 653032713536151929076083326976 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 779128512225236210514636308480, coefficient := 779128512225236210514636308480 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 4199092613256009892457829367808, coefficient := (-4199092613256009892457829367808) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 2733371129783104877143099703296, coefficient := 2733371129783104877143099703296 }, { argument := 2733372083701134416811432869888, coefficient := 2733372083701134416811432869888 }, { argument := 5466743213484239293954532573184, coefficient := (-5466743213484239293954532573184) }, { argument := 37614585684392035941129260105728, coefficient := 37614585684392035941129260105728 }, { argument := 137179845998499416870075225866240, coefficient := 137179845998499416870075225866240 }, { argument := 37616272017851236277086844878848, coefficient := 37616272017851236277086844878848 }, { argument := 212410703700742689088291330850816, coefficient := (-212410703700742689088291330850816) }, { argument := 23183562405281989839204183441408, coefficient := 23183562405281989839204183441408 }, { argument := 912936652207744523302080425754624, coefficient := 912936652207744523302080425754624 }, { argument := 912936759197679559196762387251200, coefficient := 912936759197679559196762387251200 }, { argument := 23183734563874489334990093942784, coefficient := 23183734563874489334990093942784 }, { argument := 1872240708374580561673037090390016, coefficient := (-1872240708374580561673037090390016) }, { argument := 648752587229670060397359529984, coefficient := 648752587229670060397359529984 }, { argument := 125863407672137330394399609192448, coefficient := 125863407672137330394399609192448 }, { argument := 1306978066036946063034244900323328, coefficient := 1306978066036946063034244900323328 }, { argument := 125863541022322073667441153540096, coefficient := 125863541022322073667441153540096 }, { argument := 648752587229670060397359529984, coefficient := 648752587229670060397359529984 }, { argument := 1560002519905864807216880382115840, coefficient := (-1560002519905864807216880382115840) }, { argument := 298384407382586434421077835776, coefficient := 298384407382586434421077835776 }, { argument := 58092771365630230372020813561856, coefficient := 58092771365630230372020813561856 }, { argument := 58092772362049558257515953651712, coefficient := 58092772362049558257515953651712 }, { argument := 298383410963258548925937745920, coefficient := 298383410963258548925937745920 }, { argument := 116782311546025633612883782795264, coefficient := (-116782311546025633612883782795264) }, { argument := 26855002599055646572599574528, coefficient := 26855002599055646572599574528 }, { argument := 1213797261762630048879977955328, coefficient := 1213797261762630048879977955328 }, { argument := 26998335866543706044125675520, coefficient := 26998335866543706044125675520 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
